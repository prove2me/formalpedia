-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P42.pureGaussianCM_parametrization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:31:37.250997+00:00
-- url     : https://prove2.me/submissions/ad624ac2-e371-47fc-8e9b-d1379346c1e5

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P10
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P42
noncomputable section

open scoped InnerProductSpace RealInnerProductSpace Matrix

namespace X5MGP

abbrev QuadratureIndex (n : ℕ) := Fin n × Fin 2

def interleavedSymplecticForm (n : ℕ) : Matrix (QuadratureIndex n) (QuadratureIndex n) ℝ :=
  fun i j => if i.1 = j.1 then
    (if i.2 = j.2 then 0 else if i.2 = 0 then 1 else -1) else 0

def isSymplectic {n : ℕ} (S : Matrix (QuadratureIndex n) (QuadratureIndex n) ℝ) : Prop :=
  S * interleavedSymplecticForm n * S.transpose = interleavedSymplecticForm n

def williamsonDiagonal {n : ℕ} (nu : Fin n → ℝ) :
    Matrix (QuadratureIndex n) (QuadratureIndex n) ℝ :=
  Matrix.diagonal (fun i => nu i.1)

end X5MGP

lemma wl_eigen {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (A : E →ₗ[ℝ] E) (hskew : ∀ x y, ⟪A x, y⟫ = -⟪x, A y⟫) (W : Submodule ℝ E)
    (hW : ∀ x ∈ W, A x ∈ W) (hne : 0 < Module.finrank ℝ W) :
    ∃ e ∈ W, e ≠ 0 ∧ ∃ c : ℝ, A (A e) = c • e := by
  have h2 : ∀ x ∈ W, (A ∘ₗ A) x ∈ W := fun x hx => hW _ (hW x hx)
  set T : W →ₗ[ℝ] W := (A ∘ₗ A).restrict h2
  have hT : T.IsSymmetric := by
    intro x y
    simp only [T, Submodule.coe_inner, LinearMap.coe_restrict_apply, LinearMap.comp_apply]
    rw [hskew, hskew, neg_neg]
  have : Nontrivial W := Module.nontrivial_of_finrank_pos hne
  obtain ⟨v, hv, hv0⟩ := (hT.hasEigenvalue_iSup_of_finiteDimensional).exists_hasEigenvector
  refine ⟨v, v.2, fun h => hv0 (Subtype.ext h), ?_⟩
  refine ⟨(⨆ x : {x : W // x ≠ 0}, RCLike.re ⟪T x, x⟫ / ‖(x : W)‖ ^ 2), ?_⟩
  have := Module.End.mem_eigenspace_iff.1 hv
  have := congrArg Subtype.val this
  simpa [T] using this

open X5MGP in
lemma wl_core {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (A : E →ₗ[ℝ] E) (hskew : ∀ x y, ⟪A x, y⟫ = -⟪x, A y⟫) (hinj : ∀ x, A x = 0 → x = 0) :
    ∀ k : ℕ, ∀ W : Submodule ℝ E, (∀ x ∈ W, A x ∈ W) → Module.finrank ℝ W = 2 * k →
      ∃ v : Fin k × Fin 2 → E, ∃ nu : Fin k → ℝ, (∀ a, v a ∈ W) ∧ (∀ i, 0 < nu i) ∧
        (∀ a b, ⟪v a, v b⟫ = williamsonDiagonal nu a b) ∧
        (∀ a b, ⟪v a, A (v b)⟫ = interleavedSymplecticForm k a b) := by
  have hself : ∀ x, ⟪x, A x⟫ = 0 := by
    intro x
    have := hskew x x
    rw [real_inner_comm] at this
    linarith
  intro k
  induction k with
  | zero =>
    intro W _ _
    refine ⟨fun _ => 0, fun _ => 0, fun _ => W.zero_mem, fun i => i.elim0, fun a => a.1.elim0,
      fun a => a.1.elim0⟩
  | succ k ih =>
    intro W hW hdim
    obtain ⟨e0, he0W, he00, c, hc⟩ := wl_eigen A hskew W hW (by rw [hdim]; omega)
    have hAe0 : A e0 ≠ 0 := fun h => he00 (hinj _ h)
    have hpos1 : 0 < ⟪A e0, A e0⟫ := real_inner_self_pos.2 hAe0
    have hpos2 : 0 < ⟪e0, e0⟫ := real_inner_self_pos.2 he00
    have hrel : ⟪A e0, A e0⟫ = -c * ⟪e0, e0⟫ := by
      rw [hskew, hc, inner_smul_right]; ring
    have hcneg : 0 < -c := by
      by_contra h; push Not at h; nlinarith
    set s := Real.sqrt (-c) with hs
    have hspos : 0 < s := Real.sqrt_pos.2 hcneg
    have hss : s * s = -c := Real.mul_self_sqrt hcneg.le
    set r := (Real.sqrt (s * ⟪e0, e0⟫))⁻¹ with hr
    have hrr : r * r * ⟪e0, e0⟫ = s⁻¹ := by
      have h1 := Real.mul_self_sqrt (mul_pos hspos hpos2).le
      rw [hr]
      have h3 : 0 < Real.sqrt (s * ⟪e0, e0⟫) := Real.sqrt_pos.2 (mul_pos hspos hpos2)
      field_simp
      nlinarith
    set e := r • e0 with he
    have heW : e ∈ W := W.smul_mem _ he0W
    have hAAe : A (A e) = -(s * s) • e := by
      rw [he, map_smul, map_smul, hc, hss, neg_neg, smul_comm]
    have hee : ⟪e, e⟫ = s⁻¹ := by
      rw [he, inner_smul_left, inner_smul_right]; simpa [mul_assoc] using hrr
    set f := -(s⁻¹) • A e with hf
    have hfW : f ∈ W := W.smul_mem _ (hW _ heW)
    have hAe : A e = -s • f := by
      rw [hf, smul_smul]; field_simp; simp
    have hAf : A f = s • e := by
      rw [hf, map_smul, hAAe, smul_smul]; congr 1; field_simp
    have hxAe : ∀ x, ⟪x, A e⟫ = -s * ⟪x, f⟫ := fun x => by rw [hAe, inner_smul_right]
    have hxAf : ∀ x, ⟪x, A f⟫ = s * ⟪x, e⟫ := fun x => by rw [hAf, inner_smul_right]
    have heAx : ∀ x, ⟪e, A x⟫ = s * ⟪f, x⟫ := fun x => by
      have := hskew e x; rw [hAe, inner_smul_left] at this; simp at this; linarith
    have hfAx : ∀ x, ⟪f, A x⟫ = -s * ⟪e, x⟫ := fun x => by
      have := hskew f x; rw [hAf, inner_smul_left] at this; simp at this; linarith
    have hef : ⟪e, f⟫ = 0 := by
      have := hxAe e; rw [hself] at this
      have : s * ⟪e, f⟫ = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · exact h
    have hfe : ⟪f, e⟫ = 0 := by rw [real_inner_comm]; exact hef
    have hff : ⟪f, f⟫ = s⁻¹ := by
      have h1 := hxAf f
      have h2 := hfAx f
      rw [hAf, inner_smul_right] at h2
      have h3 := hxAe f
      -- ⟪f, A f⟫ = 0 and ⟪f, A e⟫ = -s⟪f,f⟫ ; also ⟪f, A e⟫ = ⟪f, -s f⟫
      have h4 : ⟪f, A e⟫ = -1 := by
        have := hfAx e
        rw [hee] at this; rw [this]; field_simp
      rw [h4] at h3
      field_simp; linarith
    -- complement
    set W' : Submodule ℝ E := W ⊓ LinearMap.ker (innerₛₗ ℝ e) ⊓ LinearMap.ker (innerₛₗ ℝ f)
      with hW'
    have memW' : ∀ x, x ∈ W' ↔ x ∈ W ∧ ⟪e, x⟫ = 0 ∧ ⟪f, x⟫ = 0 := by
      intro x; simp [hW', and_assoc]
    have hW'inv : ∀ x ∈ W', A x ∈ W' := by
      intro x hx
      rw [memW'] at hx ⊢
      refine ⟨hW _ hx.1, ?_, ?_⟩
      · rw [heAx, hx.2.2, mul_zero]
      · rw [hfAx, hx.2.1, mul_zero]
    have dec : ∀ w ∈ W, w - (s * ⟪e, w⟫) • e - (s * ⟪f, w⟫) • f ∈ W' := by
      intro w hw
      rw [memW']
      refine ⟨W.sub_mem (W.sub_mem hw (W.smul_mem _ heW)) (W.smul_mem _ hfW), ?_, ?_⟩
      · simp only [inner_sub_right, inner_smul_right, hee, hef]; field_simp; ring
      · simp only [inner_sub_right, inner_smul_right, hff, hfe]; field_simp; ring
    set P : Submodule ℝ E := Submodule.span ℝ (Set.range ![e, f]) with hP
    have hli : LinearIndependent ℝ ![e, f] := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hg
      have h1 := congrArg (fun x => ⟪e, x⟫) hg
      have h2 := congrArg (fun x => ⟪f, x⟫) hg
      simp only [inner_add_right, inner_smul_right, hee, hef, hfe, hff, inner_zero_right] at h1 h2
      have hsi : 0 < s⁻¹ := inv_pos.2 hspos
      intro i; fin_cases i
      · simp; nlinarith
      · simp; nlinarith
    have hPr : Module.finrank ℝ P = 2 := by
      rw [hP, finrank_span_eq_card hli]; simp
    have hinf : W' ⊓ P = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
      rw [memW'] at hx1
      obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hx2
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hx1 ⊢
      have h1 := hx1.2.1
      have h2 := hx1.2.2
      simp only [inner_add_right, inner_smul_right, hee, hef, hfe, hff] at h1 h2
      have hsi : 0 < s⁻¹ := inv_pos.2 hspos
      have c0 : g 0 = 0 := by nlinarith
      have c1 : g 1 = 0 := by nlinarith
      simp [c0, c1]
    have hsup : W' ⊔ P = W := by
      apply le_antisymm
      · apply sup_le
        · intro x hx; exact ((memW' x).1 hx).1
        · rw [hP, Submodule.span_le]
          rintro _ ⟨i, rfl⟩; fin_cases i
          · simpa using heW
          · simpa using hfW
      · intro w hw
        have : w = (w - (s * ⟪e, w⟫) • e - (s * ⟪f, w⟫) • f) +
            ((s * ⟪e, w⟫) • e + (s * ⟪f, w⟫) • f) := by abel
        rw [this]
        apply Submodule.add_mem_sup (dec w hw)
        apply P.add_mem
        · exact P.smul_mem _ (Submodule.subset_span ⟨0, by simp⟩)
        · exact P.smul_mem _ (Submodule.subset_span ⟨1, by simp⟩)
    have hdim' := Submodule.finrank_sup_add_finrank_inf_eq W' P
    rw [hsup, hinf, finrank_bot, hPr, hdim] at hdim'
    obtain ⟨v', nu', hv'W, hnu', hv'G, hv'O⟩ := ih W' hW'inv (by omega)
    have hev' : ∀ a, ⟪e, v' a⟫ = 0 := fun a => ((memW' _).1 (hv'W a)).2.1
    have hfv' : ∀ a, ⟪f, v' a⟫ = 0 := fun a => ((memW' _).1 (hv'W a)).2.2
    have hv'e : ∀ a, ⟪v' a, e⟫ = 0 := fun a => by rw [real_inner_comm]; exact hev' a
    have hv'f : ∀ a, ⟪v' a, f⟫ = 0 := fun a => by rw [real_inner_comm]; exact hfv' a
    have hAee : ⟪e, A e⟫ = 0 := hself e
    have hAff : ⟪f, A f⟫ = 0 := hself f
    have hAef : ⟪e, A f⟫ = 1 := by rw [hxAf, hee]; field_simp
    have hAfe : ⟪f, A e⟫ = -1 := by rw [hfAx, hee]; field_simp
    let v : Fin (k + 1) × Fin 2 → E := fun a => Fin.cases (![e, f] a.2) (fun j => v' (j, a.2)) a.1
    refine ⟨v, Fin.cases s⁻¹ nu', ?_, ?_, ?_, ?_⟩
    · rintro ⟨i, t⟩
      refine Fin.cases ?_ (fun j => ?_) i
      · fin_cases t <;> simp [v, heW, hfW]
      · simp only [v, Fin.cases_succ]; exact ((memW' _).1 (hv'W _)).1
    · intro i; refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hspos
      · simpa using hnu' j
    · have hee2 : ‖e‖ ^ 2 = s⁻¹ := by rw [← real_inner_self_eq_norm_sq, hee]
      have hff2 : ‖f‖ ^ 2 = s⁻¹ := by rw [← real_inner_self_eq_norm_sq, hff]
      rintro ⟨i, t⟩ ⟨j, u⟩
      refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
        fin_cases t <;> fin_cases u <;>
        simp [v, williamsonDiagonal, Matrix.diagonal_apply, hee2, hff2, hef, hfe, hff, hev', hfv', hv'e,
          hv'f, hv'G, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]
    · rintro ⟨i, t⟩ ⟨j, u⟩
      have hsne : s ≠ 0 := hspos.ne'
      refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
        fin_cases t <;> fin_cases u <;>
        simp [v, interleavedSymplecticForm, hAee, hAff, hAef, hAfe, heAx, hfAx, hxAe, hxAf,
          hev', hfv', hv'e, hv'f, hv'O, hsne, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

open X5MGP in
lemma wl_euclid (n : ℕ) (M : Matrix (QuadratureIndex n) (QuadratureIndex n) ℝ)
    (hMt : M.transpose = -M) (hM : M.det ≠ 0) :
    ∃ U : Matrix (QuadratureIndex n) (QuadratureIndex n) ℝ, ∃ nu : Fin n → ℝ, (∀ k, 0 < nu k) ∧
      U.transpose * U = williamsonDiagonal nu ∧
      U.transpose * M * U = interleavedSymplecticForm n := by
  let A : EuclideanSpace ℝ (QuadratureIndex n) →ₗ[ℝ] EuclideanSpace ℝ (QuadratureIndex n) :=
    Matrix.toLpLin 2 2 M
  have hin : ∀ x y : EuclideanSpace ℝ (QuadratureIndex n),
      ⟪x, A y⟫ = WithLp.ofLp x ⬝ᵥ (M *ᵥ WithLp.ofLp y) := by
    intro x y
    rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply]
    simp [dotProduct_comm]
  have hskew : ∀ x y, ⟪A x, y⟫ = -⟪x, A y⟫ := by
    intro x y
    rw [real_inner_comm, hin, hin, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hMt,
      Matrix.neg_mulVec, neg_dotProduct, dotProduct_comm]
  have hinj : ∀ x, A x = 0 → x = 0 := by
    intro x hx
    have h1 : M *ᵥ WithLp.ofLp x = 0 := by
      have := congrArg WithLp.ofLp hx
      simpa [A, Matrix.toLpLin_apply] using this
    have h2 := Matrix.eq_zero_of_mulVec_eq_zero hM h1
    have := congrArg (WithLp.toLp 2) h2
    simpa using this
  obtain ⟨v, nu, -, hnu, hG, hO⟩ := wl_core A hskew hinj n ⊤ (fun _ _ => Submodule.mem_top)
    (by rw [finrank_top, finrank_euclideanSpace]; simp [mul_comm])
  refine ⟨Matrix.of fun i a => WithLp.ofLp (v a) i, nu, hnu, ?_, ?_⟩
  · ext a b
    rw [← hG a b, EuclideanSpace.inner_eq_star_dotProduct]
    simp [Matrix.mul_apply, dotProduct, mul_comm]
  · ext a b
    rw [← hO a b, hin, Matrix.mul_assoc]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

namespace X5Williamson
open X5MGP

lemma wl_omega_t (n : ℕ) : (interleavedSymplecticForm n).transpose = -interleavedSymplecticForm n := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases a <;> fin_cases b <;> simp [interleavedSymplecticForm, eq_comm] <;> split_ifs <;> norm_num

lemma wl_omega_sq (n : ℕ) :
    interleavedSymplecticForm n * interleavedSymplecticForm n = -1 := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases a <;> fin_cases b <;>
    simp [interleavedSymplecticForm, Matrix.one_apply, Finset.sum_ite_eq, eq_comm] <;>
    split_ifs <;> norm_num

lemma wl_omega_det (n : ℕ) : (interleavedSymplecticForm n).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (wl_omega_sq n)
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_neg, Matrix.det_one] at this
  simp at this

lemma wl_factor {a : Type*} [Fintype a] [DecidableEq a] (V : Matrix a a ℝ) (hV : V.PosDef) :
    ∃ B : Matrix a a ℝ, V = B * B.transpose ∧ B.det ≠ 0 := by
  have hM := hV.isHermitian
  have hst : ∀ X : Matrix a a ℝ, star X = X.transpose := fun X => by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  set U : Matrix a a ℝ := (hM.eigenvectorUnitary : Matrix a a ℝ)
  set ev := hM.eigenvalues
  have hev : ∀ i, 0 < ev i := fun i => hV.eigenvalues_pos i
  have hVU : V = U * Matrix.diagonal ev * U.transpose := by
    conv_lhs => rw [hM.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, hst]
    congr 2
  set B : Matrix a a ℝ := U * Matrix.diagonal (fun i => Real.sqrt (ev i)) with hB
  have hBB : V = B * B.transpose := by
    rw [hVU, hB, Matrix.transpose_mul, Matrix.diagonal_transpose]
    have : Matrix.diagonal (fun i => Real.sqrt (ev i)) * Matrix.diagonal (fun i => Real.sqrt (ev i)) =
        Matrix.diagonal ev := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1; funext i; exact Real.mul_self_sqrt (hev i).le
    rw [← this]; simp only [Matrix.mul_assoc]
  refine ⟨B, hBB, fun h => ?_⟩
  have := hV.det_pos
  rw [hBB, Matrix.det_mul, h, zero_mul] at this
  exact lt_irrefl _ this

end X5Williamson

open X5MGP X5Williamson in
theorem wl_williamson (n : ℕ)
    (V : Matrix (QuadratureIndex n) (QuadratureIndex n) ℝ) (hV : V.PosDef) :
    ∃ nu : Fin n → ℝ, ∃ S : Matrix (QuadratureIndex n) (QuadratureIndex n) ℝ,
      (∀ k, 0 < nu k) ∧ isSymplectic S ∧
      V = S * williamsonDiagonal nu * S.transpose := by
  set Om := interleavedSymplecticForm n with hOm
  obtain ⟨B, hVB, hB⟩ := wl_factor V hV
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.2 hB
  set M := B⁻¹ * Om * B⁻¹.transpose with hMdef
  have hMt : M.transpose = -M := by
    rw [hMdef, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hOm,
      wl_omega_t]
    simp [Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg]
  have hBi : B⁻¹.det ≠ 0 := (Matrix.isUnit_nonsing_inv_det B hBu).ne_zero
  have hMdet : M.det ≠ 0 := by
    rw [hMdef, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hBi (wl_omega_det n)) hBi
  obtain ⟨U, nu, hnu, hUU, hUO⟩ := wl_euclid n M hMt hMdet
  have hU : U.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det hUO
    rw [Matrix.det_mul, Matrix.det_mul, h, mul_zero] at this
    exact wl_omega_det n this.symm
  have hUu : IsUnit U.det := isUnit_iff_ne_zero.2 hU
  have e1 : U⁻¹.transpose * U.transpose = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hUu, Matrix.transpose_one]
  have e2 : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv _ hUu
  have e3 : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ hBu
  have e4 : B⁻¹.transpose * B.transpose = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hBu, Matrix.transpose_one]
  refine ⟨nu, B * U⁻¹.transpose, hnu, ?_, ?_⟩
  · unfold isSymplectic
    rw [← hOm]
    calc B * U⁻¹.transpose * Om * (B * U⁻¹.transpose).transpose
        = B * (U⁻¹.transpose * U.transpose) * M * (U * U⁻¹) * B.transpose := by
          rw [Matrix.transpose_mul, Matrix.transpose_transpose]
          conv_lhs => rw [hOm, ← hUO]
          simp only [Matrix.mul_assoc]
      _ = (B * B⁻¹) * Om * (B⁻¹.transpose * B.transpose) := by
          rw [e1, e2, hMdef]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = Om := by rw [e3, e4, Matrix.one_mul, Matrix.mul_one]
  · rw [← hUU]
    calc V = B * B.transpose := hVB
      _ = B * (U⁻¹.transpose * U.transpose) * (U * U⁻¹) * B.transpose := by
          rw [e1, e2, Matrix.mul_one, Matrix.mul_one]
      _ = B * U⁻¹.transpose * (U.transpose * U) * (B * U⁻¹.transpose).transpose := by
          rw [Matrix.transpose_mul, Matrix.transpose_transpose]
          simp only [Matrix.mul_assoc]



end

noncomputable section
open scoped Matrix ComplexOrder

namespace X5MGP
open QAlgorithms.Papers.Independent.Dependency50.P10 Matrix

variable {n : ℕ}

def ep (n : ℕ) : QuadratureIndex n ≃ Phase n where
  toFun p := if p.2 = 0 then Sum.inl p.1 else Sum.inr p.1
  invFun := Sum.elim (fun i => (i, 0)) (fun i => (i, 1))
  left_inv := by rintro ⟨i, a⟩; fin_cases a <;> rfl
  right_inv := by rintro (i | i) <;> rfl

lemma ep_sigma (n : ℕ) : (sigma n).submatrix (ep n) (ep n) = interleavedSymplecticForm n := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [ep, sigma, interleavedSymplecticForm, Matrix.one_apply, eq_comm] <;> split_ifs <;> simp

lemma ep_thermal (D : Fin n → ℝ) :
    (thermalCovariance D).submatrix (ep n) (ep n) = williamsonDiagonal D := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [ep, thermalCovariance, williamsonDiagonal, diagonal_apply, eq_comm]

lemma sigma_t (n : ℕ) : (sigma n)ᵀ = -sigma n := by
  simp [sigma, fromBlocks_transpose, fromBlocks_neg]

lemma sigma_sq (n : ℕ) : sigma n * sigma n = -1 := by
  simp [sigma, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]

lemma sigma_det (n : ℕ) : (sigma n).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (sigma_sq n)
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_neg, Matrix.det_one] at this
  simp at this

theorem williamson_phase (G : Matrix (Phase n) (Phase n) ℝ) (hG : G.PosDef) :
    ∃ D : Fin n → ℝ, ∃ T : Matrix (Phase n) (Phase n) ℝ, (∀ k, 0 < D k) ∧
      T * sigma n * Tᵀ = sigma n ∧ G = T * thermalCovariance D * Tᵀ := by
  obtain ⟨nu, S, hnu, hS, hV⟩ := wl_williamson n (G.submatrix (ep n) (ep n))
    (hG.submatrix (ep n).injective)
  set e := ep n
  refine ⟨nu, S.submatrix e.symm e.symm, hnu, ?_, ?_⟩
  · have h1 : sigma n = (interleavedSymplecticForm n).submatrix e.symm e.symm := by
      rw [← ep_sigma]; simp [e]
    unfold isSymplectic at hS
    rw [h1, transpose_submatrix, submatrix_mul_equiv _ _ _ e.symm,
      submatrix_mul_equiv _ _ _ e.symm, hS]
  · have h1 : thermalCovariance nu = (williamsonDiagonal nu).submatrix e.symm e.symm := by
      rw [← ep_thermal]; simp [e]
    have h2 : G = (G.submatrix e e).submatrix e.symm e.symm := by simp
    rw [h1, h2, hV, transpose_submatrix, submatrix_mul_equiv _ _ _ e.symm,
      submatrix_mul_equiv _ _ _ e.symm]

end X5MGP

noncomputable section
open scoped Matrix ComplexOrder

namespace X5MGP
open QAlgorithms.Papers.Independent.Dependency50.P10 Matrix

variable {n : ℕ}

lemma cx_mul {a b c : Type*} [Fintype b] (A : Matrix a b ℝ) (B : Matrix b c ℝ) :
    complexify (A * B) = complexify A * complexify B := by
  ext i j; simp [complexify, Matrix.mul_apply]

lemma cx_transpose {a b : Type*} (A : Matrix a b ℝ) : complexify Aᵀ = (complexify A)ᴴ := by
  ext i j; simp [complexify, Matrix.conjTranspose_apply]

lemma cx_neg {a b : Type*} (A : Matrix a b ℝ) : complexify (-A) = -complexify A := by
  ext i j; simp [complexify]

lemma cx_sub {a b : Type*} (A B : Matrix a b ℝ) :
    complexify (A - B) = complexify A - complexify B := by
  ext i j; simp [complexify]

lemma cx_mulVec {a : Type*} [Fintype a] (A : Matrix a a ℝ) (x : a → ℝ) :
    complexify A *ᵥ (fun i => (x i : ℂ)) = fun i => ((A *ᵥ x) i : ℂ) := by
  ext i; simp [complexify, Matrix.mulVec, dotProduct]

lemma cx_det {a : Type*} [Fintype a] [DecidableEq a] (A : Matrix a a ℝ) :
    (complexify A).det = (A.det : ℂ) := by
  have : complexify A = (Complex.ofRealHom).mapMatrix A := rfl
  rw [this, ← RingHom.map_det]; rfl

lemma cx_submatrix {a b c d : Type*} (A : Matrix a b ℝ) (r : c → a) (s : d → b) :
    complexify (A.submatrix r s) = (complexify A).submatrix r s := rfl

lemma phys_congr {a : Type*} [Fintype a] (omega G T : Matrix a a ℝ)
    (hT : T * omega * Tᵀ = omega) (h : physicalCovariance G omega) :
    physicalCovariance (T * G * Tᵀ) omega := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, h.1,
      Matrix.mul_assoc]
  have := h.2.mul_mul_conjTranspose_same (complexify T)
  convert this using 1
  conv_lhs => rw [← hT]
  simp only [cx_mul, cx_transpose, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul]

lemma exists_factor {a : Type*} [Fintype a] [DecidableEq a] (K : Matrix a a ℂ)
    (hK : K.PosSemidef) : ∃ Z : Matrix a a ℂ, Z * Zᴴ = K := by
  have hH := hK.isHermitian
  set U : Matrix a a ℂ := (hH.eigenvectorUnitary : Matrix a a ℂ)
  set lam := hH.eigenvalues
  have hlam : ∀ i, 0 ≤ lam i := fun i => hK.eigenvalues_nonneg i
  refine ⟨U * diagonal (fun i => ((Real.sqrt (lam i) : ℝ) : ℂ)), ?_⟩
  conv_rhs => rw [hH.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose,
    ← Matrix.star_eq_conjTranspose]
  have hd : diagonal (fun i => ((Real.sqrt (lam i) : ℝ) : ℂ)) *
      diagonal (star (fun i => ((Real.sqrt (lam i) : ℝ) : ℂ))) =
      diagonal (RCLike.ofReal ∘ lam) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal, Function.comp_apply]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hlam i)]
    rfl
  calc U * diagonal (fun i => ((Real.sqrt (lam i) : ℝ) : ℂ)) *
        (diagonal (star (fun i => ((Real.sqrt (lam i) : ℝ) : ℂ))) * star U)
      = U * (diagonal (fun i => ((Real.sqrt (lam i) : ℝ) : ℂ)) *
        diagonal (star (fun i => ((Real.sqrt (lam i) : ℝ) : ℂ)))) * star U := by
        simp only [Matrix.mul_assoc]
    _ = U * diagonal (RCLike.ofReal ∘ lam) * star U := by rw [hd]

lemma phys_posDef {a : Type*} [Fintype a] [DecidableEq a] (omega G : Matrix a a ℝ)
    (homt : omegaᵀ = -omega) (homd : omega.det ≠ 0)
    (h : physicalCovariance G omega) : G.PosDef := by
  obtain ⟨hVsym, h⟩ := h
  set K := complexify G - Complex.I • complexify omega with hK
  obtain ⟨Z, hZ⟩ := exists_factor K h
  have hskew : ∀ x : a → ℝ, x ⬝ᵥ (omega *ᵥ x) = 0 := by
    intro x
    have : x ⬝ᵥ (omega *ᵥ x) = -(x ⬝ᵥ (omega *ᵥ x)) := by
      conv_lhs => rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, homt,
        Matrix.neg_mulVec, neg_dotProduct, dotProduct_comm]
    linarith
  have key : ∀ x : a → ℝ,
      star (fun i => (x i : ℂ)) ⬝ᵥ (K *ᵥ (fun i => (x i : ℂ))) = ((x ⬝ᵥ (G *ᵥ x) : ℝ) : ℂ) := by
    intro x
    rw [hK, Matrix.sub_mulVec, Matrix.smul_mulVec, cx_mulVec, cx_mulVec, dotProduct_sub,
      dotProduct_smul]
    have h0 := hskew x
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
    simp only [← Complex.ofReal_mul, ← Complex.ofReal_sum]
    simp only [dotProduct] at h0
    rw [h0]; simp
  have hV' : G.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hVsym]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hV' fun x hx => ?_
  simp only [star_trivial]
  have h1 := h.dotProduct_mulVec_nonneg (fun i => (x i : ℂ))
  rw [key] at h1
  have h2 := Complex.zero_le_real.1 h1
  refine lt_of_le_of_ne h2 fun h3 => hx ?_
  have h4 := key x
  rw [← h3, ← hZ] at h4
  simp only [Complex.ofReal_zero] at h4
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec] at h4
  have h5 : star (fun i => (x i : ℂ)) ᵥ* Z = star (Zᴴ *ᵥ (fun i => (x i : ℂ))) := by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
  rw [h5, dotProduct_star_self_eq_zero] at h4
  have h6 : K *ᵥ (fun i => (x i : ℂ)) = 0 := by
    rw [← hZ, ← Matrix.mulVec_mulVec, h4, Matrix.mulVec_zero]
  rw [hK, Matrix.sub_mulVec, Matrix.smul_mulVec, cx_mulVec, cx_mulVec] at h6
  have h7 : omega *ᵥ x = 0 := by
    ext i
    have := congrFun h6 i
    have := congrArg Complex.im this
    simpa using this
  exact Matrix.eq_zero_of_mulVec_eq_zero homd h7

lemma thermal_ge (D : Fin n → ℝ) (h : physicalCovariance (thermalCovariance D) (sigma n))
    (k : Fin n) : 1 ≤ D k := by
  set z : Phase n → ℂ := Sum.elim (fun j => if j = k then 1 else 0)
    (fun j => if j = k then -Complex.I else 0)
  have h1 := h.2.dotProduct_mulVec_nonneg z
  have key : star z ⬝ᵥ ((complexify (thermalCovariance D) - Complex.I • complexify (sigma n))
      *ᵥ z) = ((2 * (D k - 1) : ℝ) : ℂ) := by
    simp [z, dotProduct, Matrix.mulVec, thermalCovariance, sigma, complexify, Matrix.diagonal_apply,
      Matrix.sub_apply, Matrix.one_apply, Fintype.sum_sum_type]
    rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (by simp)]
    apply Complex.ext <;> simp <;> ring
  rw [key] at h1
  have := Complex.zero_le_real.1 h1
  linarith

lemma det_T {N : ℕ} (T : Matrix (Phase N) (Phase N) ℝ) (hT : T * sigma N * Tᵀ = sigma N) :
    T.det ^ 2 = 1 := by
  have := congrArg Matrix.det hT
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at this
  have h := sigma_det N
  have : (T.det ^ 2 - 1) * (sigma N).det = 0 := by linear_combination this
  rcases mul_eq_zero.1 this with h1 | h1
  · linear_combination h1
  · exact absurd h1 h

/-- Structure of physical covariances. -/
theorem decomp (G : Matrix (Phase n) (Phase n) ℝ) (hG : physicalCovariance G (sigma n)) :
    ∃ D : Fin n → ℝ, ∃ T : Matrix (Phase n) (Phase n) ℝ, (∀ k, 1 ≤ D k) ∧
      T * sigma n * Tᵀ = sigma n ∧ G = T * thermalCovariance D * Tᵀ ∧ IsUnit T.det := by
  obtain ⟨D, T, -, hT, hGT⟩ := williamson_phase G (phys_posDef _ _ (sigma_t n) (sigma_det n) hG)
  have hTd : IsUnit T.det := by
    have := det_T T hT
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    rw [h0] at this; norm_num at this
  refine ⟨D, T, fun k => ?_, hT, hGT, hTd⟩
  have hTi : T⁻¹ * sigma n * T⁻¹ᵀ = sigma n := by
    conv_lhs => rw [← hT]
    rw [Matrix.transpose_nonsing_inv]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ (by rwa [Matrix.det_transpose]), Matrix.mul_one,
      ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hTd, Matrix.one_mul]
  have hH : thermalCovariance D = T⁻¹ * G * T⁻¹ᵀ := by
    rw [hGT, Matrix.transpose_nonsing_inv]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ (by rwa [Matrix.det_transpose]), Matrix.mul_one,
      ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hTd, Matrix.one_mul]
  apply thermal_ge D _ k
  rw [hH]
  exact phys_congr _ _ _ hTi hG

end X5MGP

noncomputable section
open scoped Matrix ComplexOrder

namespace X5PG
open QAlgorithms.Papers.Independent.Dependency50.P10 Matrix
open QAlgorithms.Papers.Independent.Claimed50.P42 (pureGaussianCM)

variable {n : ℕ}

lemma symp_t (M : Matrix (Phase n) (Phase n) ℝ) (h : Mᵀ * sigma n * M = sigma n) :
    M * sigma n * Mᵀ = sigma n := by
  have h1 : (-(sigma n * Mᵀ * sigma n)) * M = 1 := by
    rw [Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᵀ, h,
      X5MGP.sigma_sq, neg_neg]
  have h2 := mul_eq_one_comm.mp h1
  have e1 : M * sigma n * Mᵀ * sigma n = -1 := by
    have := h2
    rw [Matrix.mul_neg] at this
    simp only [Matrix.mul_assoc] at this ⊢
    exact neg_eq_iff_eq_neg.mp this
  calc M * sigma n * Mᵀ = M * sigma n * Mᵀ * sigma n * (-sigma n) := by
        rw [Matrix.mul_neg, Matrix.mul_assoc (M * sigma n * Mᵀ), X5MGP.sigma_sq, Matrix.mul_neg,
          Matrix.mul_one, neg_neg]
    _ = sigma n := by rw [e1]; simp

lemma det_thermal (d : Fin n → ℝ) : (thermalCovariance d).det = ∏ j, d j ^ 2 := by
  simp [thermalCovariance, det_diagonal, sq, Finset.prod_mul_distrib]

lemma pure_sym (G : Matrix (Phase n) (Phase n) ℝ) (h : pureCovariance G (sigma n)) :
    G * sigma n * G = sigma n := by
  obtain ⟨D, T, hD, hT, hG, hTu⟩ := X5MGP.decomp G h.1
  have hdT := X5MGP.det_T T hT
  have hprod : ∏ j, D j ^ 2 = 1 := by
    have := h.2
    rw [hG, det_mul, det_mul, det_transpose, det_thermal] at this
    linear_combination this - (∏ j, D j ^ 2) * hdT
  have hD1 : ∀ k, D k = 1 := by
    intro k
    have hle : D k ^ 2 ≤ ∏ j, D j ^ 2 := by
      rw [← Finset.mul_prod_erase Finset.univ (fun j => D j ^ 2) (Finset.mem_univ k)]
      have hrest : ∏ j ∈ Finset.univ.erase k, (1 : ℝ) ≤ ∏ j ∈ Finset.univ.erase k, D j ^ 2 :=
        Finset.prod_le_prod (fun _ _ => zero_le_one) (fun j _ => by nlinarith [hD j])
      rw [Finset.prod_const_one] at hrest
      have := hD k
      nlinarith
    have := hD k
    nlinarith
  have hth : thermalCovariance D = 1 := by
    have : D = fun _ => 1 := funext hD1
    rw [this]; simp [thermalCovariance, ← fromBlocks_one]
  have hTt : Tᵀ * sigma n * T = sigma n := by
    have := symp_t Tᵀ (by rw [transpose_transpose]; exact hT)
    rwa [transpose_transpose] at this
  rw [hG, hth, Matrix.mul_one]
  calc T * Tᵀ * sigma n * (T * Tᵀ) = T * (Tᵀ * sigma n * T) * Tᵀ := by simp only [Matrix.mul_assoc]
    _ = sigma n := by rw [hTt, hT]

lemma cxm (A B : Matrix (Fin n) (Fin n) ℝ) : complexify (A * B) = complexify A * complexify B := by
  ext i j; simp [complexify, Matrix.mul_apply]

lemma cx_conjTranspose' {b c : Type*} (A : Matrix b c ℝ) :
    (complexify A)ᴴ = complexify Aᵀ := by
  ext i j; simp [complexify, Matrix.conjTranspose_apply]

lemma cx_psd (M : Matrix (Fin n) (Fin n) ℝ) (h : M.PosSemidef) : (complexify M).PosSemidef := by
  have hMt : Mᵀ = M := by
    have := h.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v => ?_
  · rw [Matrix.IsHermitian, cx_conjTranspose', hMt]
  · set re : Fin n → ℝ := fun i => (v i).re
    set im : Fin n → ℝ := fun i => (v i).im
    have hre := h.dotProduct_mulVec_nonneg re
    have him := h.dotProduct_mulVec_nonneg im
    have key : star v ⬝ᵥ (complexify M *ᵥ v) =
        ((re ⬝ᵥ (M *ᵥ re) + im ⬝ᵥ (M *ᵥ im) : ℝ) : ℂ) := by
      have hsym : ∑ i, ∑ j, M i j * (re i * im j - im i * re j) = 0 := by
        have h1 : ∑ i, ∑ j, M i j * (im i * re j) = ∑ i, ∑ j, M i j * (re i * im j) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          have : M j i = M i j := by
            have := congrFun (congrFun hMt i) j
            simpa [Matrix.transpose_apply] using this
          rw [this]; ring
        simp only [mul_sub, Finset.sum_sub_distrib, h1, sub_self]
      apply Complex.ext
      · simp only [dotProduct, Matrix.mulVec, complexify, Pi.star_apply, Complex.re_sum,
          Finset.mul_sum, Complex.ofReal_re, star_trivial]
        simp [Complex.mul_re, Finset.mul_sum, Finset.sum_add_distrib, re, im, mul_comm,
          mul_left_comm, mul_assoc]
      · simp only [dotProduct, Matrix.mulVec, complexify, Pi.star_apply, Complex.im_sum,
          Finset.mul_sum, Complex.ofReal_im]
        simp only [Complex.mul_im, Complex.mul_re, Complex.star_def, Complex.conj_re,
          Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.im_sum, Complex.re_sum,
          Finset.mul_sum]
        refine Eq.trans ?_ hsym
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [re, im]
        ring
    rw [key]
    exact_mod_cast add_nonneg (by simpa using hre) (by simpa using him)

lemma phys_G0 (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.PosDef) :
    physicalCovariance (fromBlocks X 0 0 X⁻¹) (sigma n) := by
  have hXt : Xᵀ = X := by
    have := hX.isHermitian; rwa [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hXu : IsUnit X.det := isUnit_iff_ne_zero.mpr hX.det_pos.ne'
  refine ⟨?_, ?_⟩
  · rw [fromBlocks_transpose, hXt, transpose_nonsing_inv, hXt]; simp
  set cX := complexify X
  set W := complexify X⁻¹
  have hXW : cX * W = 1 := by
    rw [← cxm, mul_nonsing_inv _ hXu]; ext i j; simp [complexify, one_apply]; split_ifs <;> simp
  have hWX : W * cX = 1 := by
    rw [← cxm, nonsing_inv_mul _ hXu]; ext i j; simp [complexify, one_apply]; split_ifs <;> simp
  have hcXh : cXᴴ = cX := by
    ext i j; simp [cX, complexify, conjTranspose_apply]
    rw [← transpose_apply X j i, hXt]
  have hWpsd : W.PosSemidef := cx_psd _ hX.inv.posSemidef
  set Z : Matrix (Fin n) (Fin n ⊕ Fin n) ℂ := fromCols cX (-Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ))
  have e1 : complexify (fromBlocks X 0 0 X⁻¹) - Complex.I • complexify (sigma n) =
      fromBlocks cX (-Complex.I • 1) (Complex.I • 1) W := by
    ext (i | i) (j | j) <;> simp [complexify, sigma, cX, W, one_apply] <;> split_ifs <;> simp
  have e2 : Zᴴ * W * Z = fromBlocks cX (-Complex.I • 1) (Complex.I • 1) W := by
    rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul, fromRows_mul_fromCols, hcXh,
      hXW]
    simp only [conjTranspose_smul, conjTranspose_one, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one, hWX, smul_smul, star_neg, Complex.star_def, Complex.conj_I]
    congr 1 <;> simp [neg_smul, smul_smul]
  rw [e1, ← e2]
  exact hWpsd.conjTranspose_mul_mul_same Z

lemma shear_symp (Y : Matrix (Fin n) (Fin n) ℝ) (hY : Yᵀ = Y) :
    (fromBlocks 1 Y 0 1)ᵀ * sigma n * (fromBlocks 1 Y 0 1)ᵀᵀ = sigma n := by
  rw [transpose_transpose, fromBlocks_transpose, hY]
  simp [sigma, fromBlocks_multiply]

lemma pgcm_eq (X Y : Matrix (Fin n) (Fin n) ℝ) (hY : Yᵀ = Y) :
    pureGaussianCM X Y = (fromBlocks 1 Y 0 1)ᵀ * fromBlocks X 0 0 X⁻¹ * (fromBlocks 1 Y 0 1)ᵀᵀ := by
  rw [transpose_transpose, fromBlocks_transpose, hY, pureGaussianCM]
  simp [fromBlocks_multiply, Matrix.mul_assoc]

lemma pure_of (X Y : Matrix (Fin n) (Fin n) ℝ) (hX : X.PosDef) (hY : Y.IsSymm) :
    pureCovariance (pureGaussianCM X Y) (sigma n) := by
  have hYt : Yᵀ = Y := hY
  refine ⟨?_, ?_⟩
  · rw [pgcm_eq X Y hYt]
    exact X5MGP.phys_congr _ _ _ (shear_symp Y hYt) (phys_G0 X hX)
  · rw [pgcm_eq X Y hYt, transpose_transpose, det_mul, det_mul, det_transpose,
      det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁]
    have hXu : IsUnit X.det := isUnit_iff_ne_zero.mpr hX.det_pos.ne'
    rw [det_nonsing_inv, Ring.inverse_eq_inv']
    simp only [det_one, mul_one, one_mul]
    exact mul_inv_cancel₀ hX.det_pos.ne'

theorem pg_main (gamma : Matrix (Phase n) (Phase n) ℝ) (hgamma : gamma.IsSymm) :
    pureCovariance gamma (sigma n) ↔
      ∃ X Y : Matrix (Fin n) (Fin n) ℝ, X.PosDef ∧ Y.IsSymm ∧ gamma = pureGaussianCM X Y := by
  constructor
  · intro h
    have hG : gamma.PosDef := X5MGP.phys_posDef _ _ (X5MGP.sigma_t n) (X5MGP.sigma_det n) h.1
    have hsym := pure_sym gamma h
    set A := gamma.toBlocks₁₁
    set B := gamma.toBlocks₁₂
    set C := gamma.toBlocks₂₂
    have hgt : gammaᵀ = gamma := hgamma
    have h21 : gamma.toBlocks₂₁ = Bᵀ := by
      ext i j; simp only [B, toBlocks₂₁, toBlocks₁₂, transpose_apply, of_apply]
      rw [← transpose_apply gamma (Sum.inl j) (Sum.inr i), hgt]
    have hAt : Aᵀ = A := by
      ext i j; simp only [A, toBlocks₁₁, transpose_apply, of_apply]
      rw [← transpose_apply gamma (Sum.inl i) (Sum.inl j), hgt]
    have hA : A.PosDef := hG.submatrix Sum.inl_injective
    have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
    have hg : gamma = fromBlocks A B Bᵀ C := by
      rw [← h21]; exact (fromBlocks_toBlocks gamma).symm
    rw [hg, sigma, fromBlocks_multiply, fromBlocks_multiply] at hsym
    simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero,
      Matrix.neg_mul, neg_add_eq_sub] at hsym
    obtain ⟨e11, e12, -, -⟩ := Matrix.fromBlocks_inj.mp hsym
    -- e11 : A * Bᵀ - B * A = 0, e12 : A * C - B * B = 1
    have hAinvt : A⁻¹ᵀ = A⁻¹ := by rw [transpose_nonsing_inv, hAt]
    have hcomm : Bᵀ * A⁻¹ = A⁻¹ * B := by
      have e : A * Bᵀ = B * A := by
        have := e11; rw [sub_eq_zero] at this; exact this
      calc Bᵀ * A⁻¹ = A⁻¹ * (A * Bᵀ) * A⁻¹ := by
            rw [← Matrix.mul_assoc, nonsing_inv_mul _ hAu, Matrix.one_mul]
        _ = A⁻¹ * (B * A) * A⁻¹ := by rw [e]
        _ = A⁻¹ * B := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hAu, Matrix.mul_one]
    have hC : C = A⁻¹ + A⁻¹ * B * B := by
      have e : A * C = 1 + B * B := by rw [← e12]; abel
      calc C = A⁻¹ * (A * C) := by rw [← Matrix.mul_assoc, nonsing_inv_mul _ hAu, Matrix.one_mul]
        _ = _ := by rw [e, Matrix.mul_add, Matrix.mul_one, Matrix.mul_assoc]
    refine ⟨A, A⁻¹ * B, hA, ?_, ?_⟩
    · show (A⁻¹ * B)ᵀ = A⁻¹ * B
      rw [transpose_mul, hAinvt, hcomm]
    · rw [hg, pureGaussianCM]
      have hYX : A⁻¹ * B * A = Bᵀ := by
        rw [← hcomm, Matrix.mul_assoc, nonsing_inv_mul _ hAu, Matrix.mul_one]
      congr 1
      · rw [← Matrix.mul_assoc, mul_nonsing_inv _ hAu, Matrix.one_mul]
      · rw [hYX]
      · rw [hYX, hC, add_comm]
        congr 1
        rw [show A⁻¹ * B * B = Bᵀ * A⁻¹ * B by rw [hcomm], Matrix.mul_assoc]
  · rintro ⟨X, Y, hX, hY, rfl⟩
    exact pure_of X Y hX hY

end X5PG


open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma pureCovariance) in
open QAlgorithms.Papers.Independent.Claimed50.P42 in
theorem solution (n : ℕ)
    (gamma : Matrix (Phase n) (Phase n) ℝ) (hgamma : gamma.IsSymm) :
    pureCovariance gamma (sigma n) ↔
      ∃ X Y : Matrix (Fin n) (Fin n) ℝ,
        X.PosDef ∧ Y.IsSymm ∧ gamma = pureGaussianCM X Y :=
  X5PG.pg_main gamma hgamma

