-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier30.P02.covariance_williamson
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:48:18.589338+00:00
-- url     : https://prove2.me/submissions/ef03d16c-ce9b-407f-b47b-2ebd96743895

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P10
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P02
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

namespace X5CW
open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma thermalCovariance)
open Matrix

abbrev cx {a b : Type*} (X : Matrix a b ℝ) : Matrix a b ℂ := X.map (fun x : ℝ => (x : ℂ))

variable {n : ℕ}

def Q (V : Matrix (Phase n) (Phase n) ℝ) : Prop :=
  (cx V + Complex.I • cx (sigma n)).PosSemidef

lemma cx_mul {a b c : Type*} [Fintype b] (A : Matrix a b ℝ) (B : Matrix b c ℝ) :
    cx (A * B) = cx A * cx B := by
  ext i j; simp [Matrix.mul_apply]

lemma cx_transpose {a b : Type*} (A : Matrix a b ℝ) : cx A.transpose = (cx A)ᴴ := by
  ext i j; simp [Matrix.conjTranspose_apply]

lemma cx_neg {a b : Type*} (A : Matrix a b ℝ) : cx (-A) = -cx A := by
  ext i j; simp

lemma qc_congr (T V : Matrix (Phase n) (Phase n) ℝ)
    (hT : T * sigma n * T.transpose = sigma n)
    (h : Q V) : Q (T * V * T.transpose) := by
  unfold Q at *
  have := h.mul_mul_conjTranspose_same (cx T)
  convert this using 1
  conv_lhs => rw [← hT]
  simp only [cx_mul, cx_transpose, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul]

lemma qc_diag (nu : Fin n → ℝ) (hnu : ∀ k, 1 ≤ nu k) : Q (thermalCovariance nu) := by
  unfold Q
  set P : Matrix (Phase n) (Phase n) ℂ :=
    1 + Complex.I • cx (sigma n) with hP
  have hsplit : cx (thermalCovariance nu) + Complex.I • cx (sigma n) =
      Matrix.diagonal (fun i => ((Sum.elim nu nu i - 1 : ℝ) : ℂ)) + P := by
    rw [hP, ← add_assoc]; congr 1
    ext (i | i) (j | j) <;>
      simp [thermalCovariance, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp
  rw [hsplit]
  refine Matrix.PosSemidef.add ?_ ?_
  · apply Matrix.PosSemidef.diagonal
    intro i
    rcases i with i | i <;> exact Complex.zero_le_real.2 (sub_nonneg.2 (hnu i))
  · have hPh : Pᴴ = P := by
      rw [hP, Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_smul,
        ← cx_transpose, X5MGP.sigma_t, cx_neg]
      simp
    have hPP : Pᴴ * P = (2 : ℂ) • P := by
      rw [hPh, hP]
      have h2 : cx (sigma n) * cx (sigma n) = -1 := by
        rw [← cx_mul, X5MGP.sigma_sq]; ext i j; simp [Matrix.one_apply]; split_ifs <;> simp
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
        Matrix.smul_mul, Matrix.mul_smul, h2, smul_smul, Complex.I_mul_I]
      ext i j
      simp [Matrix.one_apply]
      split_ifs <;> ring
    have := (Matrix.posSemidef_conjTranspose_mul_self P).smul (a := (1 / 2 : ℝ)) (by norm_num)
    convert this using 1
    rw [hPP]
    ext i j; simp

lemma qc_nu (nu : Fin n → ℝ) (h : Q (thermalCovariance nu)) (k : Fin n) :
    1 ≤ nu k := by
  unfold Q at h
  set z : Phase n → ℂ := Sum.elim (fun j => if j = k then 1 else 0)
    (fun j => if j = k then Complex.I else 0)
  have h1 := h.dotProduct_mulVec_nonneg z
  have key : star z ⬝ᵥ ((cx (thermalCovariance nu) + Complex.I • cx (sigma n))
      *ᵥ z) = ((2 * (nu k - 1) : ℝ) : ℂ) := by
    simp [z, dotProduct, Matrix.mulVec, Fintype.sum_sum_type, thermalCovariance, sigma,
      Matrix.diagonal_apply, Matrix.add_apply, Matrix.one_apply]
    apply Complex.ext <;> simp <;>
      rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (by simp)] <;> simp <;> ring
  rw [key] at h1
  have := Complex.zero_le_real.1 h1
  linarith

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

lemma cx_mulVec {a : Type*} [Fintype a] (A : Matrix a a ℝ) (x : a → ℝ) :
    cx A *ᵥ (fun i => (x i : ℂ)) = fun i => ((A *ᵥ x) i : ℂ) := by
  ext i; simp [Matrix.mulVec, dotProduct]

lemma qc_posDef (V : Matrix (Phase n) (Phase n) ℝ) (hVsym : V.transpose = V)
    (h : Q V) : V.PosDef := by
  unfold Q at h
  set K := cx V + Complex.I • cx (sigma n) with hK
  obtain ⟨Z, hZ⟩ := exists_factor K h
  have hskew : ∀ x : Phase n → ℝ, x ⬝ᵥ (sigma n *ᵥ x) = 0 := by
    intro x
    have : x ⬝ᵥ (sigma n *ᵥ x) = -(x ⬝ᵥ (sigma n *ᵥ x)) := by
      conv_lhs => rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, X5MGP.sigma_t, Matrix.neg_mulVec,
        neg_dotProduct, dotProduct_comm]
    linarith
  have key : ∀ x : Phase n → ℝ,
      star (fun i => (x i : ℂ)) ⬝ᵥ (K *ᵥ (fun i => (x i : ℂ))) = ((x ⬝ᵥ (V *ᵥ x) : ℝ) : ℂ) := by
    intro x
    rw [hK, Matrix.add_mulVec, Matrix.smul_mulVec, cx_mulVec, cx_mulVec, dotProduct_add,
      dotProduct_smul]
    have h0 := hskew x
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
    simp only [← Complex.ofReal_mul, ← Complex.ofReal_sum]
    simp only [dotProduct] at h0
    rw [h0]; simp
  have hV' : V.IsHermitian := by
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
  rw [hK, Matrix.add_mulVec, Matrix.smul_mulVec, cx_mulVec, cx_mulVec] at h6
  have h7 : sigma n *ᵥ x = 0 := by
    ext i
    have := congrFun h6 i
    have := congrArg Complex.im this
    simpa using this
  exact Matrix.eq_zero_of_mulVec_eq_zero (X5MGP.sigma_det n) h7

end X5CW

noncomputable section
open scoped Matrix ComplexOrder

namespace X5CW
open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma thermalCovariance complexify)
open QAlgorithms.Papers.Independent.Frontier30.P02 (canonicalJ uncertaintyMatrix covarianceSet
  IsSymplectic WilliamsonData PhaseMatrix)
open Matrix

variable {n : ℕ}

lemma J_eq (n : ℕ) : canonicalJ n = -sigma n := by
  simp [canonicalJ, sigma, fromBlocks_neg]

lemma memK_iff (S : PhaseMatrix n) : S ∈ covarianceSet n ↔ Sᵀ = S ∧ Q ((2:ℝ) • S) := by
  have : uncertaintyMatrix S = cx ((2:ℝ) • S) + Complex.I • cx (sigma n) := by
    ext i j
    simp [uncertaintyMatrix, complexify, J_eq, sub_eq_add_neg, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  simp [covarianceSet, Q, this]

lemma symp_iff (M : PhaseMatrix n) : IsSymplectic M ↔ Mᵀ * sigma n * M = sigma n := by
  simp [IsSymplectic, J_eq, Matrix.mul_neg, Matrix.neg_mul]

lemma symp_inv (M : PhaseMatrix n) (h : Mᵀ * sigma n * M = sigma n) :
    (-(sigma n * Mᵀ * sigma n)) * M = 1 ∧ M * (-(sigma n * Mᵀ * sigma n)) = 1 ∧
      M * sigma n * Mᵀ = sigma n := by
  have h1 : (-(sigma n * Mᵀ * sigma n)) * M = 1 := by
    rw [Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᵀ, h,
      X5MGP.sigma_sq, neg_neg]
  have h2 := mul_eq_one_comm.mp h1
  refine ⟨h1, h2, ?_⟩
  have e1 : M * sigma n * Mᵀ * sigma n = -1 := by
    have := h2
    rw [Matrix.mul_neg] at this
    simp only [Matrix.mul_assoc] at this ⊢
    exact neg_eq_iff_eq_neg.mp this
  calc M * sigma n * Mᵀ = M * sigma n * Mᵀ * sigma n * (-sigma n) := by
        rw [Matrix.mul_neg, Matrix.mul_assoc (M * sigma n * Mᵀ), X5MGP.sigma_sq, Matrix.mul_neg,
          Matrix.mul_one, neg_neg]
    _ = sigma n := by rw [e1]; simp

lemma det_W (d : Fin n → ℝ) : (thermalCovariance d).det = ∏ j, d j ^ 2 := by
  simp [thermalCovariance, det_diagonal, sq, Finset.prod_mul_distrib]

lemma det_char (d : Fin n → ℝ) (t : ℝ) (ht : t ≠ 0) :
    (t • (1 : PhaseMatrix n) - sigma n * thermalCovariance d).det = ∏ j, (t ^ 2 + d j ^ 2) := by
  have hA : (t • (1 : PhaseMatrix n) - sigma n * thermalCovariance d) =
      fromBlocks (diagonal (fun _ => t)) (-diagonal d) (diagonal d) (diagonal (fun _ => t)) := by
    ext (i | i) (j | j) <;>
      simp [sigma, thermalCovariance, fromBlocks_multiply, diagonal_apply, one_apply] <;>
      split_ifs <;> simp_all
  rw [hA]
  let _ : Invertible (diagonal (fun _ : Fin n => t)) :=
    ⟨diagonal (fun _ => t⁻¹), by simp [diagonal_mul_diagonal, ht], by simp [diagonal_mul_diagonal, ht]⟩
  rw [det_fromBlocks₁₁]
  have : ⅟(diagonal (fun _ : Fin n => t)) = diagonal (fun _ => t⁻¹) := rfl
  rw [this]
  simp only [diagonal_mul_diagonal, Matrix.mul_neg, diagonal_sub, sub_neg_eq_add, det_diagonal,
    ← Finset.prod_mul_distrib]
  rw [diagonal_add, det_diagonal, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  field_simp

lemma char_eq (S : PhaseMatrix n) (d : Fin n → ℝ) (M : PhaseMatrix n)
    (h : WilliamsonData S d M) (t : ℝ) (ht : t ≠ 0) :
    (t • (1 : PhaseMatrix n) - sigma n * S).det = ∏ j, (t ^ 2 + d j ^ 2) := by
  obtain ⟨-, -, hM, hS⟩ := h
  rw [symp_iff] at hM
  obtain ⟨h1, h2, -⟩ := symp_inv M hM
  set N := -(sigma n * Mᵀ * sigma n)
  have hN : N * sigma n = sigma n * Mᵀ := by
    simp only [N, Matrix.neg_mul, Matrix.mul_assoc, X5MGP.sigma_sq, Matrix.mul_neg, Matrix.mul_one,
      neg_neg]
  have : t • (1 : PhaseMatrix n) - sigma n * S =
      N * (t • (1 : PhaseMatrix n) - sigma n * thermalCovariance d) * M := by
    rw [hS, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, h1,
      ← Matrix.mul_assoc N, hN]
    simp only [Matrix.mul_assoc]
    rfl
  rw [this, det_mul, det_mul, mul_comm (N.det), mul_assoc, ← det_mul, h1, det_one, mul_one,
    det_char d t ht]

lemma mset_eq (d d' : Fin n → ℝ) (hd : ∀ j, 0 ≤ d j) (hd' : ∀ j, 0 ≤ d' j)
    (h : ∀ t : ℝ, t ≠ 0 → ∏ j, (t ^ 2 + d j ^ 2) = ∏ j, (t ^ 2 + d' j ^ 2)) :
    Multiset.map d Finset.univ.val = Multiset.map d' Finset.univ.val := by
  classical
  let s : (Fin n → ℝ) → Multiset ℝ := fun f => Multiset.map (fun j => -(f j) ^ 2) Finset.univ.val
  let p : (Fin n → ℝ) → Polynomial ℝ := fun f =>
    ((s f).map fun a => Polynomial.X - Polynomial.C a).prod
  have hev : ∀ f : Fin n → ℝ, ∀ y : ℝ, (p f).eval y = ∏ j, (y + f j ^ 2) := by
    intro f y
    simp only [p, s, Polynomial.eval_multiset_prod, Multiset.map_map, Function.comp_def,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_neg_eq_add]
    rfl
  have hp : p d = p d' := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply Set.Infinite.mono _ (Set.Ioi_infinite (0 : ℝ))
    intro y hy
    simp only [Set.mem_setOf_eq, hev]
    have hy' : (0 : ℝ) ≤ y := le_of_lt hy
    have := h (Real.sqrt y) (Real.sqrt_ne_zero'.mpr hy)
    rwa [Real.sq_sqrt hy'] at this
  have hs : s d = s d' := by
    have := congrArg Polynomial.roots hp
    simpa only [p, Polynomial.roots_multiset_prod_X_sub_C] using this
  have := congrArg (Multiset.map (fun x : ℝ => Real.sqrt (-x))) hs
  simp only [s, Multiset.map_map, Function.comp_def, neg_neg] at this
  have e1 : (fun j => Real.sqrt (d j ^ 2)) = d := funext fun j => Real.sqrt_sq (hd j)
  have e2 : (fun j => Real.sqrt (d' j ^ 2)) = d' := funext fun j => Real.sqrt_sq (hd' j)
  rwa [e1, e2] at this

lemma antitone_eq (d d' : Fin n → ℝ) (h1 : Antitone d) (h2 : Antitone d')
    (h : Multiset.map d Finset.univ.val = Multiset.map d' Finset.univ.val) : d = d' := by
  rw [Fin.univ_val_map, Fin.univ_val_map, Multiset.coe_eq_coe] at h
  exact List.ofFn_injective (h.eq_of_pairwise' h1.sortedGE_ofFn.pairwise h2.sortedGE_ofFn.pairwise)

lemma uniq (S : PhaseMatrix n) (d d' : Fin n → ℝ) (M M' : PhaseMatrix n)
    (h : WilliamsonData S d M) (h' : WilliamsonData S d' M') : d = d' := by
  apply antitone_eq d d' h.1 h'.1
  apply mset_eq d d' (fun j => by linarith [h.2.1 j]) (fun j => by linarith [h'.2.1 j])
  intro t ht
  rw [← char_eq S d M h t ht, ← char_eq S d' M' h' t ht]

lemma sigma_perm (π : Equiv.Perm (Fin n)) :
    (sigma n).submatrix (Equiv.sumCongr π π) (Equiv.sumCongr π π) = sigma n := by
  ext (i | i) (j | j) <;> simp [sigma, Matrix.one_apply]

lemma thermal_perm (D : Fin n → ℝ) (π : Equiv.Perm (Fin n)) :
    (thermalCovariance D).submatrix (Equiv.sumCongr π π) (Equiv.sumCongr π π) =
      thermalCovariance (D ∘ π) := by
  ext (i | i) (j | j) <;> simp [thermalCovariance, Matrix.diagonal_apply]

lemma thermal_two (d : Fin n → ℝ) :
    thermalCovariance (fun j => 2 * d j) = (2 : ℝ) • thermalCovariance d := by
  ext (i | i) (j | j) <;> simp [thermalCovariance, Matrix.diagonal_apply] <;> split_ifs <;> simp

lemma wd_W (d : Fin n → ℝ) :
    QAlgorithms.Papers.Independent.Frontier30.P02.williamsonDiagonal d = thermalCovariance d := rfl

lemma symp_left_inv (A B : PhaseMatrix n) (hA : A * sigma n * Aᵀ = sigma n) (hBA : B * A = 1) :
    B * sigma n * Bᵀ = sigma n := by
  calc B * sigma n * Bᵀ = B * (A * sigma n * Aᵀ) * Bᵀ := by rw [hA]
    _ = (B * A) * sigma n * (B * A)ᵀ := by
        rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = sigma n := by rw [hBA]; simp

lemma posDef_of_memK (S : PhaseMatrix n) (hS : S ∈ covarianceSet n) : S.PosDef := by
  rw [memK_iff] at hS
  have h2 := qc_posDef _ (by rw [Matrix.transpose_smul, hS.1]) hS.2
  have := h2.smul (show (0 : ℝ) < 1 / 2 by norm_num)
  rwa [smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul] at this

lemma exists_wd (S : PhaseMatrix n) (hS : S ∈ covarianceSet n) :
    ∃ d M, WilliamsonData S d M := by
  have hpd := posDef_of_memK S hS
  have hQ := ((memK_iff S).mp hS).2
  obtain ⟨D, T, hD, hT, hVT⟩ := X5MGP.williamson_phase S hpd
  set π : Equiv.Perm (Fin n) := Tuple.sort D * Fin.revPerm
  have hanti : Antitone (D ∘ π) := by
    have : D ∘ π = (D ∘ Tuple.sort D) ∘ Fin.rev := by
      funext x; simp [π, Equiv.Perm.coe_mul]
    rw [this]
    exact (Tuple.monotone_sort D).comp_antitone Fin.rev_anti
  set e : Phase n ≃ Phase n := Equiv.sumCongr π π
  set T' := T.submatrix id e
  have key : ∀ M : Matrix (Phase n) (Phase n) ℝ,
      T' * M.submatrix e e * T'ᵀ = T * M * Tᵀ := by
    intro M
    ext i j
    simp only [T', mul_apply, transpose_apply, submatrix_apply, id]
    rw [← Equiv.sum_comp e (fun x => (∑ j_1, T i j_1 * M j_1 x) * T j x)]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← Equiv.sum_comp e (fun y => T i y * M y (e x))]
  have hT'σ : T' * sigma n * T'ᵀ = sigma n := by
    rw [← sigma_perm π, key, sigma_perm, hT]
  have hVT' : S = T' * thermalCovariance (D ∘ π) * T'ᵀ := by
    rw [← thermal_perm, key, hVT]
  have hT't : T'ᵀᵀ * sigma n * T'ᵀ = sigma n := by rwa [Matrix.transpose_transpose]
  obtain ⟨-, -, hT'2⟩ := symp_inv T'ᵀ hT't
  rw [Matrix.transpose_transpose] at hT'2
  obtain ⟨hX, -, -⟩ := symp_inv T' hT'2
  set X := -(sigma n * T'ᵀ * sigma n)
  have hXσ := symp_left_inv T' X hT'σ hX
  refine ⟨D ∘ π, T'ᵀ, hanti, ?_, ?_, ?_⟩
  · intro j
    have hQ2 := qc_congr X _ hXσ hQ
    have e2 : X * ((2 : ℝ) • S) * Xᵀ = thermalCovariance (fun j => 2 * (D ∘ π) j) := by
      rw [thermal_two, hVT', Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      calc X * (T' * thermalCovariance (D ∘ π) * T'ᵀ) * Xᵀ
          = (X * T') * thermalCovariance (D ∘ π) * (X * T')ᵀ := by
            rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [hX]; simp
    rw [e2] at hQ2
    have := qc_nu _ hQ2 j
    linarith
  · rw [symp_iff, Matrix.transpose_transpose, hT'σ]
  · rw [Matrix.transpose_transpose, wd_W, hVT']

lemma memK_of_wd (S : PhaseMatrix n) (d : Fin n → ℝ) (M : PhaseMatrix n)
    (h : WilliamsonData S d M) : S ∈ covarianceSet n := by
  obtain ⟨-, hd, hM, hS⟩ := h
  rw [symp_iff] at hM
  rw [wd_W] at hS
  rw [memK_iff]
  constructor
  · rw [hS, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_assoc]
    congr 2
    simp [thermalCovariance, fromBlocks_transpose]
  · have : (2 : ℝ) • S = Mᵀ * thermalCovariance (fun j => 2 * d j) * Mᵀᵀ := by
      rw [thermal_two, hS, Matrix.transpose_transpose, Matrix.mul_smul, Matrix.smul_mul]
    rw [this]
    refine qc_congr _ _ (by rw [Matrix.transpose_transpose, hM]) (qc_diag _ fun k => ?_)
    linarith [hd k]

lemma det_wd (S : PhaseMatrix n) (d : Fin n → ℝ) (M : PhaseMatrix n)
    (h : WilliamsonData S d M) : S.det = ∏ j, d j ^ 2 := by
  obtain ⟨-, -, hM, hS⟩ := h
  rw [symp_iff] at hM
  have h1 := congrArg Matrix.det hM
  rw [det_mul, det_mul, det_transpose] at h1
  have h2 : M.det * M.det = 1 := by
    have := X5MGP.sigma_det n
    apply mul_right_cancel₀ this
    linear_combination h1
  rw [hS, wd_W, det_mul, det_mul, det_transpose, det_W]
  linear_combination (∏ j, d j ^ 2) * h2

end X5CW


open scoped ComplexOrder
open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify) in
open QAlgorithms.Papers.Independent.Frontier30.P02 in
theorem solution {n : ℕ} (hn : 0 < n) (S : PhaseMatrix n) :
    (S ∈ covarianceSet n ↔
      ∃! d : Fin n → ℝ, ∃ M : PhaseMatrix n, WilliamsonData S d M) ∧
    (S ∈ covarianceSet n → S.PosDef ∧ (1 / 4 : ℝ) ^ n ≤ S.det) ∧
    (∀ (d : Fin n → ℝ) (M : PhaseMatrix n), WilliamsonData S d M →
      S.det = ∏ j : Fin n, (d j) ^ 2) := by
  refine ⟨⟨fun hS => ?_, fun h => ?_⟩, fun hS => ⟨X5CW.posDef_of_memK S hS, ?_⟩,
    fun d M h => X5CW.det_wd S d M h⟩
  · obtain ⟨d, M, h⟩ := X5CW.exists_wd S hS
    exact ⟨d, ⟨M, h⟩, fun d' ⟨M', h'⟩ => X5CW.uniq S d' d M' M h' h⟩
  · obtain ⟨d, ⟨M, h⟩, -⟩ := h
    exact X5CW.memK_of_wd S d M h
  · obtain ⟨d, M, h⟩ := X5CW.exists_wd S hS
    rw [X5CW.det_wd S d M h]
    calc (1 / 4 : ℝ) ^ n = ∏ _j : Fin n, (1 / 4 : ℝ) := by simp
      _ ≤ ∏ j, d j ^ 2 := by
        apply Finset.prod_le_prod (fun _ _ => by norm_num)
        intro j _
        have := h.2.1 j
        nlinarith

