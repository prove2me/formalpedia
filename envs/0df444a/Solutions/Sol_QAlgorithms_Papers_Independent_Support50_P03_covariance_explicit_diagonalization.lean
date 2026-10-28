-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P03.covariance_explicit_diagonalization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T08:00:12.67035+00:00
-- url     : https://prove2.me/submissions/b3dc416e-d640-4bc7-845a-7dbee72dd3d6

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P03

noncomputable section

open scoped InnerProductSpace RealInnerProductSpace Matrix

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

open QAlgorithms.Papers.Independent.Frontier30.P08 in
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

open QAlgorithms.Papers.Independent.Frontier30.P08 in
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
open QAlgorithms.Papers.Independent.Frontier30.P08

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

open QAlgorithms.Papers.Independent.Frontier30.P08 X5Williamson in
theorem x5wl_main (n : ℕ) (hn : 0 < n)
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

namespace QAlgorithms.Papers.Independent.Support50.P03

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)
open QAlgorithms.Papers.Independent.Frontier30.P02 (PhaseMatrix)
open QAlgorithms.Papers.Independent.Frontier30.P08
  (QuadratureIndex interleavedSymplecticForm williamsonDiagonal isSymplectic)
open Matrix

def x5g_e (n : ℕ) : Phase n ≃ QuadratureIndex n where
  toFun := Sum.elim (fun j => (j, 0)) (fun j => (j, 1))
  invFun := fun p => if p.2 = 0 then Sum.inl p.1 else Sum.inr p.1
  left_inv := by intro x; rcases x with j | j <;> simp
  right_inv := by
    rintro ⟨j, k⟩; fin_cases k <;> simp

theorem x5g_omega (n : ℕ) :
    (interleavedSymplecticForm n).submatrix (x5g_e n) (x5g_e n) = sigma n := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [x5g_e, interleavedSymplecticForm, sigma, Matrix.one_apply, eq_comm] <;>
    split_ifs <;> simp

theorem x5g_diag (n : ℕ) (ν : Fin n → ℝ) :
    (williamsonDiagonal ν).submatrix (x5g_e n) (x5g_e n) = thermalCovariance ν := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [x5g_e, williamsonDiagonal, thermalCovariance, Matrix.diagonal_apply]

theorem x5g_J (n : ℕ) : Matrix.J (Fin n) ℝ = -sigma n := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.J, sigma]

theorem x5g_will (n : ℕ) (hn : 0 < n) (V : PhaseMatrix n) (hV : V.PosDef) :
    ∃ (ν : Fin n → ℝ) (S : PhaseMatrix n), (∀ k, 0 < ν k) ∧
      S ∈ Matrix.symplecticGroup (Fin n) ℝ ∧ V = S * thermalCovariance ν * S.transpose := by
  set e := x5g_e n
  obtain ⟨ν, S', hν, hS', hV'⟩ := x5wl_main n hn (V.submatrix e.symm e.symm)
    (hV.submatrix e.symm.injective)
  have key : ∀ (A B C : Matrix (QuadratureIndex n) (QuadratureIndex n) ℝ),
      (A * B * C).submatrix e e = A.submatrix e e * B.submatrix e e * C.submatrix e e := by
    intro A B C
    rw [submatrix_mul_equiv _ _ _ e _, submatrix_mul_equiv _ _ _ e _]
  refine ⟨ν, S'.submatrix e e, hν, ?_, ?_⟩
  · rw [SymplecticGroup.mem_iff, x5g_J]
    have hS'' : S' * interleavedSymplecticForm n * S'ᵀ = interleavedSymplecticForm n := hS'
    have := congrArg (fun M => M.submatrix e e) hS''

    rw [key, x5g_omega, ← transpose_submatrix] at this
    rw [Matrix.mul_neg, Matrix.neg_mul, this]
  · have h1 : V = (V.submatrix e.symm e.symm).submatrix e e := by
      simp [submatrix_submatrix]
    rw [h1, hV', key, x5g_diag, transpose_submatrix]

end QAlgorithms.Papers.Independent.Support50.P03


noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P03

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)
open QAlgorithms.Papers.Independent.Frontier30.P02 (PhaseMatrix)
open Matrix
open scoped ComplexOrder

theorem x5g_cmul {l m p : Type*} [Fintype m] (A : Matrix l m ℝ) (B : Matrix m p ℝ) :
    complexify (A * B) = complexify A * complexify B := by
  ext i j; simp [complexify, Matrix.mul_apply]

theorem x5g_cadd {l m : Type*} (A B : Matrix l m ℝ) :
    complexify (A + B) = complexify A + complexify B := by
  ext i j; simp [complexify]

theorem x5g_cT {l m : Type*} (A : Matrix l m ℝ) : (complexify A)ᴴ = complexify Aᵀ := by
  ext i j; simp [complexify, conjTranspose_apply]

theorem x5g_inv (n : ℕ) (S : PhaseMatrix n) (hS : S ∈ Matrix.symplecticGroup (Fin n) ℝ) :
    ∃ R : PhaseMatrix n, R ∈ Matrix.symplecticGroup (Fin n) ℝ ∧ R * S = 1 ∧ S * R = 1 := by
  set g : Matrix.symplecticGroup (Fin n) ℝ := ⟨S, hS⟩
  refine ⟨((g⁻¹ : Matrix.symplecticGroup (Fin n) ℝ) : PhaseMatrix n), (g⁻¹).2, ?_, ?_⟩
  · exact congrArg Subtype.val (inv_mul_cancel g)
  · exact congrArg Subtype.val (mul_inv_cancel g)

theorem x5g_symp_sigma (n : ℕ) (R : PhaseMatrix n) (hR : R ∈ Matrix.symplecticGroup (Fin n) ℝ) :
    R * sigma n * R.transpose = sigma n := by
  rw [SymplecticGroup.mem_iff, x5g_J, Matrix.mul_neg, Matrix.neg_mul] at hR
  exact neg_inj.mp hR

theorem x5g_half (n : ℕ) (V : PhaseMatrix n) (hV : HalfVacuumCovariance V) (ν : Fin n → ℝ)
    (S : PhaseMatrix n) (hS : S ∈ Matrix.symplecticGroup (Fin n) ℝ)
    (hVS : V = S * thermalCovariance ν * S.transpose) : ∀ j, (1 / 2 : ℝ) ≤ ν j := by
  obtain ⟨-, -, hpsd⟩ := hV
  obtain ⟨R, hR, hRS, -⟩ := x5g_inv n S hS
  have hRV : R * V * R.transpose = thermalCovariance ν := by
    rw [hVS]
    have : R * (S * thermalCovariance ν * S.transpose) * R.transpose =
        (R * S) * thermalCovariance ν * (R * S).transpose := by
      rw [transpose_mul]; simp only [Matrix.mul_assoc]
    rw [this, hRS, Matrix.one_mul, transpose_one, Matrix.mul_one]
  have hRσ := x5g_symp_sigma n R hR
  have h2 := hpsd.mul_mul_conjTranspose_same (complexify R)
  have hN : complexify R * (complexify V + (Complex.I / 2) • complexify (sigma n)) *
      (complexify R)ᴴ = complexify (thermalCovariance ν) +
        (Complex.I / 2) • complexify (sigma n) := by
    rw [x5g_cT, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      ← x5g_cmul, ← x5g_cmul, ← x5g_cmul, ← x5g_cmul, hRV, hRσ]
  rw [hN] at h2
  intro j
  have h3 := h2.submatrix (![Sum.inl j, Sum.inr j] : Fin 2 → Phase n)
  have h4 := h3.dotProduct_mulVec_nonneg ![1, Complex.I]
  simp [dotProduct, mulVec, Fin.sum_univ_two, complexify, thermalCovariance, sigma,
    Matrix.diagonal_apply] at h4
  have h5 := (Complex.le_def.mp h4).1
  simp at h5
  linarith

end QAlgorithms.Papers.Independent.Support50.P03


noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P03

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)
open QAlgorithms.Papers.Independent.Frontier30.P02 (PhaseMatrix)
open Matrix
open scoped ComplexOrder

theorem x5g_s2 : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 1 / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; push_cast; ring

theorem x5g_UUh (n : ℕ) : modeEigenbasis n * (modeEigenbasis n)ᴴ = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [modeEigenbasis, Matrix.mul_apply, Fintype.sum_sum_type, conjTranspose_apply,
      Matrix.smul_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.one_apply, smul_eq_mul, Matrix.one_apply_ne, Sum.inl.injEq,
      Sum.inr.injEq, reduceCtorEq, if_false] <;>
    rcases eq_or_ne i j with rfl | hij <;>
    simp [*, Ne.symm, mul_ite, ite_mul, Finset.sum_ite_eq, star_mul'] <;>
    first
    | linear_combination 2 * x5g_s2
    | linear_combination (-2 * Complex.I ^ 2) * x5g_s2 - Complex.I_sq

theorem x5g_key (n : ℕ) (d : Fin n → ℝ) :
    Complex.I • (complexify (thermalCovariance d) * complexify (sigma n)) =
      modeEigenbasis n * complexify (signedDiagonal d) * (modeEigenbasis n)ᴴ := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [modeEigenbasis, Matrix.mul_apply, Fintype.sum_sum_type, conjTranspose_apply,
      Matrix.smul_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.one_apply, smul_eq_mul, complexify, thermalCovariance, sigma,
      signedDiagonal, Matrix.diagonal_apply, Matrix.zero_apply, Matrix.neg_apply,
      Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false] <;>
    simp only [apply_ite (fun x : ℝ => (x : ℂ)), apply_ite (starRingEnd ℂ), Complex.ofReal_zero,
      Complex.ofReal_one, map_zero] <;>
    rcases eq_or_ne i j with rfl | hij <;>
    simp [*, Ne.symm, mul_ite, ite_mul, Finset.sum_ite_eq, star_mul'] <;>
    first
    | linear_combination (-2 * Complex.I * (d i : ℂ)) * x5g_s2
    | linear_combination (2 * Complex.I * (d i : ℂ)) * x5g_s2

end QAlgorithms.Papers.Independent.Support50.P03


noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P03

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)
open QAlgorithms.Papers.Independent.Frontier30.P02 (PhaseMatrix)
open Matrix Polynomial
open scoped ComplexOrder

theorem x5g_aeval_conj {ι : Type*} [Fintype ι] [DecidableEq ι] (E F M : Matrix ι ι ℂ)
    (hEF : E * F = 1) (hFE : F * E = 1) (p : ℂ[X]) :
    aeval (E * M * F) p = E * aeval M p * F := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, Matrix.mul_add, Matrix.add_mul]
  | monomial k c =>
    simp only [aeval_monomial, Matrix.algebraMap_eq_diagonal]
    have hpow : ∀ k : ℕ, (E * M * F) ^ k = E * M ^ k * F := by
      intro k
      induction k with
      | zero => simp [hEF]
      | succ k ih =>
        rw [pow_succ, ih, pow_succ]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc F E, hFE, Matrix.one_mul]
    rw [hpow]
    have : diagonal ((algebraMap ℂ (ι → ℂ)) c) = c • (1 : Matrix ι ι ℂ) := by
      ext i j; simp [Matrix.diagonal_apply, Matrix.one_apply]
    rw [this, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.smul_mul]

theorem x5g_aeval_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (δ : ι → ℂ) (p : ℂ[X]) :
    aeval (diagonal δ) p = diagonal (fun k => p.eval (δ k)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, eval_add, diagonal_add]
  | monomial k c =>
    simp only [aeval_monomial, Matrix.algebraMap_eq_diagonal, diagonal_pow, diagonal_mul_diagonal,
      eval_monomial]
    rfl

theorem x5g_arcoth_neg (x : ℝ) : realArcoth (-x) = -realArcoth x := by
  unfold realArcoth
  have : (-x + 1) / (-x - 1) = ((x + 1) / (x - 1))⁻¹ := by
    rw [inv_div]
    by_cases h1 : x + 1 = 0
    · rw [show -x - 1 = -(x + 1) by ring, h1]; simp
    · rw [show -x + 1 = -(x - 1) by ring, show -x - 1 = -(x + 1) by ring, neg_div_neg_eq]
  rw [this, Real.log_inv]; ring

theorem x5g_sd {n : ℕ} (x : Fin n → ℝ) :
    complexify (signedDiagonal x) =
      diagonal (fun k : Phase n => ((Sum.elim (fun j => -x j) x k : ℝ) : ℂ)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [complexify, signedDiagonal, Matrix.diagonal_apply, apply_ite (fun r : ℝ => (r : ℂ))]

theorem x5g_eval_nodes {n : ℕ} (ν : Fin n → ℝ) (k : Phase n) :
    (arcothPolynomial ν).eval ((Sum.elim (fun j => -(2 * ν j)) (fun j => 2 * ν j) k : ℝ) : ℂ) =
      ((Sum.elim (fun j => -realArcoth (2 * ν j)) (fun j => realArcoth (2 * ν j)) k : ℝ) : ℂ) := by
  classical
  unfold arcothPolynomial
  have hmem : (((Sum.elim (fun j => -(2 * ν j)) (fun j => 2 * ν j) k : ℝ) : ℂ)) ∈ arcothNodes ν := by
    unfold arcothNodes
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨k, ?_⟩
    rcases k with j | j <;> simp
  have h := Lagrange.eval_interpolate_at_node (s := arcothNodes ν) (v := fun z : ℂ => z)
    (fun z => (realArcoth z.re : ℂ)) (fun a _ b _ h => h) hmem

  rw [h]
  rcases k with j | j
  · simp [← x5g_arcoth_neg]
  · simp

end QAlgorithms.Papers.Independent.Support50.P03


noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P03

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)
open QAlgorithms.Papers.Independent.Frontier30.P02 (PhaseMatrix)
open Matrix Polynomial
open scoped ComplexOrder

theorem x5g_csmul {l m : Type*} (r : ℝ) (A : Matrix l m ℝ) :
    complexify (r • A) = (r : ℂ) • complexify A := by
  ext i j; simp [complexify]

theorem x5g_goal (n : ℕ) (hn : 0 < n)
    (V : PhaseMatrix n) (hV : HalfVacuumCovariance V) :
    (∃ (nu : Fin n → ℝ) (S : PhaseMatrix n), GroupedWilliamsonData V nu S) ∧
    (∀ (nu : Fin n → ℝ) (S : PhaseMatrix n), GroupedWilliamsonData V nu S →
      (let E := complexify S * modeEigenbasis n
       IsUnit E.det ∧
       Complex.I • (complexify V * complexify (sigma n)) =
         E * complexify (signedDiagonal nu) * E⁻¹ ∧
       complexify S = E * (modeEigenbasis n).conjTranspose ∧
       (FaithfulSpectrum nu →
         (let B := (2 * Complex.I) • (complexify V * complexify (sigma n))
          spectralArcoth nu B =
            E * complexify (signedDiagonal (fun j => realArcoth (2 * nu j))) * E⁻¹ ∧
          (2 * Complex.I) • (complexify (sigma n) * spectralArcoth nu B) =
            complexify (gibbsMatrix S nu))))) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨ν, S, -, hS, hVS⟩ := x5g_will n hn V hV.2.1
    exact ⟨ν, S, x5g_half n V hV ν S hS hVS, hS, hVS⟩
  · intro ν S hW
    obtain ⟨-, hS, hVS⟩ := hW
    obtain ⟨R, -, hRS, hSR⟩ := x5g_inv n S hS
    have hUUh := x5g_UUh n
    have hUhU : (modeEigenbasis n)ᴴ * modeEigenbasis n = 1 := mul_eq_one_comm.mp hUUh
    have hc1 : complexify (1 : PhaseMatrix n) = 1 := by
      ext i j; simp [complexify, Matrix.one_apply, apply_ite (fun r : ℝ => (r : ℂ))]
    have hSRc : complexify S * complexify R = 1 := by rw [← x5g_cmul, hSR, hc1]
    have hRSc : complexify R * complexify S = 1 := by rw [← x5g_cmul, hRS, hc1]
    have hSt : S.transpose * sigma n = sigma n * R := by
      have h := x5g_symp_sigma n S.transpose (SymplecticGroup.transpose_mem hS)
      rw [transpose_transpose] at h
      calc S.transpose * sigma n = S.transpose * sigma n * (S * R) := by rw [hSR, Matrix.mul_one]
        _ = (S.transpose * sigma n * S) * R := by simp only [Matrix.mul_assoc]
        _ = sigma n * R := by rw [h]
    intro E
    have hE : E = complexify S * modeEigenbasis n := rfl
    have hEinv : E * ((modeEigenbasis n)ᴴ * complexify R) = 1 := by
      rw [hE, show complexify S * modeEigenbasis n * ((modeEigenbasis n)ᴴ * complexify R) =
        complexify S * (modeEigenbasis n * (modeEigenbasis n)ᴴ) * complexify R by
          simp only [Matrix.mul_assoc], hUUh, Matrix.mul_one, hSRc]
    have hEi : E⁻¹ = (modeEigenbasis n)ᴴ * complexify R := inv_eq_right_inv hEinv
    have hEiE : E⁻¹ * E = 1 := by
      rw [hEi, hE, show (modeEigenbasis n)ᴴ * complexify R * (complexify S * modeEigenbasis n) =
        (modeEigenbasis n)ᴴ * (complexify R * complexify S) * modeEigenbasis n by
          simp only [Matrix.mul_assoc], hRSc, Matrix.mul_one, hUhU]
    have hEE : E * E⁻¹ = 1 := by rw [hEi]; exact hEinv
    have hconj : ∀ d : Fin n → ℝ, complexify S *
        (Complex.I • (complexify (thermalCovariance d) * complexify (sigma n))) * complexify R =
        E * complexify (signedDiagonal d) * E⁻¹ := by
      intro d; rw [x5g_key, hEi, hE]; simp only [Matrix.mul_assoc]
    have hVσ : Complex.I • (complexify V * complexify (sigma n)) = complexify S *
        (Complex.I • (complexify (thermalCovariance ν) * complexify (sigma n))) * complexify R := by
      have : complexify V * complexify (sigma n) = complexify S *
          (complexify (thermalCovariance ν) * complexify (sigma n)) * complexify R := by
        rw [hVS, ← x5g_cmul, ← x5g_cmul, ← x5g_cmul, ← x5g_cmul,
          Matrix.mul_assoc (S * thermalCovariance ν), hSt]
        simp only [Matrix.mul_assoc]
      rw [this, Matrix.mul_smul, Matrix.smul_mul]
    refine ⟨isUnit_det_of_right_inverse hEinv, by rw [hVσ, hconj], ?_, ?_⟩
    · rw [hE, Matrix.mul_assoc, hUUh, Matrix.mul_one]
    · intro _ B
      have h2 : complexify (signedDiagonal (fun j => 2 * ν j)) =
          (2 : ℂ) • complexify (signedDiagonal ν) := by
        ext i j
        rcases i with i | i <;> rcases j with j | j <;>
          simp [complexify, signedDiagonal, Matrix.diagonal_apply,
            apply_ite (fun r : ℝ => (r : ℂ))] <;> split_ifs <;> simp
      have hB : B = E * complexify (signedDiagonal (fun j => 2 * ν j)) * E⁻¹ := by
        show (2 * Complex.I) • (complexify V * complexify (sigma n)) = _
        rw [h2, Matrix.mul_smul, Matrix.smul_mul, ← hconj, ← hVσ, smul_smul]
      have hspec : spectralArcoth ν B =
          E * complexify (signedDiagonal (fun j => realArcoth (2 * ν j))) * E⁻¹ := by
        rw [spectralArcoth, hB, x5g_aeval_conj _ _ _ hEE hEiE, x5g_sd, x5g_aeval_diag, x5g_sd]
        simp only [x5g_eval_nodes]
      refine ⟨hspec, ?_⟩
      rw [hspec, ← hconj, gibbsMatrix, x5g_csmul]
      have e1 : sigma n * S * thermalCovariance (fun j => realArcoth (2 * ν j)) * S.transpose *
          sigma n = sigma n * S * thermalCovariance (fun j => realArcoth (2 * ν j)) *
          (sigma n * R) := by
        rw [← hSt]; simp only [Matrix.mul_assoc]
      rw [e1]
      simp only [x5g_cmul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
      congr 1
      rw [mul_assoc, Complex.I_mul_I]; push_cast; ring

end QAlgorithms.Papers.Independent.Support50.P03

open QAlgorithms.Papers.Independent.Support50.P03
open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)
open QAlgorithms.Papers.Independent.Frontier30.P02 (PhaseMatrix)

theorem solution (n : ℕ) (hn : 0 < n)
    (V : PhaseMatrix n) (hV : HalfVacuumCovariance V) :
    (∃ (nu : Fin n → ℝ) (S : PhaseMatrix n), GroupedWilliamsonData V nu S) ∧
    (∀ (nu : Fin n → ℝ) (S : PhaseMatrix n), GroupedWilliamsonData V nu S →
      (let E := complexify S * modeEigenbasis n
       IsUnit E.det ∧
       Complex.I • (complexify V * complexify (sigma n)) =
         E * complexify (signedDiagonal nu) * E⁻¹ ∧
       complexify S = E * (modeEigenbasis n).conjTranspose ∧
       (FaithfulSpectrum nu →
         (let B := (2 * Complex.I) • (complexify V * complexify (sigma n))
          spectralArcoth nu B =
            E * complexify (signedDiagonal (fun j => realArcoth (2 * nu j))) * E⁻¹ ∧
          (2 * Complex.I) • (complexify (sigma n) * spectralArcoth nu B) =
            complexify (gibbsMatrix S nu))))) :=
  x5g_goal n hn V hV
