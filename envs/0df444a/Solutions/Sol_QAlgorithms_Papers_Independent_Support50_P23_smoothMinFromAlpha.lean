-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P23.smoothMinFromAlpha
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T19:32:03.742444+00:00
-- url     : https://prove2.me/submissions/f2bd559a-682b-4a9e-9c10-b72650a3ac08

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P23
import Mathlib
import Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P23_positiveThresholdExists
import Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P23_pinchingQuasiMonotone

section X5mod_AI_Base
open Matrix

section X5mod_AI_Base

/-- conjugation by an isometry as a non-unital star algebra hom -/
noncomputable def x5ai_conjHom {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (W : Matrix n m ℂ) (hW : Wᴴ * W = 1) : Matrix m m ℂ →⋆ₙₐ[ℂ] Matrix n n ℂ where
  toFun X := W * X * Wᴴ
  map_smul' c X := by simp
  map_zero' := by simp
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_mul' X Y := by
    calc W * (X * Y) * Wᴴ = W * X * (Wᴴ * W) * Y * Wᴴ := by rw [hW]; simp [Matrix.mul_assoc]
      _ = _ := by simp [Matrix.mul_assoc]
  map_star' X := by simp [Matrix.star_eq_conjTranspose, conjTranspose_mul, Matrix.mul_assoc]

theorem x5ai_finite_cont {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m ℂ) (f : ℝ → ℝ) :
    ContinuousOn f (quasispectrum ℝ M) := by
  have : (quasispectrum ℝ M).Finite := by
    rw [quasispectrum_eq_spectrum_union_zero]
    exact (M.finite_real_spectrum).union (Set.finite_singleton 0)
  exact this.continuousOn _

theorem x5ai_finite_cont' {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m ℂ) (f : ℝ → ℝ) :
    ContinuousOn f (spectrum ℝ M) :=
  M.finite_real_spectrum.continuousOn _

theorem x5ai_conj {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (W : Matrix n m ℂ) (hW : Wᴴ * W = 1) (M : Matrix m m ℂ) (hM : M.IsHermitian)
    (f : ℝ → ℝ) (hf : f 0 = 0) : cfc f (W * M * Wᴴ) = W * cfc f M * Wᴴ := by
  have hWM : (W * M * Wᴴ).IsHermitian := by
    simp [IsHermitian, conjTranspose_mul, hM.eq, Matrix.mul_assoc]
  have hc : Continuous (x5ai_conjHom W hW) := by
    change Continuous fun X : Matrix m m ℂ => W * X * Wᴴ; fun_prop
  have h := NonUnitalStarAlgHom.map_cfcₙ (R := ℝ) (S := ℂ) (p := IsSelfAdjoint) (q := IsSelfAdjoint)
    (x5ai_conjHom W hW) f M (x5ai_finite_cont M f) hf hc hM.isSelfAdjoint hWM.isSelfAdjoint
  have h2 : W * cfcₙ f M * Wᴴ = cfcₙ f (W * M * Wᴴ) := h
  have e1 : cfcₙ f M = cfc f M := cfcₙ_eq_cfc (x5ai_finite_cont M f) hf
  have e2 : cfcₙ f (W * M * Wᴴ) = cfc f (W * M * Wᴴ) := cfcₙ_eq_cfc (x5ai_finite_cont (W * M * Wᴴ) f) hf
  rw [← e1, ← e2, h2]

/-- identity tensor X as a star algebra hom -/
noncomputable def x5ai_kronHom (C : Type*) {n : Type*} [Fintype C] [DecidableEq C] [Fintype n] [DecidableEq n] :
    Matrix n n ℂ →⋆ₐ[ℂ] Matrix (C × n) (C × n) ℂ where
  toFun X := Matrix.kronecker (1 : Matrix C C ℂ) X
  map_one' := Matrix.one_kronecker_one
  map_mul' X Y := by
    have := Matrix.mul_kronecker_mul (1 : Matrix C C ℂ) (1 : Matrix C C ℂ) X Y
    rw [Matrix.mul_one] at this
    exact this
  map_zero' := by simp
  map_add' X Y := by simp [Matrix.kronecker_add]
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one]
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.smul_apply, Matrix.one_apply, Prod.mk.injEq]
    split_ifs <;> simp_all
  map_star' X := by simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker]

theorem x5ai_kron (C : Type*) {n : Type*} [Fintype C] [DecidableEq C] [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (hM : M.IsHermitian) (f : ℝ → ℝ) :
    cfc f (Matrix.kronecker (1 : Matrix C C ℂ) M) = Matrix.kronecker (1 : Matrix C C ℂ) (cfc f M) := by
  have hK : (Matrix.kronecker (1 : Matrix C C ℂ) M).IsHermitian := by
    simp [IsHermitian, Matrix.conjTranspose_kronecker, hM.eq]
  have h := StarAlgHom.map_cfc (R := ℝ) (S := ℂ) (p := IsSelfAdjoint) (q := IsSelfAdjoint)
    (x5ai_kronHom C (n := n)) f M (x5ai_finite_cont' M f)
    (by
      change Continuous fun X : Matrix n n ℂ => Matrix.kronecker (1 : Matrix C C ℂ) X
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [Matrix.kronecker, Matrix.kroneckerMap_apply]
      exact continuous_const.mul ((continuous_apply _).comp (continuous_apply _)))
    hM.isSelfAdjoint hK.isSelfAdjoint
  exact h.symm

end X5mod_AI_Base
end X5mod_AI_Base

section X5mod_LS_T1
open Matrix
open scoped ComplexOrder

namespace X5LS
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma tr_cfc {A : Matrix I I ℂ} (hA : A.IsHermitian)
    (f : ℝ → ℝ) : (cfc f A).trace = ∑ i, ((f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [hA.cfc_eq f, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  rfl

lemma cont (A : Matrix I I ℂ) (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) :=
  A.finite_real_spectrum.continuousOn _

lemma spec_nonneg {R : Matrix I I ℂ} (hR : R.PosSemidef) : ∀ x ∈ spectrum ℝ R, 0 ≤ x := by
  intro x hx
  rw [hR.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  exact hR.eigenvalues_nonneg i

lemma sq_herm (R : Matrix I I ℂ) : (cfc Real.sqrt R).IsHermitian :=
  (cfc_predicate Real.sqrt R : IsSelfAdjoint _)

lemma sq_mul_sq {R : Matrix I I ℂ} (hR : R.PosSemidef) : cfc Real.sqrt R * cfc Real.sqrt R = R := by
  rw [← cfc_mul (hf := cont R _) (hg := cont R _)]
  conv_rhs => rw [← cfc_id' ℝ R hR.isHermitian.isSelfAdjoint]
  exact cfc_congr fun x hx => Real.mul_self_sqrt (spec_nonneg hR x hx)

lemma tr_psd {R X : Matrix I I ℂ} (hR : R.PosSemidef) (hX : X.PosSemidef) :
    0 ≤ (R * X).trace.re := by
  set S := cfc Real.sqrt R
  have h : (S * X * Sᴴ).PosSemidef := hX.mul_mul_conjTranspose_same S
  have e : (R * X).trace = (S * X * Sᴴ).trace := by
    rw [← sq_mul_sq hR, (sq_herm R).eq, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  rw [e]
  exact (Complex.nonneg_iff.mp h.trace_nonneg).1

lemma tn_aux (M U : Matrix I I ℂ) (d : I → ℝ) (hUU : star U * U = 1) (hUU' : U * star U = 1)
    (e : M * Mᴴ = U * diagonal (RCLike.ofReal ∘ d) * star U) :
    (trace M).re ≤ ∑ j, Real.sqrt (d j) := by
  set K := star U * M * U with hK
  have hKK : K * Kᴴ = diagonal (RCLike.ofReal ∘ d) := by
    have h1 : Kᴴ = star U * Mᴴ * U := by
      simp [hK, conjTranspose_mul, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
    rw [h1]
    calc star U * M * U * (star U * Mᴴ * U) = star U * (M * Mᴴ) * U := by
          simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc U, hUU', Matrix.one_mul]
      _ = _ := by rw [e]; simp only [Matrix.mul_assoc]; rw [hUU, Matrix.mul_one,
            ← Matrix.mul_assoc, hUU, Matrix.one_mul]
  have htr : trace M = trace K := by
    rw [hK, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hUU', Matrix.mul_one]
  rw [htr, Matrix.trace, Complex.re_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hj : ∑ k, ‖K j k‖ ^ 2 = d j := by
    have := congrFun (congrFun hKK j) j
    simp only [mul_apply, conjTranspose_apply, diagonal_apply_eq, Function.comp_apply] at this
    have h2 : ∀ k, K j k * star (K j k) = ((‖K j k‖ ^ 2 : ℝ) : ℂ) := fun k => by
      rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [h2] at this
    rw [← Complex.ofReal_sum] at this
    exact Complex.ofReal_injective this
  have h3 : ‖K j j‖ ^ 2 ≤ d j := by
    rw [← hj]
    exact Finset.single_le_sum (f := fun k => ‖K j k‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ j)
  simp only [diag_apply]
  calc (K j j).re ≤ ‖K j j‖ := Complex.re_le_norm _
    _ = Real.sqrt (‖K j j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt h3

lemma tn (M : Matrix I I ℂ) : (trace M).re ≤ (trace (cfc Real.sqrt (M * Mᴴ))).re := by
  have hH : (M * Mᴴ).IsHermitian := isHermitian_mul_conjTranspose_self M
  have e : M * Mᴴ = (hH.eigenvectorUnitary : Matrix I I ℂ) *
      diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star (hH.eigenvectorUnitary : Matrix I I ℂ) := by
    conv_lhs => rw [← cfc_id' ℝ (M * Mᴴ)]
    rw [hH.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
    rfl
  rw [tr_cfc hH, Complex.re_sum]
  simp only [Complex.ofReal_re]
  exact tn_aux M _ _ (Unitary.coe_star_mul_self _) (Unitary.coe_mul_star_self _) e

end X5LS
end X5mod_LS_T1

section X5mod_LS_T2
open Matrix
open scoped ComplexOrder

namespace X5LS
variable {I : Type*} [Fintype I] [DecidableEq I]
set_option linter.unusedSectionVars false

open scoped MatrixOrder in
lemma cfc_psd {X : Matrix I I ℂ} (hX : X.IsHermitian) (f : ℝ → ℝ)
    (hf : ∀ x ∈ spectrum ℝ X, 0 ≤ f x) : (cfc f X).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg hf

open scoped Matrix.Norms.L2Operator MatrixOrder in
lemma sqrt_mono {A B : Matrix I I ℂ} (hA : A.PosSemidef) (hAB : (B - A).PosSemidef) :
    (cfc Real.sqrt B - cfc Real.sqrt A).PosSemidef := by
  have hA0 : (0 : Matrix I I ℂ) ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  have hle : A ≤ B := Matrix.le_iff.mpr hAB
  have hB0 : (0 : Matrix I I ℂ) ≤ B := hA0.trans hle
  have h := CFC.sqrt_le_sqrt A B hle
  rw [CFC.sqrt_eq_real_sqrt A hA0, CFC.sqrt_eq_real_sqrt B hB0,
    cfcₙ_eq_cfc (by exact (A.finite_real_spectrum.union (Set.finite_singleton 0)).continuousOn _ |>.mono (by rw [quasispectrum_eq_spectrum_union_zero])) (by simp),
    cfcₙ_eq_cfc (by exact (B.finite_real_spectrum.union (Set.finite_singleton 0)).continuousOn _ |>.mono (by rw [quasispectrum_eq_spectrum_union_zero])) (by simp)] at h
  exact Matrix.le_iff.mp h

lemma herm_cfc (X : Matrix I I ℂ) (f : ℝ → ℝ) : (cfc f X).IsHermitian :=
  (cfc_predicate f X : IsSelfAdjoint _)

/-- conjugation by a hermitian matrix preserves PSD -/
lemma conj_psd {X C : Matrix I I ℂ} (hX : X.PosSemidef) (hC : C.IsHermitian) :
    (C * X * C).PosSemidef := by
  have := hX.mul_mul_conjTranspose_same C
  rwa [hC.eq] at this

lemma re_tr_herm {G R : Matrix I I ℂ} (hR : R.IsHermitian) :
    (R * Gᴴ).trace.re = (G * R).trace.re := by
  have : R * Gᴴ = (G * R)ᴴ := by rw [conjTranspose_mul, hR.eq]
  rw [this, trace_conjTranspose]
  simp

end X5LS
end X5mod_LS_T2

section X5mod_LS_T3
open Matrix
open scoped ComplexOrder

namespace X5LS
variable {I : Type*} [Fintype I] [DecidableEq I]
set_option linter.unusedSectionVars false

lemma posneg (X : Matrix I I ℂ) (hX : X.IsHermitian) :
    X = cfc (fun x : ℝ => max x 0) X - cfc (fun x : ℝ => max (-x) 0) X := by
  rw [← cfc_sub (hf := cont X _) (hg := cont X _)]
  conv_lhs => rw [← cfc_id' ℝ X hX.isSelfAdjoint]
  refine cfc_congr fun x _ => ?_
  rcases le_total x 0 with h | h
  · simp [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
  · simp [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]

lemma iB_B {B : Matrix I I ℂ} (hB : B.PosSemidef) :
    cfc (fun x : ℝ => (Real.sqrt x)⁻¹) B * B = cfc Real.sqrt B := by
  conv_lhs => arg 2; rw [← cfc_id' ℝ B hB.isHermitian.isSelfAdjoint]
  rw [← cfc_mul (hf := cont B _) (hg := cont B _)]
  refine cfc_congr fun x hx => ?_
  have h0 := spec_nonneg hB x hx
  rcases h0.lt_or_eq with h | h
  · have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr h
    field_simp
    rw [Real.sq_sqrt h.le]
  · subst h; simp

lemma one_sub_P {B : Matrix I I ℂ} (hB : B.PosSemidef) :
    (1 - cfc (fun x : ℝ => (Real.sqrt x)⁻¹) B * B * cfc (fun x : ℝ => (Real.sqrt x)⁻¹) B).PosSemidef := by
  rw [iB_B hB, ← cfc_mul (hf := cont B _) (hg := cont B _),
    ← cfc_one ℝ B hB.isHermitian.isSelfAdjoint, ← cfc_sub (hf := cont B _) (hg := cont B _)]
  refine cfc_psd hB.isHermitian _ fun x hx => ?_
  have h0 := spec_nonneg hB x hx
  rcases h0.lt_or_eq with h | h
  · have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr h
    simp [hs.ne']
  · subst h; simp

theorem core (ρ A : Matrix I I ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) (hA : A.PosSemidef) :
    ∃ τ : Matrix I I ℂ, τ.PosSemidef ∧ τ.trace.re ≤ 1 ∧ (A - τ).PosSemidef ∧
      1 - (cfc (fun x : ℝ => max x 0) (ρ - A)).trace.re ≤
        (cfc Real.sqrt (cfc Real.sqrt ρ * τ * cfc Real.sqrt ρ)).trace.re := by
  have hX : (ρ - A).IsHermitian := hρ.isHermitian.sub hA.isHermitian
  set D := cfc (fun x : ℝ => max x 0) (ρ - A) with hD
  set N := cfc (fun x : ℝ => max (-x) 0) (ρ - A) with hN
  have hDpsd : D.PosSemidef := cfc_psd hX _ fun x _ => le_max_right _ _
  have hNpsd : N.PosSemidef := cfc_psd hX _ fun x _ => le_max_right _ _
  have hpn := posneg (ρ - A) hX
  set B := A + D with hBdef
  have hB : B.PosSemidef := hA.add hDpsd
  have hBρ : (B - ρ).PosSemidef := by
    have : B - ρ = N := by
      rw [hBdef]; rw [← hD, ← hN] at hpn
      calc A + D - ρ = D - (ρ - A) - 0 + 0 := by abel
        _ = N := by rw [hpn]; abel
    rw [this]; exact hNpsd
  have hBA : (B - A).PosSemidef := by rw [hBdef, add_sub_cancel_left]; exact hDpsd
  set sA := cfc Real.sqrt A
  set sB := cfc Real.sqrt B
  set iB := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) B
  set sρ := cfc Real.sqrt ρ
  have hsA : sA.IsHermitian := herm_cfc _ _
  have hiB : iB.IsHermitian := herm_cfc _ _
  have hsρ : sρ.IsHermitian := herm_cfc _ _
  set G := sA * iB with hG
  have hGh : Gᴴ = iB * sA := by rw [hG, conjTranspose_mul, hsA.eq, hiB.eq]
  have h1P := one_sub_P hB
  -- 1 - iB X iB is PSD whenever B - X is PSD
  have key : ∀ X : Matrix I I ℂ, (B - X).PosSemidef → (1 - iB * X * iB).PosSemidef := by
    intro X hX'
    have e : 1 - iB * X * iB = (1 - iB * B * iB) + iB * (B - X) * iB := by
      simp only [Matrix.mul_sub, Matrix.sub_mul]; abel
    rw [e]; exact h1P.add (conj_psd hX' hiB)
  refine ⟨G * ρ * Gᴴ, hρ.mul_mul_conjTranspose_same G, ?_, ?_, ?_⟩
  · -- trace bound
    have hGG : (1 - Gᴴ * G).PosSemidef := by
      have : Gᴴ * G = iB * A * iB := by
        rw [hGh, hG]; simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc sA sA, sq_mul_sq hA]
      rw [this]; exact key A hBA
    have h := tr_psd hρ hGG
    have e : (G * ρ * Gᴴ).trace = (ρ * (Gᴴ * G)).trace := by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
    rw [e]
    rw [Matrix.mul_sub, Matrix.mul_one, trace_sub, htr, Complex.sub_re, Complex.one_re] at h
    linarith
  · -- A - τ PSD
    have e : A - G * ρ * Gᴴ = sA * (1 - iB * ρ * iB) * sA := by
      rw [hGh, hG, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, sq_mul_sq hA]
      simp only [Matrix.mul_assoc]
    rw [e]; exact conj_psd (key ρ hBρ) hsA
  · -- fidelity
    set M := sρ * G * sρ with hM
    have hMh : Mᴴ = sρ * Gᴴ * sρ := by
      rw [hM, conjTranspose_mul, conjTranspose_mul, hsρ.eq, Matrix.mul_assoc]
    have hρ' : ρ = sρ * sρ := (sq_mul_sq hρ).symm
    have hMM : sρ * (G * ρ * Gᴴ) * sρ = M * Mᴴ := by
      calc sρ * (G * ρ * Gᴴ) * sρ = sρ * (G * (sρ * sρ) * Gᴴ) * sρ := by rw [← hρ']
        _ = M * Mᴴ := by rw [hMh, hM]; simp only [Matrix.mul_assoc]
    rw [hMM]
    refine le_trans ?_ (tn M)
    have htrM : M.trace = (G * ρ).trace := by
      rw [hM, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, sq_mul_sq hρ]
    rw [htrM]
    -- 2 - G - Gᴴ is PSD
    have h2 : ((2 : Matrix I I ℂ) - G - Gᴴ).PosSemidef := by
      have hGG : (1 - Gᴴ * G).PosSemidef := by
        have : Gᴴ * G = iB * A * iB := by
          rw [hGh, hG]; simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc sA sA, sq_mul_sq hA]
        rw [this]; exact key A hBA
      have h1 := posSemidef_conjTranspose_mul_self (1 - G)
      have e : (2 : Matrix I I ℂ) - G - Gᴴ = (1 - G)ᴴ * (1 - G) + (1 - Gᴴ * G) := by
        rw [conjTranspose_sub, conjTranspose_one]
        simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
        rw [show (2 : Matrix I I ℂ) = 1 + 1 by norm_num]; abel
      rw [e]; exact h1.add hGG
    have hT := tr_psd hBρ h2
    have hT2 : 0 ≤ (sA * (sB - sA)).trace.re := tr_psd (cfc_psd hA.isHermitian _ fun x _ => Real.sqrt_nonneg x) (sqrt_mono hA hBA)
    have eGB : (G * B).trace = (sA * sB).trace := by
      rw [hG, Matrix.mul_assoc, iB_B hB]
    have eA : (sA * sA).trace = A.trace := by rw [sq_mul_sq hA]
    have r1 := re_tr_herm (G := G) hB.isHermitian
    have r2 := re_tr_herm (G := G) hρ.isHermitian
    rw [Matrix.mul_sub, trace_sub, eA, Complex.sub_re] at hT2
    have eT : ((B - ρ) * (2 - G - Gᴴ)).trace.re =
        2 * B.trace.re - (B * G).trace.re - (B * Gᴴ).trace.re - 2 * ρ.trace.re
          + (ρ * G).trace.re + (ρ * Gᴴ).trace.re := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, trace_sub, Complex.sub_re]
      rw [show (2 : Matrix I I ℂ) = (2 : ℂ) • (1 : Matrix I I ℂ) by
        rw [two_smul]; norm_num]
      simp [trace_smul]
      ring
    rw [eT, r1, r2, Matrix.trace_mul_comm B G, Matrix.trace_mul_comm ρ G, eGB, htr] at hT
    have eB : B.trace.re = A.trace.re + D.trace.re := by rw [hBdef, trace_add, Complex.add_re]
    simp only [Complex.one_re] at hT
    linarith

end X5LS
end X5mod_LS_T3

section X5mod_EO_PT
open Matrix
open scoped ComplexOrder Kronecker

namespace X5EO
set_option linter.unusedSectionVars false
open QAlgorithms

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- embedding of a B-vector into the a-th block -/
def emb (a : A) (y : B → ℂ) : A × B → ℂ := fun p => if p.1 = a then y p.2 else 0

lemma pt_kron (rho : Matrix (A × B) (A × B) ℂ) (Y : Matrix B B ℂ) :
    (rho * ((1 : Matrix A A ℂ) ⊗ₖ Y)).trace = (traceLeft rho * Y).trace := by
  simp only [Matrix.trace, diag_apply, mul_apply, kronecker_apply, one_apply, traceLeft, of_apply,
    Fintype.sum_prod_type, ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]

lemma qf_emb (rho : Matrix (A × B) (A × B) ℂ) (y : B → ℂ) :
    star y ⬝ᵥ (traceLeft rho *ᵥ y) = ∑ a, star (emb a y) ⬝ᵥ (rho *ᵥ emb a y) := by
  simp only [dotProduct, mulVec, traceLeft, of_apply, emb, Pi.star_apply, Fintype.sum_prod_type,
    apply_ite (star : ℂ → ℂ), star_zero, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum, Finset.sum_mul]
  calc _ = ∑ x : B, ∑ i : A, ∑ y1 : B, star (y x) * (rho (i, x) (i, y1) * y y1) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

lemma tl_psd {rho : Matrix (A × B) (A × B) ℂ} (h : rho.PosSemidef) : (traceLeft rho).PosSemidef := by
  have hH : (traceLeft rho).IsHermitian := by
    ext b b'
    simp only [conjTranspose_apply, traceLeft, of_apply, star_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have := congrFun (congrFun h.isHermitian (a, b)) (a, b')
    rw [conjTranspose_apply] at this
    exact this
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH fun y => ?_
  rw [qf_emb]
  exact Finset.sum_nonneg fun a _ => h.dotProduct_mulVec_nonneg _

lemma tl_trace (rho : Matrix (A × B) (A × B) ℂ) : (traceLeft rho).trace = rho.trace := by
  simp only [Matrix.trace, diag_apply, traceLeft, of_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

lemma tl_density {rho : Matrix (A × B) (A × B) ℂ} (h : IsDensityMatrix rho) : IsDensityMatrix (traceLeft rho) :=
  ⟨tl_psd h.1, by rw [tl_trace, h.2]⟩

/-- (1 ⊗ Y) applied to the block embedding -/
lemma kron_emb (Y : Matrix B B ℂ) (a : A) (y : B → ℂ) :
    ((1 : Matrix A A ℂ) ⊗ₖ Y) *ᵥ emb a y = emb a (Y *ᵥ y) := by
  ext ⟨a', b⟩
  simp only [mulVec, dotProduct, kronecker_apply, one_apply, emb, Fintype.sum_prod_type, ite_mul,
    one_mul, zero_mul, mul_ite, mul_zero]
  by_cases h : a' = a
  · subst h; simp
  · simp [h, Ne.symm h]

lemma emb_sum (x : A × B → ℂ) : x = ∑ a, emb a (fun b => x (a, b)) := by
  ext ⟨a', b⟩
  simp [emb, Finset.sum_apply]

/-- kernel of (1⊗Y) splits blockwise -/
lemma ker_kron {Y : Matrix B B ℂ} {x : A × B → ℂ} (h : ((1 : Matrix A A ℂ) ⊗ₖ Y) *ᵥ x = 0) (a : A) :
    Y *ᵥ (fun b => x (a, b)) = 0 := by
  ext b
  have := congrFun h (a, b)
  simpa [mulVec, dotProduct, kronecker_apply, one_apply, Fintype.sum_prod_type] using this

lemma supp_tl {rho : Matrix (A × B) (A × B) ℂ} (h : rho.PosSemidef) :
    LinearMap.ker ((1 : Matrix A A ℂ) ⊗ₖ traceLeft rho).mulVecLin ≤ LinearMap.ker rho.mulVecLin := by
  intro x hx
  simp only [LinearMap.mem_ker, mulVecLin_apply] at hx ⊢
  have hblk : ∀ a, traceLeft rho *ᵥ (fun b => x (a, b)) = 0 := ker_kron hx
  have hzero : ∀ a a', rho *ᵥ emb a' (fun b => x (a, b)) = 0 := by
    intro a a'
    have h0 : star (fun b => x (a, b)) ⬝ᵥ (traceLeft rho *ᵥ (fun b => x (a, b))) = 0 := by
      rw [hblk a, dotProduct_zero]
    rw [qf_emb] at h0
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun a' _ => h.dotProduct_mulVec_nonneg
      (emb a' (fun b => x (a, b))))).1 h0 a' (Finset.mem_univ _)
    exact (Matrix.PosSemidef.dotProduct_mulVec_zero_iff h _).1 this
  rw [emb_sum x, mulVec_sum]
  exact Finset.sum_eq_zero fun a _ => hzero a a

lemma supp_tl_of {rho : Matrix (A × B) (A × B) ℂ} {sigma : Matrix B B ℂ}
    (h : LinearMap.ker ((1 : Matrix A A ℂ) ⊗ₖ sigma).mulVecLin ≤ LinearMap.ker rho.mulVecLin) :
    LinearMap.ker sigma.mulVecLin ≤ LinearMap.ker (traceLeft rho).mulVecLin := by
  intro y hy
  simp only [LinearMap.mem_ker, mulVecLin_apply] at hy ⊢
  have h1 : ∀ a, rho *ᵥ emb a y = 0 := by
    intro a
    have := h (x := emb a y) (by simp only [LinearMap.mem_ker, mulVecLin_apply]; rw [kron_emb, hy]; ext p; simp [emb])
    simpa using this
  ext b
  have : (traceLeft rho *ᵥ y) b = ∑ a, (rho *ᵥ emb a y) (a, b) := by
    simp only [mulVec, dotProduct, traceLeft, of_apply, emb, Fintype.sum_prod_type, mul_ite, mul_zero,
      Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, Finset.sum_mul]
    exact Finset.sum_comm
  rw [this]
  simp [h1]

end X5EO
end X5mod_EO_PT

section X5mod_OL_Base
open Matrix
open scoped ComplexOrder

namespace X5OL

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- overlap matrix of the two eigenbases -/
noncomputable def ov {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) : Matrix I I ℂ :=
  star (hR.eigenvectorUnitary : Matrix I I ℂ) * (hN.eigenvectorUnitary : Matrix I I ℂ)

noncomputable def w {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) (i j : I) : ℝ :=
  ‖ov hR hN i j‖ ^ 2

lemma ov_unitary {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) :
    ov hR hN * star (ov hR hN) = 1 := by
  unfold ov
  have hU : star (hR.eigenvectorUnitary : Matrix I I ℂ) * (hR.eigenvectorUnitary : Matrix I I ℂ) = 1 :=
    Unitary.star_mul_self_of_mem (hR.eigenvectorUnitary).2
  have hV : (hN.eigenvectorUnitary : Matrix I I ℂ) * star (hN.eigenvectorUnitary : Matrix I I ℂ) = 1 :=
    Unitary.mul_star_self_of_mem (hN.eigenvectorUnitary).2
  rw [star_mul, star_star, Matrix.mul_assoc, ← Matrix.mul_assoc (hN.eigenvectorUnitary : Matrix I I ℂ),
    hV, Matrix.one_mul, hU]

lemma w_row {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) (i : I) :
    ∑ j, w hR hN i j = 1 := by
  have h := congrFun (congrFun (ov_unitary hR hN) i) i
  rw [mul_apply, one_apply_eq] at h
  have : (∑ j, ((w hR hN i j : ℝ) : ℂ)) = 1 := by
    rw [← h]; refine Finset.sum_congr rfl fun j _ => ?_
    simp only [w, star_apply, Complex.ofReal_pow]
    rw [RCLike.star_def, Complex.mul_conj']
  exact_mod_cast this

lemma w_nonneg {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) (i j : I) :
    0 ≤ w hR hN i j := by unfold w; positivity

lemma tr_cfc_cfc {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) (f g : ℝ → ℝ) :
    (cfc f R * cfc g N).trace =
      ∑ i, ∑ j, ((f (hR.eigenvalues i) * g (hN.eigenvalues j) * w hR hN i j : ℝ) : ℂ) := by
  rw [hR.cfc_eq, hN.cfc_eq]
  unfold IsHermitian.cfc
  simp only [Unitary.conjStarAlgAut_apply]
  set U := (hR.eigenvectorUnitary : Matrix I I ℂ)
  set V := (hN.eigenvectorUnitary : Matrix I I ℂ)
  set Df := diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ f ∘ hR.eigenvalues)
  set Dg := diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ g ∘ hN.eigenvalues)
  have hU : star U * U = 1 := Unitary.star_mul_self_of_mem (hR.eigenvectorUnitary).2
  have hU' : U * star U = 1 := Unitary.mul_star_self_of_mem (hR.eigenvectorUnitary).2
  have : (U * Df * star U * (V * Dg * star V)).trace = (Df * (star U * V) * Dg * star (star U * V)).trace := by
    rw [star_mul, star_star]
    rw [show U * Df * star U * (V * Dg * star V) = U * (Df * (star U * V) * Dg * (star V * U)) * star U by
      simp only [Matrix.mul_assoc]; rw [hU']; simp]
    rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]
  rw [this]
  change (Df * ov hR hN * Dg * star (ov hR hN)).trace = _
  have hE : ∀ i k, (Df * ov hR hN * Dg) i k =
      ((f (hR.eigenvalues i) : ℝ) : ℂ) * ov hR hN i k * ((g (hN.eigenvalues k) : ℝ) : ℂ) := by
    intro i k; simp [Df, Dg, diagonal_mul, mul_diagonal]
  simp only [Matrix.trace, diag_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hE, star_apply]
  simp only [w, Complex.ofReal_mul, Complex.ofReal_pow]
  rw [← Complex.mul_conj', RCLike.star_def]
  ring

lemma ov_apply {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) (i j : I) :
    ov hR hN i j = star (hR.eigenvectorBasis i).ofLp ⬝ᵥ (hN.eigenvectorBasis j).ofLp := by
  simp only [ov, mul_apply, star_apply, IsHermitian.eigenvectorUnitary_apply, dotProduct, Pi.star_apply]

lemma supp_fwd {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian)
    (h : LinearMap.ker N.mulVecLin ≤ LinearMap.ker R.mulVecLin) (i j : I)
    (hi : hR.eigenvalues i ≠ 0) (hj : hN.eigenvalues j = 0) : ov hR hN i j = 0 := by
  set b := (hR.eigenvectorBasis i).ofLp
  set v := (hN.eigenvectorBasis j).ofLp
  have hNv : N *ᵥ v = 0 := by rw [hN.mulVec_eigenvectorBasis j, hj, zero_smul]
  have hRv : R *ᵥ v = 0 := by
    have := h (show v ∈ LinearMap.ker N.mulVecLin by rw [LinearMap.mem_ker, mulVecLin_apply]; exact hNv)
    rwa [LinearMap.mem_ker, mulVecLin_apply] at this
  have key : ((hR.eigenvalues i : ℝ) : ℂ) * (star b ⬝ᵥ v) = 0 := by
    have hb : R *ᵥ b = hR.eigenvalues i • b := hR.mulVec_eigenvectorBasis i
    have : star (R *ᵥ b) ⬝ᵥ v = star b ⬝ᵥ (R *ᵥ v) := by
      rw [star_mulVec, hR.eq, dotProduct_mulVec]
    rw [hRv, dotProduct_zero, hb, star_smul] at this
    rw [← this, smul_dotProduct]
    simp [RCLike.real_smul_eq_coe_mul]
  rw [ov_apply]
  rcases mul_eq_zero.1 key with h1 | h1
  · exact absurd (by exact_mod_cast h1) hi
  · exact h1

lemma spec_mulVec {R : Matrix I I ℂ} (hR : R.IsHermitian) (x : I → ℂ) :
    R *ᵥ x = (hR.eigenvectorUnitary : Matrix I I ℂ) *ᵥ
      (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ hR.eigenvalues) *ᵥ (star (hR.eigenvectorUnitary : Matrix I I ℂ) *ᵥ x)) := by
  conv_lhs => rw [hR.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, ← mulVec_mulVec, ← mulVec_mulVec]

lemma supp_bwd {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian)
    (h : ∀ i j, hR.eigenvalues i ≠ 0 → hN.eigenvalues j = 0 → ov hR hN i j = 0) :
    LinearMap.ker N.mulVecLin ≤ LinearMap.ker R.mulVecLin := by
  intro x hx
  rw [LinearMap.mem_ker, mulVecLin_apply] at hx ⊢
  set U := (hR.eigenvectorUnitary : Matrix I I ℂ)
  set V := (hN.eigenvectorUnitary : Matrix I I ℂ)
  have hV : V * star V = 1 := Unitary.mul_star_self_of_mem (hN.eigenvectorUnitary).2
  have hV' : star V * V = 1 := Unitary.star_mul_self_of_mem (hN.eigenvectorUnitary).2
  set c := star V *ᵥ x
  have hc : ∀ j, hN.eigenvalues j ≠ 0 → c j = 0 := by
    intro j hj
    have h1 : star V *ᵥ (N *ᵥ x) = 0 := by rw [hx, mulVec_zero]
    rw [spec_mulVec hN, mulVec_mulVec, hV', one_mulVec] at h1
    have := congrFun h1 j
    rw [mulVec_diagonal] at this
    simp only [Function.comp_apply, Pi.zero_apply] at this
    rcases mul_eq_zero.1 this with h2 | h2
    · exact absurd (by simpa using h2) hj
    · exact h2
  have hUx : star U *ᵥ x = ov hR hN *ᵥ c := by
    rw [show ov hR hN = star U * V from rfl, mulVec_mulVec, Matrix.mul_assoc, hV, Matrix.mul_one]
  have hD : diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ hR.eigenvalues) *ᵥ (star U *ᵥ x) = 0 := by
    ext i
    rw [hUx, mulVec_diagonal, Pi.zero_apply]
    by_cases hi : hR.eigenvalues i = 0
    · simp [hi]
    · simp only [mulVec, dotProduct]
      rw [Finset.sum_eq_zero, mul_zero]
      intro j _
      by_cases hj : hN.eigenvalues j = 0
      · rw [h i j hi hj, zero_mul]
      · rw [hc j hj, mul_zero]
  rw [spec_mulVec hR, hD, mulVec_zero]

end X5OL
end X5mod_OL_Base

section X5mod_EO_Klein
open Matrix
open scoped ComplexOrder

namespace X5OL
set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma w_col {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) (j : I) :
    ∑ i, w hR hN i j = 1 := by
  have hu : star (ov hR hN) * ov hR hN = 1 := mul_eq_one_comm.1 (ov_unitary hR hN)
  have h := congrFun (congrFun hu j) j
  rw [mul_apply, one_apply_eq] at h
  have : (∑ i, ((w hR hN i j : ℝ) : ℂ)) = 1 := by
    rw [← h]; refine Finset.sum_congr rfl fun i _ => ?_
    simp only [w, star_apply, Complex.ofReal_pow]
    rw [RCLike.star_def, mul_comm, Complex.mul_conj']
  exact_mod_cast this

lemma tr_eig {S : Matrix I I ℂ} (hS : S.IsHermitian) : S.trace.re = ∑ j, hS.eigenvalues j := by
  have := X5LS.tr_cfc hS (fun x => x)
  rw [cfc_id' ℝ S hS.isSelfAdjoint] at this
  rw [this, Complex.re_sum]; simp

theorem klein {P S : Matrix I I ℂ} (hP : P.PosSemidef) (htrP : P.trace = 1) (hS : S.PosSemidef)
    (htrS : S.trace = 1) (hsupp : LinearMap.ker S.mulVecLin ≤ LinearMap.ker P.mulVecLin) :
    (P * cfc (Real.logb 2) S).trace.re ≤ (P * cfc (Real.logb 2) P).trace.re := by
  have hR := hP.isHermitian
  have hN := hS.isHermitian
  set ν := hR.eigenvalues
  set μ := hN.eigenvalues
  set W := w hR hN
  have hν : ∀ i, 0 ≤ ν i := hP.eigenvalues_nonneg
  have hμ : ∀ j, 0 ≤ μ j := hS.eigenvalues_nonneg
  have hW : ∀ i j, 0 ≤ W i j := w_nonneg hR hN
  have hrow : ∀ i, ∑ j, W i j = 1 := w_row hR hN
  have hcol : ∀ j, ∑ i, W i j = 1 := w_col hR hN
  have htrν : ∑ i, ν i = 1 := by rw [← tr_eig hR, htrP, Complex.one_re]
  have htrμ : ∑ j, μ j = 1 := by rw [← tr_eig hN, htrS, Complex.one_re]
  have hL : (P * cfc (Real.logb 2) S).trace.re = ∑ i, ∑ j, ν i * Real.logb 2 (μ j) * W i j := by
    have := tr_cfc_cfc hR hN (fun x => x) (Real.logb 2)
    rw [cfc_id' ℝ P hR.isSelfAdjoint] at this
    rw [this, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_sum]; simp only [Complex.ofReal_re]; rfl
  have hRt : (P * cfc (Real.logb 2) P).trace.re = ∑ i, ∑ j, ν i * Real.logb 2 (ν i) * W i j := by
    have e : P * cfc (Real.logb 2) P = cfc (fun x => x * Real.logb 2 x) P := by
      conv_lhs => arg 1; rw [← cfc_id' ℝ P hR.isSelfAdjoint]
      rw [← cfc_mul (hf := X5LS.cont P _) (hg := X5LS.cont P _)]
    rw [e, X5LS.tr_cfc hR, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum, hrow, mul_one, Complex.ofReal_re]
  rw [hL, hRt, ← sub_nonneg]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have key : ∀ i j, ν i * Real.logb 2 (μ j) * W i j - ν i * Real.logb 2 (ν i) * W i j ≤
      W i j * (μ j - ν i) / Real.log 2 := by
    intro i j
    rcases (hν i).lt_or_eq with hi | hi
    · rcases (hμ j).lt_or_eq with hj | hj
      · have h1 := Real.log_le_sub_one_of_pos (div_pos hj hi)
        rw [Real.log_div hj.ne' hi.ne'] at h1
        have h2 : ν i * (Real.log (μ j) - Real.log (ν i)) ≤ μ j - ν i := by
          have := mul_le_mul_of_nonneg_left h1 hi.le
          have e : ν i * (μ j / ν i - 1) = μ j - ν i := by field_simp
          linarith
        unfold Real.logb
        rw [le_div_iff₀ hl2]
        have : (ν i * (Real.log (μ j) / Real.log 2) * W i j - ν i * (Real.log (ν i) / Real.log 2) * W i j) *
            Real.log 2 = W i j * (ν i * (Real.log (μ j) - Real.log (ν i))) := by
          field_simp
        rw [this]
        exact mul_le_mul_of_nonneg_left h2 (hW i j)
      · have hw : W i j = 0 := by
          simp only [W, w, supp_fwd hR hN hsupp i j hi.ne' hj.symm, norm_zero]; norm_num
        rw [hw]; simp
    · rw [← hi]; simp only [zero_mul, sub_zero, sub_self]
      exact div_nonneg (mul_nonneg (hW i j) (hμ j)) hl2.le
  have hsum : ∑ i, ∑ j, W i j * (μ j - ν i) / Real.log 2 = 0 := by
    simp only [← Finset.sum_div, mul_sub, Finset.sum_sub_distrib]
    have a1 : ∑ x, ∑ x1, W x x1 * μ x1 = 1 := by
      rw [Finset.sum_comm]; simp only [← Finset.sum_mul, hcol, one_mul, htrμ]
    have a2 : ∑ x, ∑ x1, W x x1 * ν x = 1 := by simp only [← Finset.sum_mul, hrow, one_mul, htrν]
    rw [a1, a2]; simp
  have hle := (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j).trans hsum.le
  simp only [Finset.sum_sub_distrib] at hle ⊢
  linarith

end X5OL
end X5mod_EO_Klein

section X5mod_EO_H2
open Matrix
open scoped ComplexOrder

namespace X5LS
variable {I : Type*} [Fintype I] [DecidableEq I]
set_option linter.unusedSectionVars false

lemma ker_of_le {ρ S : Matrix I I ℂ} (hρ : ρ.PosSemidef) (c : ℝ) (h : ((c : ℂ) • S - ρ).PosSemidef) :
    LinearMap.ker S.mulVecLin ≤ LinearMap.ker ρ.mulVecLin := by
  intro x hx
  simp only [LinearMap.mem_ker, mulVecLin_apply] at hx ⊢
  have h1 := h.dotProduct_mulVec_nonneg x
  rw [sub_mulVec, smul_mulVec, hx, smul_zero, zero_sub, dotProduct_neg] at h1
  have h2 := hρ.dotProduct_mulVec_nonneg x
  have h3 : star x ⬝ᵥ (ρ *ᵥ x) = 0 := le_antisymm (neg_nonneg.1 h1) h2
  exact (Matrix.PosSemidef.dotProduct_mulVec_zero_iff hρ x).1 h3

/-- ρ (1 - Π) = 0 when ker S ⊆ ker ρ, Π the support projection of S -/
lemma supp_proj {ρ S : Matrix I I ℂ} (hS : S.PosSemidef)
    (hk : LinearMap.ker S.mulVecLin ≤ LinearMap.ker ρ.mulVecLin) :
    ρ * (1 - cfc (fun x : ℝ => Real.sqrt x) S * cfc (fun x : ℝ => (Real.sqrt x)⁻¹) S) = 0 := by
  set Q := 1 - cfc (fun x : ℝ => Real.sqrt x) S * cfc (fun x : ℝ => (Real.sqrt x)⁻¹) S
  have hSQ : S * Q = 0 := by
    simp only [Q]
    rw [← cfc_mul (hf := cont S _) (hg := cont S _), ← cfc_one ℝ S hS.isHermitian.isSelfAdjoint,
      ← cfc_sub (hf := cont S _) (hg := cont S _)]
    conv_lhs => arg 1; rw [← cfc_id' ℝ S hS.isHermitian.isSelfAdjoint]
    rw [← cfc_mul (hf := cont S _) (hg := cont S _)]
    rw [show (0 : Matrix I I ℂ) = cfc (fun _ : ℝ => (0 : ℝ)) S by rw [cfc_const_zero]]
    refine cfc_congr fun x hx => ?_
    have h0 := spec_nonneg hS x hx
    rcases h0.lt_or_eq with h | h
    · have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr h
      simp [hs.ne']
    · subst h; simp
  ext i j
  have hv : S *ᵥ (Q *ᵥ Pi.single j 1) = 0 := by rw [mulVec_mulVec, hSQ, zero_mulVec]
  have := hk (x := Q *ᵥ Pi.single j 1) (by simpa using hv)
  simp only [LinearMap.mem_ker, mulVecLin_apply, mulVec_mulVec] at this
  have := congrFun this i
  simpa [mulVec_single] using this

theorem tr_sq_inv {ρ S : Matrix I I ℂ} (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) (hS : S.PosSemidef)
    (c : ℝ) (hc : 0 < c) (h : ((c : ℂ) • S - ρ).PosSemidef) :
    (cfc (fun x : ℝ => x ^ (2 : ℝ)) ρ * cfc (fun x : ℝ => if x = 0 then 0 else x ^ (1 - (2 : ℝ))) S).trace.re
      ≤ c := by
  have hk := ker_of_le hρ c h
  set sS := cfc Real.sqrt S with hsSdef
  set iS := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) S with hiSdef
  have hsS : sS.IsHermitian := herm_cfc _ _
  have hiS : iS.IsHermitian := herm_cfc _ _
  have hSS : sS * sS = S := sq_mul_sq hS
  -- P = sS iS = iS sS
  have hPc : sS * iS = cfc (fun x : ℝ => Real.sqrt x * (Real.sqrt x)⁻¹) S :=
    (cfc_mul (hf := cont S _) (hg := cont S _) ..).symm
  have hPi : iS * sS = sS * iS := by
    rw [← cfc_mul (hf := cont S _) (hg := cont S _), ← cfc_mul (hf := cont S _) (hg := cont S _)]
    exact cfc_congr fun x _ => mul_comm _ _
  have hρP : ρ * (sS * iS) = ρ := by
    have := supp_proj hS hk
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
    exact this.symm
  have hPρ : (sS * iS) * ρ = ρ := by
    have h1 : (ρ * (sS * iS))ᴴ = ρᴴ := by rw [hρP]
    rw [conjTranspose_mul, hρ.isHermitian.eq, conjTranspose_mul, hsS.eq, hiS.eq, hPi] at h1
    exact h1
  have hiSP : iS * (sS * iS) = iS := by
    rw [hPc, ← cfc_mul (hf := cont S _) (hg := cont S _)]
    refine cfc_congr fun x hx => ?_
    rcases (spec_nonneg hS x hx).lt_or_eq with h | h
    · have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr h
      field_simp
    · subst h; simp
  set Z := iS * ρ * iS with hZ
  have hZpsd : Z.PosSemidef := conj_psd hρ hiS
  have hρZ : sS * Z * sS = ρ := by
    rw [hZ]
    calc sS * (iS * ρ * iS) * sS = (sS * iS) * ρ * (iS * sS) := by simp only [Matrix.mul_assoc]
      _ = ρ := by rw [hPi, hPρ, hρP]
  have hZP : Z * (sS * iS) = Z := by
    simp only [hZ, Matrix.mul_assoc]; rw [hiSP]
  -- c - Z is PSD
  have hcZ : ((c : ℂ) • (1 : Matrix I I ℂ) - Z).PosSemidef := by
    have e : (c : ℂ) • (1 : Matrix I I ℂ) - Z =
        (c : ℂ) • (1 - iS * S * iS) + iS * ((c : ℂ) • S - ρ) * iS := by
      simp only [hZ, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub]; abel
    rw [e]
    exact ((one_sub_P hS).smul (by exact_mod_cast hc.le)).add (conj_psd h hiS)
  have hspec : ∀ x ∈ spectrum ℝ Z, 0 ≤ x ∧ x ≤ c := by
    intro x hx
    refine ⟨spec_nonneg hZpsd x hx, ?_⟩
    open scoped MatrixOrder in
    have hle : Z ≤ algebraMap ℝ (Matrix I I ℂ) c := by
      rw [Matrix.le_iff, Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul]
      exact hcZ
    exact (le_algebraMap_iff_spectrum_le (ha := hZpsd.isHermitian.isSelfAdjoint)).1 hle x hx
  have hZ2 : ((c : ℂ) • Z - Z * Z).PosSemidef := by
    have e : cfc (fun x : ℝ => c * x - x * x) Z = (c : ℂ) • Z - Z * Z := by
      rw [cfc_sub (fun x : ℝ => c * x) (fun x : ℝ => x * x) Z (hf := cont Z _) (hg := cont Z _),
        cfc_const_mul c (fun x : ℝ => x) Z (hf := cont Z _),
        cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) Z (hf := cont Z _) (hg := cont Z _),
        cfc_id' ℝ Z hZpsd.isHermitian.isSelfAdjoint, Complex.coe_smul]
    rw [← e]
    exact cfc_psd hZpsd.isHermitian _ fun x hx => by nlinarith [hspec x hx]
  have hsq : cfc (fun x : ℝ => x ^ (2 : ℝ)) ρ = ρ * ρ := by
    have e : cfc (fun x : ℝ => x ^ (2 : ℝ)) ρ = cfc (fun x : ℝ => x * x) ρ :=
      cfc_congr fun x _ => by rw [Real.rpow_two, sq]
    rw [e, cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) ρ (hf := cont ρ _) (hg := cont ρ _),
      cfc_id' ℝ ρ hρ.isHermitian.isSelfAdjoint]
  have hinv : cfc (fun x : ℝ => if x = 0 then 0 else x ^ (1 - (2 : ℝ))) S = iS * iS := by
    rw [← cfc_mul (hf := cont S _) (hg := cont S _)]
    refine cfc_congr fun x hx => ?_
    rcases (spec_nonneg hS x hx).lt_or_eq with h | h
    · rw [if_neg h.ne', show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one, ← mul_inv,
        Real.mul_self_sqrt h.le]
    · subst h; simp
  rw [hsq, hinv]
  have hT : (ρ * ρ * (iS * iS)).trace = (Z * Z * S).trace := by
    calc (ρ * ρ * (iS * iS)).trace = (iS * ρ * (ρ * iS)).trace := by
          rw [show ρ * ρ * (iS * iS) = (ρ * ρ * iS) * iS by simp only [Matrix.mul_assoc],
            Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
      _ = (iS * (sS * Z * sS) * ((sS * Z * sS) * iS)).trace := by rw [hρZ]
      _ = ((iS * sS) * Z * (sS * sS) * Z * (sS * iS)).trace := by simp only [Matrix.mul_assoc]
      _ = ((sS * iS) * (Z * S * Z * (sS * iS))).trace := by
          rw [hPi, hSS]; simp only [Matrix.mul_assoc]
      _ = (Z * S * Z * (sS * iS) * (sS * iS)).trace := by
          rw [Matrix.trace_mul_comm]
      _ = (Z * Z * S).trace := by
          have e : Z * S * Z * (sS * iS) * (sS * iS) = Z * S * Z := by
            rw [Matrix.mul_assoc (Z * S), hZP, Matrix.mul_assoc (Z * S), hZP]
          rw [e, Matrix.trace_mul_comm (Z * S) Z, ← Matrix.mul_assoc]
  have hone : (Z * S).trace = 1 := by
    rw [← htr, ← hρZ, ← hSS, Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm sS]; simp only [Matrix.mul_assoc]
  have hfin := tr_psd hZ2 (cfc_psd hS.isHermitian Real.sqrt (fun x _ => Real.sqrt_nonneg x) |>.mul_mul_conjTranspose_same sS |> fun _ => hS)
  rw [Matrix.sub_mul, trace_sub, Matrix.smul_mul, trace_smul, hone, Complex.sub_re] at hfin
  rw [hT]
  simp at hfin
  linarith

end X5LS
end X5mod_EO_H2

section X5mod_AD_Kron
open Matrix Polynomial
open scoped ComplexOrder Kronecker

namespace X5AD
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma aeval_diag (δ : ι → ℂ) (p : ℝ[X]) :
    aeval (diagonal δ) p = diagonal (fun k => aeval (δ k) p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, diagonal_add]
  | monomial k c =>
    simp only [aeval_monomial, Matrix.algebraMap_eq_diagonal, diagonal_pow, diagonal_mul_diagonal]
    rfl

lemma cfc_diag (d : ι → ℝ) (f : ℝ → ℝ) :
    cfc f (diagonal (fun k => ((d k : ℝ) : ℂ))) = diagonal (fun k => ((f (d k) : ℝ) : ℂ)) := by
  set D := diagonal (fun k => ((d k : ℝ) : ℂ))
  have hfin : (spectrum ℝ D).Finite := D.finite_real_spectrum
  set s : Finset ℝ := Finset.univ.image d ∪ hfin.toFinset
  set p := Lagrange.interpolate s (fun x : ℝ => x) f
  have hp : ∀ x ∈ s, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := fun x : ℝ => x) f (fun a _ b _ h => h) hx
  have hD : IsSelfAdjoint D := by
    rw [← Matrix.isHermitian_iff_isSelfAdjoint]
    exact isHermitian_diagonal_of_self_adjoint _ (by ext k; simp [Complex.conj_ofReal])
  have h1 : cfc f D = cfc (fun x => p.eval x) D :=
    cfc_congr fun x hx => (hp x (Finset.mem_union_right _ (hfin.mem_toFinset.2 hx))).symm
  rw [h1, cfc_polynomial p D hD, aeval_diag]
  congr 1; ext k
  rw [show ((d k : ℝ) : ℂ) = algebraMap ℝ ℂ (d k) from rfl, aeval_algebraMap_apply,
    Polynomial.aeval_def, Algebra.algebraMap_self, ← Polynomial.eval,
    hp _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ k)))]
  rfl

lemma spec {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    X = (hX.eigenvectorUnitary : Matrix ι ι ℂ) * diagonal (fun k => ((hX.eigenvalues k : ℝ) : ℂ)) *
      (hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ := by
  conv_lhs => rw [← cfc_id' ℝ X hX.isSelfAdjoint]
  rw [hX.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rfl

lemma cfc_spec {X : Matrix ι ι ℂ} (hX : X.IsHermitian) (f : ℝ → ℝ) :
    cfc f X = (hX.eigenvectorUnitary : Matrix ι ι ℂ) * diagonal (fun k => ((f (hX.eigenvalues k) : ℝ) : ℂ)) *
      (hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ := by
  rw [hX.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rfl

lemma uu {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    (hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ * (hX.eigenvectorUnitary : Matrix ι ι ℂ) = 1 :=
  Unitary.coe_star_mul_self _

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem cfc_kron {X : Matrix ι ι ℂ} {Y : Matrix κ κ ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (f : ℝ → ℝ) (hf0 : f 0 = 0) (hmul : ∀ x y, 0 ≤ x → 0 ≤ y → f (x * y) = f x * f y) :
    cfc f (X ⊗ₖ Y) = cfc f X ⊗ₖ cfc f Y := by
  have hXh := hX.isHermitian
  have hYh := hY.isHermitian
  set U := (hXh.eigenvectorUnitary : Matrix ι ι ℂ)
  set V := (hYh.eigenvectorUnitary : Matrix κ κ ℂ)
  set d := hXh.eigenvalues
  set e := hYh.eigenvalues
  have hW : (U ⊗ₖ V)ᴴ * (U ⊗ₖ V) = 1 := by
    rw [conjTranspose_kronecker, ← mul_kronecker_mul, uu hXh, uu hYh, one_kronecker_one]
  have hDE : diagonal (fun k => ((d k : ℝ) : ℂ)) ⊗ₖ diagonal (fun k => ((e k : ℝ) : ℂ)) =
      diagonal (fun p : ι × κ => ((d p.1 * e p.2 : ℝ) : ℂ)) := by
    rw [diagonal_kronecker_diagonal]; congr 1; ext p; simp
  have hXY : X ⊗ₖ Y = (U ⊗ₖ V) * diagonal (fun p : ι × κ => ((d p.1 * e p.2 : ℝ) : ℂ)) * (U ⊗ₖ V)ᴴ := by
    conv_lhs => rw [spec hXh, spec hYh]
    rw [← hDE, conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul]
  have hDh : (diagonal (fun p : ι × κ => ((d p.1 * e p.2 : ℝ) : ℂ))).IsHermitian :=
    isHermitian_diagonal_of_self_adjoint _ (by ext k; simp [Complex.conj_ofReal])
  rw [hXY, x5ai_conj (U ⊗ₖ V) hW _ hDh f hf0, cfc_diag (fun p : ι × κ => d p.1 * e p.2) f,
    cfc_spec hXh, cfc_spec hYh]
  have hd : ∀ k, 0 ≤ d k := hX.eigenvalues_nonneg
  have he : ∀ k, 0 ≤ e k := hY.eigenvalues_nonneg
  have hDE' : diagonal (fun p : ι × κ => ((f (d p.1 * e p.2) : ℝ) : ℂ)) =
      diagonal (fun k => ((f (d k) : ℝ) : ℂ)) ⊗ₖ diagonal (fun k => ((f (e k) : ℝ) : ℂ)) := by
    rw [diagonal_kronecker_diagonal]; congr 1; ext p
    simp [hmul _ _ (hd p.1) (he p.2)]
  rw [hDE', conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul]

end X5AD
end X5mod_AD_Kron

section X5mod_AD_Prod
open Matrix
open scoped ComplexOrder Kronecker

namespace X5AD
set_option linter.unusedSectionVars false
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23

variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- regrouping (A×C)×(B×D) → (A×B)×(C×D) -/
def eR : (A × C) × (B × D) ≃ (A × B) × (C × D) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun y := ((y.1.1, y.2.1), (y.1.2, y.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def Pm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] (e : m ≃ n) : Matrix m n ℂ :=
  fun x y => if e x = y then 1 else 0

lemma Pm_conj {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] (e : m ≃ n) (M : Matrix n n ℂ) :
    Pm e * M * (Pm e)ᴴ = M.submatrix e e := by
  ext x y
  simp [Pm, mul_apply, conjTranspose_apply]

lemma Pm_iso {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (e : m ≃ n) :
    (Pm e)ᴴ * Pm e = 1 := by
  ext k l
  simp only [Pm, mul_apply, conjTranspose_apply, one_apply]
  have : ∀ x, (star (if e x = k then (1 : ℂ) else 0)) * (if e x = l then 1 else 0) =
      if x = e.symm k then (if k = l then 1 else 0) else 0 := by
    intro x
    by_cases hx : x = e.symm k
    · subst hx; simp
    · have : e x ≠ k := fun h => hx (by rw [← h]; simp)
      simp [this, hx]
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]

variable (A B C D) in
noncomputable def PR : Matrix ((A × C) × (B × D)) ((A × B) × (C × D)) ℂ := Pm eR

lemma PR_conj (M : Matrix ((A × B) × (C × D)) ((A × B) × (C × D)) ℂ) :
    PR A B C D * M * (PR A B C D)ᴴ = M.submatrix eR eR := Pm_conj eR M

lemma PR_iso : (PR A B C D)ᴴ * PR A B C D = 1 := Pm_iso eR

lemma iP_eq (rho : Matrix (A × B) (A × B) ℂ) (tau : Matrix (C × D) (C × D) ℂ) :
    independentProduct rho tau = PR A B C D * (rho ⊗ₖ tau) * (PR A B C D)ᴴ := by
  rw [PR_conj]; rfl

lemma iT_eq (sigma : Matrix B B ℂ) (omega : Matrix D D ℂ) :
    identityTensorReference (A := A × C) (sigma ⊗ₖ omega) =
      PR A B C D * (identityTensorReference (A := A) sigma ⊗ₖ identityTensorReference (A := C) omega) *
        (PR A B C D)ᴴ := by
  rw [PR_conj]
  ext ⟨⟨a, c⟩, ⟨b, d⟩⟩ ⟨⟨a', c'⟩, ⟨b', d'⟩⟩
  simp only [identityTensorReference, submatrix_apply, kronecker_apply, one_apply, eR,
    Equiv.coe_fn_mk, Prod.mk.injEq]
  by_cases ha : a = a' <;> by_cases hc : c = c' <;> simp [ha, hc]

/-- the trace functional behind finiteAlpha -/
noncomputable def Tr {I : Type*} [Fintype I] [DecidableEq I] (R N : Matrix I I ℂ) (t : ℝ) : ℂ :=
  (cfc (fun x : ℝ => x ^ t) R * cfc (fun x : ℝ => if x = 0 then 0 else x ^ (1 - t)) N).trace

lemma f_mul (t : ℝ) : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → (x * y) ^ t = x ^ t * y ^ t :=
  fun x y hx hy => Real.mul_rpow hx hy

lemma g_mul (t : ℝ) : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
    (fun x : ℝ => if x = 0 then 0 else x ^ (1 - t)) (x * y) =
      (fun x : ℝ => if x = 0 then 0 else x ^ (1 - t)) x * (fun x : ℝ => if x = 0 then 0 else x ^ (1 - t)) y := by
  intro x y hx hy
  by_cases h0 : x = 0
  · simp [h0]
  by_cases h1 : y = 0
  · simp [h1]
  simp [h0, h1, Real.mul_rpow hx hy]

lemma Tr_conj {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (e : m ≃ n)
    (K1 K2 : Matrix n n ℂ) (h1 : K1.IsHermitian) (h2 : K2.IsHermitian) (t : ℝ) (ht : 0 < t) :
    Tr (Pm e * K1 * (Pm e)ᴴ) (Pm e * K2 * (Pm e)ᴴ) t = Tr K1 K2 t := by
  unfold Tr
  rw [x5ai_conj (Pm e) (Pm_iso e) K1 h1 _ (Real.zero_rpow ht.ne' : (0:ℝ) ^ t = 0),
    x5ai_conj (Pm e) (Pm_iso e) K2 h2 _ (by simp)]
  have : Pm e * cfc (fun x : ℝ => x ^ t) K1 * (Pm e)ᴴ *
      (Pm e * cfc (fun x : ℝ => if x = 0 then 0 else x ^ (1 - t)) K2 * (Pm e)ᴴ) =
      Pm e * (cfc (fun x : ℝ => x ^ t) K1 * cfc (fun x : ℝ => if x = 0 then 0 else x ^ (1 - t)) K2) *
        (Pm e)ᴴ := by
    simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc (Pm e)ᴴ (Pm e), Pm_iso, Matrix.one_mul]
  rw [this, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Pm_iso, Matrix.mul_one]

lemma Tr_kron {X1 Y1 : Matrix (A × B) (A × B) ℂ} {X2 Y2 : Matrix (C × D) (C × D) ℂ}
    (hX1 : X1.PosSemidef) (hY1 : Y1.PosSemidef) (hX2 : X2.PosSemidef) (hY2 : Y2.PosSemidef)
    (t : ℝ) (ht : 0 < t) :
    Tr (X1 ⊗ₖ X2) (Y1 ⊗ₖ Y2) t = Tr X1 Y1 t * Tr X2 Y2 t := by
  unfold Tr
  rw [cfc_kron hX1 hX2 _ (Real.zero_rpow ht.ne' : (0:ℝ) ^ t = 0) (f_mul t), cfc_kron hY1 hY2 _ (by simp) (g_mul t),
    ← mul_kronecker_mul, trace_kronecker]

lemma iP_psd {rho : Matrix (A × B) (A × B) ℂ} {tau : Matrix (C × D) (C × D) ℂ}
    (h1 : rho.PosSemidef) (h2 : tau.PosSemidef) : (independentProduct rho tau).PosSemidef := by
  rw [iP_eq]; exact (h1.kronecker h2).mul_mul_conjTranspose_same _

lemma iP_density {rho : Matrix (A × B) (A × B) ℂ} {tau : Matrix (C × D) (C × D) ℂ}
    (h1 : IsDensityMatrix rho) (h2 : IsDensityMatrix tau) : IsDensityMatrix (independentProduct rho tau) := by
  refine ⟨iP_psd h1.1 h2.1, ?_⟩
  rw [iP_eq, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, PR_iso, Matrix.mul_one,
    trace_kronecker, h1.2, h2.2, one_mul]

lemma kron_density {sigma : Matrix B B ℂ} {omega : Matrix D D ℂ}
    (h1 : IsDensityMatrix sigma) (h2 : IsDensityMatrix omega) : IsDensityMatrix (sigma ⊗ₖ omega) :=
  ⟨h1.1.kronecker h2.1, by rw [trace_kronecker, h1.2, h2.2, one_mul]⟩

end X5AD
end X5mod_AD_Prod

section X5mod_OL_Main
open Matrix Filter
open scoped ComplexOrder Topology

namespace X5OL

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- the scalar function behind tr(ρ^α N^{1-α}) -/
noncomputable def Φ (ν μ : I → ℝ) (W : I → I → ℝ) (α : ℝ) : ℝ :=
  ∑ i, ∑ j, if 0 < ν i ∧ 0 < μ j then W i j * Real.exp (α * Real.log (ν i) + (1 - α) * Real.log (μ j)) else 0

noncomputable def Φ' (ν μ : I → ℝ) (W : I → I → ℝ) : ℝ :=
  ∑ i, ∑ j, if 0 < ν i ∧ 0 < μ j then W i j * ν i * (Real.log (ν i) - Real.log (μ j)) else 0

lemma Φ_deriv (ν μ : I → ℝ) (W : I → I → ℝ) : HasDerivAt (Φ ν μ W) (Φ' ν μ W) 1 := by
  unfold Φ Φ'
  refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
  split_ifs with h
  · have h1 : HasDerivAt (fun α : ℝ => α * Real.log (ν i) + (1 - α) * Real.log (μ j))
        (Real.log (ν i) - Real.log (μ j)) 1 := by
      have := ((hasDerivAt_id (1 : ℝ)).mul_const (Real.log (ν i))).add
        (((hasDerivAt_const (1 : ℝ) (1 : ℝ)).sub (hasDerivAt_id (1 : ℝ))).mul_const (Real.log (μ j)))
      exact this.congr_deriv (by ring)
    have h2 := (h1.exp).const_mul (W i j)
    refine h2.congr_deriv ?_
    simp only [one_mul, sub_self, zero_mul, add_zero, Real.exp_log h.1]
    ring
  · exact hasDerivAt_const _ _

lemma Φ_cont (ν μ : I → ℝ) (W : I → I → ℝ) : Continuous (Φ ν μ W) := by
  unfold Φ
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  split_ifs
  · fun_prop
  · exact continuous_const

lemma Φ_one (ν μ : I → ℝ) (W : I → I → ℝ) :
    Φ ν μ W 1 = ∑ i, ∑ j, if 0 < ν i ∧ 0 < μ j then W i j * ν i else 0 := by
  unfold Φ
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · simp [Real.exp_log h.1]
  · rfl

lemma tr_alpha {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian)
    (hR0 : ∀ i, 0 ≤ hR.eigenvalues i) (hN0 : ∀ j, 0 ≤ hN.eigenvalues j) (α : ℝ) (hα : 0 < α) :
    (cfc (fun x : ℝ => x ^ α) R * cfc (fun x : ℝ => if x = 0 then 0 else x ^ (1 - α)) N).trace.re =
      Φ hR.eigenvalues hN.eigenvalues (w hR hN) α := by
  rw [tr_cfc_cfc hR hN, Complex.re_sum]
  unfold Φ
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.ofReal_re]
  rcases (hR0 i).lt_or_eq with hi | hi
  · rcases (hN0 j).lt_or_eq with hj | hj
    · rw [if_neg hj.ne', if_pos ⟨hi, hj⟩, Real.rpow_def_of_pos hi, Real.rpow_def_of_pos hj, ← Real.exp_add]
      ring_nf
    · rw [← hj]; simp
  · rw [← hi]; simp [Real.zero_rpow hα.ne']

section scalar
variable (ν μ : I → ℝ) (W : I → I → ℝ) (hν : ∀ i, 0 ≤ ν i) (hμ : ∀ j, 0 ≤ μ j)
  (hW : ∀ i j, 0 ≤ W i j) (hrow : ∀ i, ∑ j, W i j = 1)
include hν hμ hrow

lemma Φ_one_supp (hs : ∀ i j, ν i ≠ 0 → μ j = 0 → W i j = 0) : Φ ν μ W 1 = ∑ i, ν i := by
  rw [Φ_one]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine (Finset.sum_congr rfl fun j _ => ?_).trans
    (show ∑ j, ν i * W i j = ν i by rw [← Finset.mul_sum, hrow, mul_one])
  rcases (hν i).lt_or_eq with hi | hi
  · rcases (hμ j).lt_or_eq with hj | hj
    · rw [if_pos ⟨hi, hj⟩]; ring
    · rw [if_neg (fun h => h.2.ne hj), hs i j hi.ne' hj.symm, mul_zero]
  · rw [if_neg (fun h => h.1.ne hi), ← hi, zero_mul]

lemma value_supp (hs : ∀ i j, ν i ≠ 0 → μ j = 0 → W i j = 0) :
    (∑ i, ∑ j, ν i * Real.logb 2 (μ j) * W i j) + -∑ i, ν i * Real.logb 2 (ν i) =
      -Φ' ν μ W / Real.log 2 := by
  unfold Φ'
  rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show ν i * Real.logb 2 (ν i) = ∑ j, ν i * Real.logb 2 (ν i) * W i j by
      rw [← Finset.mul_sum, hrow, mul_one]]
  rw [Finset.sum_div, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases (hν i).lt_or_eq with hi | hi
  · rcases (hμ j).lt_or_eq with hj | hj
    · rw [if_pos ⟨hi, hj⟩]; unfold Real.logb; ring
    · rw [if_neg (fun h => h.2.ne hj), hs i j hi.ne' hj.symm]; simp
  · rw [if_neg (fun h => h.1.ne hi), ← hi]; simp

include hW in
lemma Φ_one_lt (hex : ∃ i j, ν i ≠ 0 ∧ μ j = 0 ∧ W i j ≠ 0) : Φ ν μ W 1 < ∑ i, ν i := by
  obtain ⟨i0, j0, hi0, hj0, hw0⟩ := hex
  rw [Φ_one]
  have hle : ∀ i j, (if 0 < ν i ∧ 0 < μ j then W i j * ν i else 0) ≤ W i j * ν i := by
    intro i j; split_ifs
    · exact le_rfl
    · exact mul_nonneg (hW i j) (hν i)
  refine Finset.sum_lt_sum (fun i _ => ?_) ⟨i0, Finset.mem_univ _, ?_⟩
  · calc _ ≤ ∑ j, W i j * ν i := Finset.sum_le_sum fun j _ => hle i j
      _ = ν i := by rw [← Finset.sum_mul, hrow, one_mul]
  · calc _ < ∑ j, W i0 j * ν i0 := by
          refine Finset.sum_lt_sum (fun j _ => hle i0 j) ⟨j0, Finset.mem_univ _, ?_⟩
          rw [if_neg (fun h => h.2.ne' hj0)]
          exact mul_pos ((hW i0 j0).lt_of_ne (Ne.symm hw0)) ((hν i0).lt_of_ne (Ne.symm hi0))
      _ = ν i0 := by rw [← Finset.sum_mul, hrow, one_mul]

omit hrow in
include hW in
lemma Φ_zero (h0 : Φ ν μ W 1 = 0) (α : ℝ) : Φ ν μ W α = 0 := by
  rw [Φ_one] at h0
  have hnn : ∀ i j, 0 ≤ (if 0 < ν i ∧ 0 < μ j then W i j * ν i else 0) := by
    intro i j; split_ifs
    · exact mul_nonneg (hW i j) (hν i)
    · exact le_rfl
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ => hnn i j)).1 h0
  unfold Φ
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn i j)).1 (h1 i (Finset.mem_univ _)) j
    (Finset.mem_univ _)
  split_ifs at h2 ⊢ with h
  · rcases mul_eq_zero.1 h2 with h3 | h3
    · rw [h3, zero_mul]
    · exact absurd h3 h.1.ne'
  · rfl

end scalar

end X5OL
end X5mod_OL_Main

section X5mod_AM_Conv
open Matrix Filter Set
open scoped Topology

namespace X5OL

variable {I : Type*} [Fintype I] [DecidableEq I]
set_option linter.unusedSectionVars false

section conv
variable (ν μ : I → ℝ) (W : I → I → ℝ) (hW : ∀ i j, 0 ≤ W i j)
include hW

lemma Φ_nonneg_term (t : ℝ) (i j : I) :
    0 ≤ (if 0 < ν i ∧ 0 < μ j then W i j * Real.exp (t * Real.log (ν i) + (1 - t) * Real.log (μ j)) else 0) := by
  split_ifs
  · exact mul_nonneg (hW i j) (Real.exp_pos _).le
  · exact le_rfl

lemma Φ_pos (h1 : 0 < Φ ν μ W 1) (t : ℝ) : 0 < Φ ν μ W t := by
  unfold Φ at h1 ⊢
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1.ne'
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
  have hc : 0 < ν i ∧ 0 < μ j := by by_contra h; exact hj (if_neg h)
  have hw : W i j ≠ 0 := by intro h; apply hj; rw [if_pos hc, h, zero_mul]
  have hterm : 0 < (if 0 < ν i ∧ 0 < μ j then
      W i j * Real.exp (t * Real.log (ν i) + (1 - t) * Real.log (μ j)) else 0) := by
    rw [if_pos hc]; exact mul_pos ((hW i j).lt_of_ne (Ne.symm hw)) (Real.exp_pos _)
  refine lt_of_lt_of_le hterm ?_
  refine le_trans ?_ (Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ =>
    Φ_nonneg_term ν μ W hW t i j) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j => if 0 < ν i ∧ 0 < μ j then
      W i j * Real.exp (t * Real.log (ν i) + (1 - t) * Real.log (μ j)) else 0)
    (fun j _ => Φ_nonneg_term ν μ W hW t i j) (Finset.mem_univ j)

lemma Φ_holder (x y a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hX : 0 < Φ ν μ W x) (hY : 0 < Φ ν μ W y) :
    Φ ν μ W (a * x + b * y) ≤ Real.exp (a * Real.log (Φ ν μ W x) + b * Real.log (Φ ν μ W y)) := by
  set X := Φ ν μ W x
  set Y := Φ ν μ W y
  set E := Real.exp (a * Real.log X + b * Real.log Y)
  have key : ∀ i j, (if 0 < ν i ∧ 0 < μ j then
        W i j * Real.exp ((a * x + b * y) * Real.log (ν i) + (1 - (a * x + b * y)) * Real.log (μ j)) else 0) ≤
      E * (a * (if 0 < ν i ∧ 0 < μ j then
        W i j * Real.exp (x * Real.log (ν i) + (1 - x) * Real.log (μ j)) else 0) / X +
        b * (if 0 < ν i ∧ 0 < μ j then
        W i j * Real.exp (y * Real.log (ν i) + (1 - y) * Real.log (μ j)) else 0) / Y) := by
    intro i j
    split_ifs with hc
    · set ex := x * Real.log (ν i) + (1 - x) * Real.log (μ j)
      set ey := y * Real.log (ν i) + (1 - y) * Real.log (μ j)
      have he : (a * x + b * y) * Real.log (ν i) + (1 - (a * x + b * y)) * Real.log (μ j) =
          (a * Real.log X + b * Real.log Y) + (a * (ex - Real.log X) + b * (ey - Real.log Y)) := by
        simp only [ex, ey]
        have : b = 1 - a := by linarith
        subst this; ring
      have hcv := convexOn_exp.2 (mem_univ (ex - Real.log X)) (mem_univ (ey - Real.log Y)) ha hb hab
      simp only [smul_eq_mul] at hcv
      rw [Real.exp_sub, Real.exp_sub, Real.exp_log hX, Real.exp_log hY] at hcv
      rw [he, Real.exp_add]
      calc W i j * (E * Real.exp (a * (ex - Real.log X) + b * (ey - Real.log Y)))
          ≤ W i j * (E * (a * (Real.exp ex / X) + b * (Real.exp ey / Y))) := by
            gcongr
            exact hW i j
        _ = _ := by field_simp
    · simp
  calc Φ ν μ W (a * x + b * y) ≤ ∑ i, ∑ j, E * (a * (if 0 < ν i ∧ 0 < μ j then
        W i j * Real.exp (x * Real.log (ν i) + (1 - x) * Real.log (μ j)) else 0) / X +
        b * (if 0 < ν i ∧ 0 < μ j then
        W i j * Real.exp (y * Real.log (ν i) + (1 - y) * Real.log (μ j)) else 0) / Y) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j
    _ = E * (a * X / X + b * Y / Y) := by
        simp only [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_div]
        rfl
    _ = E := by rw [mul_div_assoc, mul_div_assoc, div_self hX.ne', div_self hY.ne', mul_one, mul_one, hab,
          mul_one]

lemma L_convex (h1 : 0 < Φ ν μ W 1) : ConvexOn ℝ univ (fun t => Real.log (Φ ν μ W t)) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have hX := Φ_pos ν μ W hW h1 x
  have hY := Φ_pos ν μ W hW h1 y
  have := Φ_holder ν μ W hW x y a b ha hb hab hX hY
  calc Real.log (Φ ν μ W (a * x + b * y))
      ≤ Real.log (Real.exp (a * Real.log (Φ ν μ W x) + b * Real.log (Φ ν μ W y))) :=
        Real.log_le_log (Φ_pos ν μ W hW h1 _) this
    _ = _ := Real.log_exp _

end conv

end X5OL
end X5mod_AM_Conv

section X5mod_OL_Thm
open Matrix Filter Set
open scoped ComplexOrder Topology

namespace X5OL
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23

attribute [local instance] Classical.propDecidable

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

lemma N_psd (sigma : Matrix B B ℂ) (hs : sigma.PosSemidef) :
    (identityTensorReference (A := A) sigma).PosSemidef := by
  unfold identityTensorReference Matrix.kronecker
  exact Matrix.PosSemidef.kronecker Matrix.PosSemidef.one hs

/-- real limit in the supported case -/
lemma real_limit {I : Type*} [Fintype I] [DecidableEq I] (ν μ : I → ℝ) (W : I → I → ℝ) (h1 : Φ ν μ W 1 = 1) :
    Tendsto (fun t => 1 / (1 - t) * Real.logb 2 (Φ ν μ W t)) (𝓝[{t : ℝ | 0 < t ∧ t ≠ 1}] 1)
      (𝓝 (-Φ' ν μ W / Real.log 2)) := by
  set ψ := fun t => Real.log (Φ ν μ W t) / Real.log 2
  have hψ : HasDerivAt ψ (Φ' ν μ W / Φ ν μ W 1 / Real.log 2) 1 :=
    ((Φ_deriv ν μ W).log (by rw [h1]; norm_num)).div_const _
  rw [h1, div_one] at hψ
  have hs := (hasDerivAt_iff_tendsto_slope.1 hψ).neg
  have hmono : 𝓝[{t : ℝ | 0 < t ∧ t ≠ 1}] (1 : ℝ) ≤ 𝓝[{(1 : ℝ)}ᶜ] 1 :=
    nhdsWithin_mono _ fun t ht => ht.2
  rw [neg_div]
  refine (hs.mono_left hmono).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht1 : t - 1 ≠ 0 := sub_ne_zero.2 ht.2
  have hψ1 : ψ 1 = 0 := by simp [ψ, h1]
  rw [slope_def_field, hψ1, sub_zero]
  simp only [ψ, Real.logb]
  field_simp
  have : (1 - t) = -(t - 1) := by ring
  rw [this]; field_simp

lemma real_atBot {I : Type*} [Fintype I] [DecidableEq I] (ν μ : I → ℝ) (W : I → I → ℝ)
    (h0 : 0 < Φ ν μ W 1) (h1 : Φ ν μ W 1 < 1) :
    Tendsto (fun t => 1 / (1 - t) * Real.logb 2 (Φ ν μ W t)) (𝓝[Ioo 0 1] 1) atBot := by
  have hC : Real.logb 2 (Φ ν μ W 1) < 0 := Real.logb_neg (by norm_num) h0 h1
  have hg : Tendsto (fun t => Real.logb 2 (Φ ν μ W t)) (𝓝[Ioo 0 1] 1) (𝓝 (Real.logb 2 (Φ ν μ W 1))) := by
    have : ContinuousAt (fun t => Real.log (Φ ν μ W t) / Real.log 2) 1 :=
      ((Φ_cont ν μ W).continuousAt.log h0.ne').div_const _
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  have hsub : Tendsto (fun t : ℝ => 1 - t) (𝓝[Ioo 0 1] 1) (𝓝[Ioi 0] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have : Tendsto (fun t : ℝ => 1 - t) (𝓝 1) (𝓝 (1 - 1)) := (continuous_const.sub continuous_id).tendsto 1
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact sub_pos.2 ht.2
  have hf : Tendsto (fun t : ℝ => 1 / (1 - t)) (𝓝[Ioo 0 1] 1) atTop := by
    simp only [one_div]
    exact tendsto_inv_nhdsGT_zero.comp hsub
  exact hf.atTop_mul_neg hC hg

theorem main [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    Tendsto (finiteAlpha rho sigma)
      (nhdsWithin 1 {t : ℝ | 0 < t ∧ t ≠ 1}) (nhds (fixedVonNeumann rho sigma)) ∧
      alphaEntropy rho sigma 1 = fixedVonNeumann rho sigma := by
  refine ⟨?_, by simp [alphaEntropy, finiteAlpha]⟩
  set N := identityTensorReference (A := A) sigma with hNdef
  have hNpsd : N.PosSemidef := N_psd sigma hsigma.1
  have hR := hrho.1.isHermitian
  have hN := hNpsd.isHermitian
  set ν := hR.eigenvalues
  set μ := hN.eigenvalues
  set W := w hR hN
  have hν : ∀ i, 0 ≤ ν i := hrho.1.eigenvalues_nonneg
  have hμ : ∀ j, 0 ≤ μ j := hNpsd.eigenvalues_nonneg
  have hW : ∀ i j, 0 ≤ W i j := w_nonneg hR hN
  have hrow : ∀ i, ∑ j, W i j = 1 := w_row hR hN
  -- traces as sums
  have hcfc1 : cfc (fun _ : ℝ => (1 : ℝ)) N = 1 := cfc_const_one ℝ N hN.isSelfAdjoint
  have hsingle : ∀ f : ℝ → ℝ, (cfc f rho).trace.re = ∑ i, f (ν i) := by
    intro f
    have := tr_cfc_cfc hR hN f (fun _ => 1)
    rw [hcfc1, Matrix.mul_one] at this
    rw [this, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_sum]
    simp only [Complex.ofReal_re, mul_one]
    rw [← Finset.mul_sum, hrow, mul_one]
  have htr : ∑ i, ν i = 1 := by
    have := hsingle (fun x => x)
    rw [cfc_id' ℝ rho hR.isSelfAdjoint, hrho.2] at this
    simpa using this.symm
  have hF : ∀ t : ℝ, 0 < t →
      (cfc (fun x : ℝ => x ^ t) rho * cfc (fun x : ℝ => if x = 0 then 0 else x ^ (1 - t)) N).trace.re =
        Φ ν μ W t := fun t ht => tr_alpha hR hN hν hμ t ht
  have hFA : ∀ t : ℝ, 0 < t → t ≠ 1 → finiteAlpha rho sigma t =
      if 1 < t ∧ ¬ supportedBy rho N then ⊥
      else (((1 / (1 - t) : ℝ)) : EReal) * log2Extended (Φ ν μ W t) := by
    intro t ht ht1
    unfold finiteAlpha
    rw [if_neg ht1, hF t ht]
  by_cases hS : supportedBy rho N
  · -- supported case
    have hs : ∀ i j, ν i ≠ 0 → μ j = 0 → W i j = 0 := by
      intro i j hi hj
      simp only [W, w, supp_fwd hR hN hS i j hi hj, norm_zero]; norm_num
    have hΦ1 : Φ ν μ W 1 = 1 := by rw [Φ_one_supp ν μ W hν hμ hrow hs, htr]
    have hval : fixedVonNeumann rho sigma = ((-Φ' ν μ W / Real.log 2 : ℝ) : EReal) := by
      unfold fixedVonNeumann
      rw [if_pos hS, ← value_supp ν μ W hν hμ hrow hs]
      congr 2
      · have := tr_cfc_cfc hR hN (fun x => x) (fun x => Real.logb 2 x)
        rw [cfc_id' ℝ rho hR.isSelfAdjoint] at this
        rw [this, Complex.re_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Complex.re_sum]; simp only [Complex.ofReal_re]; rfl
      · unfold QAlgorithms.vnEntropy
        rw [hsingle]
    rw [hval]
    have hpos : ∀ᶠ t in 𝓝 (1 : ℝ), 0 < Φ ν μ W t :=
      (Φ_cont ν μ W).continuousAt.eventually (lt_mem_nhds (by rw [hΦ1]; norm_num))
    refine (EReal.tendsto_coe.2 (real_limit ν μ W hΦ1)).congr' ?_
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds hpos] with t ht hp
    rw [hFA t ht.1 ht.2, if_neg (fun h => h.2 hS)]
    unfold log2Extended
    rw [if_neg hp.ne', ← EReal.coe_mul]
  · -- unsupported case
    have hex : ∃ i j, ν i ≠ 0 ∧ μ j = 0 ∧ W i j ≠ 0 := by
      by_contra hne
      push Not at hne
      apply hS
      refine supp_bwd hR hN fun i j hi hj => ?_
      have := hne i j hi hj
      simp only [W, w] at this
      exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this)
    have hlt : Φ ν μ W 1 < 1 := htr ▸ Φ_one_lt ν μ W hν hμ hW hrow hex
    have hval : fixedVonNeumann rho sigma = ⊥ := by unfold fixedVonNeumann; rw [if_neg hS]
    rw [hval]
    have hset : {t : ℝ | 0 < t ∧ t ≠ 1} = Ioo 0 1 ∪ Ioi 1 := by
      ext t; simp only [mem_ofPred_eq, mem_union, mem_Ioo, mem_Ioi]
      constructor
      · rintro ⟨h0, h1⟩
        rcases lt_or_gt_of_ne h1 with h | h
        · exact Or.inl ⟨h0, h⟩
        · exact Or.inr h
      · rintro (⟨h0, h1⟩ | h)
        · exact ⟨h0, h1.ne⟩
        · exact ⟨by linarith, h.ne'⟩
    rw [hset, nhdsWithin_union]
    refine Tendsto.sup ?_ ?_
    · -- left
      have hΦnn : 0 ≤ Φ ν μ W 1 := by
        rw [Φ_one]
        exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
          split_ifs
          · exact mul_nonneg (hW i j) (hν i)
          · exact le_rfl
      rcases hΦnn.eq_or_lt with h0 | h0
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with t ht
        rw [hFA t ht.1 ht.2.ne, if_neg (fun h => absurd h.1 (not_lt.2 ht.2.le)),
          Φ_zero ν μ W hν hμ hW h0.symm t]
        unfold log2Extended
        rw [if_pos rfl, EReal.coe_mul_bot_of_pos (by have := ht.2; rw [one_div]; exact inv_pos.2 (by linarith))]
      · rw [EReal.tendsto_nhds_bot_iff_real]
        intro x
        have hpos : ∀ᶠ t in 𝓝 (1 : ℝ), 0 < Φ ν μ W t :=
          (Φ_cont ν μ W).continuousAt.eventually (lt_mem_nhds h0)
        filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds hpos,
          (real_atBot ν μ W h0 hlt).eventually (eventually_lt_atBot x)] with t ht hp hlx
        rw [hFA t ht.1 ht.2.ne, if_neg (fun h => absurd h.1 (not_lt.2 ht.2.le))]
        unfold log2Extended
        rw [if_neg hp.ne', ← EReal.coe_mul, EReal.coe_lt_coe_iff]
        exact hlx
    · -- right
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [hFA t (by have := ht; simp only [mem_Ioi] at this; linarith) (ne_of_gt ht), if_pos ⟨ht, hS⟩]

end X5OL
end X5mod_OL_Thm

section X5mod_AM_Thm
open Matrix Filter Set
open scoped ComplexOrder Topology ENNReal

namespace X5OL
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23

attribute [local instance] Classical.propDecidable

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem fa_anti [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    AntitoneOn (finiteAlpha rho sigma) (Ioi 0) := by
  set N := identityTensorReference (A := A) sigma with hNdef
  have hNpsd : N.PosSemidef := N_psd sigma hsigma.1
  have hR := hrho.1.isHermitian
  have hN := hNpsd.isHermitian
  set ν := hR.eigenvalues
  set μ := hN.eigenvalues
  set W := w hR hN
  have hν : ∀ i, 0 ≤ ν i := hrho.1.eigenvalues_nonneg
  have hμ : ∀ j, 0 ≤ μ j := hNpsd.eigenvalues_nonneg
  have hW : ∀ i j, 0 ≤ W i j := w_nonneg hR hN
  have hrow : ∀ i, ∑ j, W i j = 1 := w_row hR hN
  have hcfc1 : cfc (fun _ : ℝ => (1 : ℝ)) N = 1 := cfc_const_one ℝ N hN.isSelfAdjoint
  have hsingle : ∀ f : ℝ → ℝ, (cfc f rho).trace.re = ∑ i, f (ν i) := by
    intro f
    have := tr_cfc_cfc hR hN f (fun _ => 1)
    rw [hcfc1, Matrix.mul_one] at this
    rw [this, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_sum]
    simp only [Complex.ofReal_re, mul_one]
    rw [← Finset.mul_sum, hrow, mul_one]
  have htr : ∑ i, ν i = 1 := by
    have := hsingle (fun x => x)
    rw [cfc_id' ℝ rho hR.isSelfAdjoint, hrho.2] at this
    simpa using this.symm
  have hF : ∀ t : ℝ, 0 < t →
      (cfc (fun x : ℝ => x ^ t) rho * cfc (fun x : ℝ => if x = 0 then 0 else x ^ (1 - t)) N).trace.re =
        Φ ν μ W t := fun t ht => tr_alpha hR hN hν hμ t ht
  have hFA : ∀ t : ℝ, 0 < t → t ≠ 1 → finiteAlpha rho sigma t =
      if 1 < t ∧ ¬ supportedBy rho N then ⊥
      else (((1 / (1 - t) : ℝ)) : EReal) * log2Extended (Φ ν μ W t) := by
    intro t ht ht1
    unfold finiteAlpha
    rw [if_neg ht1, hF t ht]
  have hF1 : finiteAlpha rho sigma 1 = fixedVonNeumann rho sigma := by
    unfold finiteAlpha; rw [if_pos rfl]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hS : supportedBy rho N
  · have hs : ∀ i j, ν i ≠ 0 → μ j = 0 → W i j = 0 := by
      intro i j hi hj
      simp only [W, w, supp_fwd hR hN hS i j hi hj, norm_zero]; norm_num
    have hΦ1 : Φ ν μ W 1 = 1 := by rw [Φ_one_supp ν μ W hν hμ hrow hs, htr]
    have hval : fixedVonNeumann rho sigma = ((-Φ' ν μ W / Real.log 2 : ℝ) : EReal) := by
      unfold fixedVonNeumann
      rw [if_pos hS, ← value_supp ν μ W hν hμ hrow hs]
      congr 2
      · have := tr_cfc_cfc hR hN (fun x => x) (fun x => Real.logb 2 x)
        rw [cfc_id' ℝ rho hR.isSelfAdjoint] at this
        rw [this, Complex.re_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Complex.re_sum]; simp only [Complex.ofReal_re]; rfl
      · unfold QAlgorithms.vnEntropy
        rw [hsingle]
    set L := fun t => Real.log (Φ ν μ W t) with hLdef
    have hconv := L_convex ν μ W hW (by rw [hΦ1]; norm_num)
    have hL : HasDerivAt L (Φ' ν μ W) 1 := by
      have := (Φ_deriv ν μ W).log (by rw [hΦ1]; norm_num)
      rwa [hΦ1, div_one] at this
    have hL1 : L 1 = 0 := by simp [hLdef, hΦ1]
    set h : ℝ → ℝ := fun t => if t = 1 then Φ' ν μ W else slope L 1 t with hhdef
    have hg : ∀ t, 0 < t → finiteAlpha rho sigma t = ((-(h t) / Real.log 2 : ℝ) : EReal) := by
      intro t ht
      by_cases ht1 : t = 1
      · subst ht1; rw [hF1, hval]; simp [hhdef]
      · rw [hFA t ht ht1, if_neg (fun h => h.2 hS)]
        have hp := Φ_pos ν μ W hW (by rw [hΦ1]; norm_num) t
        unfold log2Extended
        rw [if_neg hp.ne', ← EReal.coe_mul]
        congr 1
        simp only [hhdef, if_neg ht1, slope_def_field, sub_zero, hLdef, Real.logb, hΦ1, Real.log_one]
        have : t - 1 ≠ 0 := sub_ne_zero.2 ht1
        have : 1 - t ≠ 0 := fun h' => this (by linarith)
        field_simp
        ring
    have hmono : Monotone h := by
      intro s t hst
      rcases hst.lt_or_eq with hst | rfl
      · simp only [hhdef]
        by_cases hs1 : s = 1
        · subst hs1
          rw [if_pos rfl, if_neg hst.ne']
          exact hconv.le_slope_of_hasDerivAt (mem_univ _) (mem_univ _) hst hL
        · by_cases ht1 : t = 1
          · subst ht1
            rw [if_neg hs1, if_pos rfl, slope_comm]
            exact hconv.slope_le_of_hasDerivAt (mem_univ _) (mem_univ _) hst hL
          · rw [if_neg hs1, if_neg ht1]
            exact hconv.slope_mono (mem_univ _) ⟨mem_univ _, hs1⟩ ⟨mem_univ _, ht1⟩ hst.le
      · exact le_rfl
    intro s hs t ht hst
    rw [hg s hs, hg t ht, EReal.coe_le_coe_iff]
    have := hmono hst
    rw [div_le_div_iff_of_pos_right hl2]
    linarith
  · have hval : fixedVonNeumann rho sigma = ⊥ := by unfold fixedVonNeumann; rw [if_neg hS]
    have hex : ∃ i j, ν i ≠ 0 ∧ μ j = 0 ∧ W i j ≠ 0 := by
      by_contra hne
      push Not at hne
      apply hS
      refine supp_bwd hR hN fun i j hi hj => ?_
      have := hne i j hi hj
      simp only [W, w] at this
      exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this)
    have hlt : Φ ν μ W 1 < 1 := htr ▸ Φ_one_lt ν μ W hν hμ hW hrow hex
    have hbot : ∀ t, 1 ≤ t → finiteAlpha rho sigma t = ⊥ := by
      intro t ht
      rcases ht.lt_or_eq with ht | rfl
      · rw [hFA t (by linarith) ht.ne', if_pos ⟨ht, hS⟩]
      · rw [hF1, hval]
    have hΦnn : 0 ≤ Φ ν μ W 1 := by
      rw [Φ_one]
      exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
        split_ifs
        · exact mul_nonneg (hW i j) (hν i)
        · exact le_rfl
    intro s hs t ht hst
    by_cases ht1 : 1 ≤ t
    · rw [hbot t ht1]; exact bot_le
    push Not at ht1
    have hs1 : s < 1 := lt_of_le_of_lt hst ht1
    have hs0 : (0 : ℝ) < s := hs
    have ht0 : (0 : ℝ) < t := ht
    rw [hFA t ht0 ht1.ne, hFA s hs0 hs1.ne, if_neg (fun h => absurd h.1 (not_lt.2 ht1.le)),
      if_neg (fun h => absurd h.1 (not_lt.2 hs1.le))]
    rcases hΦnn.eq_or_lt with h0 | h0
    · rw [Φ_zero ν μ W hν hμ hW h0.symm t]
      unfold log2Extended
      rw [if_pos rfl, EReal.coe_mul_bot_of_pos (by rw [one_div]; exact inv_pos.2 (by linarith))]
      exact bot_le
    · have hpt := Φ_pos ν μ W hW h0 t
      have hps := Φ_pos ν μ W hW h0 s
      unfold log2Extended
      rw [if_neg hpt.ne', if_neg hps.ne', ← EReal.coe_mul, ← EReal.coe_mul, EReal.coe_le_coe_iff]
      have hconv := L_convex ν μ W hW h0
      have hL1 : Real.log (Φ ν μ W 1) < 0 := Real.log_neg h0 hlt
      set θ := (1 - t) / (1 - s)
      have h1s : 0 < 1 - s := by linarith
      have h1t : 0 < 1 - t := by linarith
      have hθ0 : 0 ≤ θ := div_nonneg h1t.le h1s.le
      have hθ1 : 0 ≤ 1 - θ := by
        simp only [θ]; rw [sub_nonneg, div_le_one h1s]; linarith
      have hc := hconv.2 (mem_univ s) (mem_univ 1) hθ0 hθ1 (by ring)
      simp only [smul_eq_mul, mul_one] at hc
      have ht' : θ * s + (1 - θ) = t := by simp only [θ]; field_simp; ring
      rw [ht'] at hc
      have hc2 : Real.log (Φ ν μ W t) ≤ θ * Real.log (Φ ν μ W s) := by
        have := mul_nonpos_of_nonneg_of_nonpos hθ1 hL1.le
        linarith
      unfold Real.logb
      have hθs : θ * (1 - s) = 1 - t := by simp only [θ]; field_simp
      have k : Real.log (Φ ν μ W t) * (1 - s) ≤ Real.log (Φ ν μ W s) * (1 - t) := by
        rw [← hθs]
        have := mul_le_mul_of_nonneg_right hc2 h1s.le
        linarith
      have e1 : ∀ (x y : ℝ), 1 / x * (y / Real.log 2) = (y / x) / Real.log 2 := fun x y => by ring
      rw [e1, e1]
      refine div_le_div_of_nonneg_right ?_ hl2.le
      rw [div_le_div_iff₀ h1t h1s]
      linarith

end X5OL

namespace X5OL
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23

attribute [local instance] Classical.propDecidable

theorem am_main {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    Antitone (alphaEntropy rho sigma) := by
  have hg := fa_anti rho sigma hrho hsigma
  have hsup : ∀ t : ℝ, 0 < t → finiteAlpha rho sigma t ≤ alphaEntropy rho sigma 0 := by
    intro t ht
    unfold alphaEntropy; rw [if_pos rfl]
    exact le_sSup ⟨t, ht, rfl⟩
  have hinf : ∀ t : ℝ, 0 < t → alphaEntropy rho sigma ⊤ ≤ finiteAlpha rho sigma t := by
    intro t ht
    unfold alphaEntropy; rw [if_neg ENNReal.top_ne_zero, if_pos rfl]
    exact sInf_le ⟨t, ht, rfl⟩
  have hfin : ∀ a : ℝ≥0∞, a ≠ 0 → a ≠ ⊤ →
      alphaEntropy rho sigma a = finiteAlpha rho sigma a.toReal ∧ 0 < a.toReal := by
    intro a h0 hT
    refine ⟨?_, ENNReal.toReal_pos h0 hT⟩
    unfold alphaEntropy; rw [if_neg h0, if_neg hT]
  intro a b hab
  by_cases ha0 : a = 0
  · subst ha0
    by_cases hb0 : b = 0
    · subst hb0; exact le_rfl
    by_cases hbT : b = ⊤
    · subst hbT; exact (hinf 1 one_pos).trans (hsup 1 one_pos)
    obtain ⟨e, hp⟩ := hfin b hb0 hbT
    rw [e]; exact hsup _ hp
  by_cases haT : a = ⊤
  · subst haT; rw [top_le_iff.1 hab]
  obtain ⟨ea, hpa⟩ := hfin a ha0 haT
  have hb0 : b ≠ 0 := fun h => ha0 (le_antisymm (h ▸ hab) bot_le)
  by_cases hbT : b = ⊤
  · subst hbT; rw [ea]; exact hinf _ hpa
  obtain ⟨eb, hpb⟩ := hfin b hb0 hbT
  rw [ea, eb]
  exact hg hpa hpb (ENNReal.toReal_mono hbT hab)

end X5OL
end X5mod_AM_Thm

section X5mod_AD_Fin
open Matrix Filter Set
open scoped ComplexOrder Kronecker Topology

namespace X5AD
set_option linter.unusedSectionVars false
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23 X5OL

attribute [local instance] Classical.propDecidable

section single
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- spectral facts for one pair -/
theorem pack (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    (∀ t, Tr rho (identityTensorReference (A := A) sigma) t =
        (((Tr rho (identityTensorReference (A := A) sigma) t).re : ℝ) : ℂ)) ∧
    (∀ t, 0 < t → 0 ≤ (Tr rho (identityTensorReference (A := A) sigma) t).re) ∧
    (supportedBy rho (identityTensorReference (A := A) sigma) ↔
      (Tr rho (identityTensorReference (A := A) sigma) 1).re = 1) ∧
    (Tr rho (identityTensorReference (A := A) sigma) 1).re ≤ 1 ∧
    (supportedBy rho (identityTensorReference (A := A) sigma) →
      ∀ t, 0 < t → 0 < (Tr rho (identityTensorReference (A := A) sigma) t).re) := by
  set N := identityTensorReference (A := A) sigma with hNdef
  have hNpsd : N.PosSemidef := N_psd sigma hsigma.1
  have hR := hrho.1.isHermitian
  have hN := hNpsd.isHermitian
  set ν := hR.eigenvalues
  set μ := hN.eigenvalues
  set W := w hR hN
  have hν : ∀ i, 0 ≤ ν i := hrho.1.eigenvalues_nonneg
  have hμ : ∀ j, 0 ≤ μ j := hNpsd.eigenvalues_nonneg
  have hW : ∀ i j, 0 ≤ W i j := w_nonneg hR hN
  have hrow : ∀ i, ∑ j, W i j = 1 := w_row hR hN
  have hcfc1 : cfc (fun _ : ℝ => (1 : ℝ)) N = 1 := cfc_const_one ℝ N hN.isSelfAdjoint
  have hsingle : ∀ f : ℝ → ℝ, (cfc f rho).trace.re = ∑ i, f (ν i) := by
    intro f
    have := tr_cfc_cfc hR hN f (fun _ => 1)
    rw [hcfc1, Matrix.mul_one] at this
    rw [this, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_sum]
    simp only [Complex.ofReal_re, mul_one]
    rw [← Finset.mul_sum, hrow, mul_one]
  have htr : ∑ i, ν i = 1 := by
    have := hsingle (fun x => x)
    rw [cfc_id' ℝ rho hR.isSelfAdjoint, hrho.2] at this
    simpa using this.symm
  have hT : ∀ t, 0 < t → (Tr rho N t).re = Φ ν μ W t := fun t ht => tr_alpha hR hN hν hμ t ht
  have hΦnn : ∀ t, 0 ≤ Φ ν μ W t := fun t =>
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Φ_nonneg_term ν μ W hW t i j
  have hsupp : supportedBy rho N ↔ Φ ν μ W 1 = 1 := by
    constructor
    · intro hS
      have hs : ∀ i j, ν i ≠ 0 → μ j = 0 → W i j = 0 := by
        intro i j hi hj
        simp only [W, w, supp_fwd hR hN hS i j hi hj, norm_zero]; norm_num
      rw [Φ_one_supp ν μ W hν hμ hrow hs, htr]
    · intro h1
      by_contra hS
      have hex : ∃ i j, ν i ≠ 0 ∧ μ j = 0 ∧ W i j ≠ 0 := by
        by_contra hne
        push Not at hne
        apply hS
        refine supp_bwd hR hN fun i j hi hj => ?_
        have := hne i j hi hj
        simp only [W, w] at this
        exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this)
      have := Φ_one_lt ν μ W hν hμ hW hrow hex
      rw [htr] at this; linarith
  have hle1 : Φ ν μ W 1 ≤ 1 := by
    by_cases hS : supportedBy rho N
    · exact (hsupp.1 hS).le
    · have hex : ∃ i j, ν i ≠ 0 ∧ μ j = 0 ∧ W i j ≠ 0 := by
        by_contra hne
        push Not at hne
        apply hS
        refine supp_bwd hR hN fun i j hi hj => ?_
        have := hne i j hi hj
        simp only [W, w] at this
        exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this)
      have := Φ_one_lt ν μ W hν hμ hW hrow hex
      rw [htr] at this; linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t
    unfold Tr
    rw [tr_cfc_cfc hR hN]
    simp only [← Complex.ofReal_sum, Complex.ofReal_re]
  · intro t ht; rw [hT t ht]; exact hΦnn t
  · rw [hT 1 one_pos]; exact hsupp
  · rw [hT 1 one_pos]; exact hle1
  · intro hS t ht
    rw [hT t ht]
    exact Φ_pos ν μ W hW (by rw [hsupp.1 hS]; norm_num) t

end single

lemma L_mul {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    log2Extended (x * y) = log2Extended x + log2Extended y := by
  unfold log2Extended
  by_cases h0 : x = 0
  · simp [h0]
  by_cases h1 : y = 0
  · simp [h1]
  rw [if_neg (mul_ne_zero h0 h1), if_neg h0, if_neg h1, Real.logb_mul h0 h1, EReal.coe_add]

lemma L_ne_top (x : ℝ) : log2Extended x ≠ ⊤ := by
  unfold log2Extended; split_ifs <;> simp

lemma emul_add (c : ℝ) (u v : EReal) (hu : u ≠ ⊤) (hv : v ≠ ⊤) :
    (c : EReal) * (u + v) = c * u + c * v := by
  induction u using EReal.rec with
  | top => exact absurd rfl hu
  | bot =>
    induction v using EReal.rec with
    | top => exact absurd rfl hv
    | bot =>
      rcases lt_trichotomy c 0 with h | rfl | h
      · simp [EReal.coe_mul_bot_of_neg h]
      · simp
      · simp [EReal.coe_mul_bot_of_pos h]
    | coe s =>
      rcases lt_trichotomy c 0 with h | rfl | h
      · simp [EReal.coe_mul_bot_of_neg h, ← EReal.coe_mul]
      · simp
      · simp [EReal.coe_mul_bot_of_pos h, ← EReal.coe_mul]
  | coe r =>
    induction v using EReal.rec with
    | top => exact absurd rfl hv
    | bot =>
      rcases lt_trichotomy c 0 with h | rfl | h
      · simp [EReal.coe_mul_bot_of_neg h, ← EReal.coe_mul]
      · simp
      · simp [EReal.coe_mul_bot_of_pos h, ← EReal.coe_mul]
    | coe s => rw [← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, mul_add]

end X5AD
end X5mod_AD_Fin

section X5mod_AD_Add
open Matrix Filter Set
open scoped ComplexOrder Kronecker Topology

namespace X5AD
set_option linter.unusedSectionVars false
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23 X5OL

attribute [local instance] Classical.propDecidable

variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

lemma fa_form {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ) (t : ℝ) (ht1 : t ≠ 1) :
    finiteAlpha rho sigma t =
      if 1 < t ∧ ¬ supportedBy rho (identityTensorReference (A := A) sigma) then ⊥
      else ((1 / (1 - t) : ℝ) : EReal) * log2Extended (Tr rho (identityTensorReference (A := A) sigma) t).re := by
  unfold finiteAlpha Tr; rw [if_neg ht1]

lemma fa_ne_top {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) (t : ℝ) (ht : 0 < t) :
    finiteAlpha rho sigma t ≠ ⊤ := by
  obtain ⟨-, -, -, -, h5⟩ := pack rho sigma hrho hsigma
  by_cases ht1 : t = 1
  · subst ht1; unfold finiteAlpha fixedVonNeumann; rw [if_pos rfl]; split_ifs
    · exact EReal.coe_ne_top _
    · simp
  rw [fa_form rho sigma t ht1]
  split_ifs with h
  · simp
  · rcases lt_or_gt_of_ne ht1 with hlt | hgt
    · have hc : (0 : ℝ) < 1 / (1 - t) := by rw [one_div]; exact inv_pos.2 (by linarith)
      unfold log2Extended; split_ifs
      · rw [EReal.coe_mul_bot_of_pos hc]; simp
      · rw [← EReal.coe_mul]; exact EReal.coe_ne_top _
    · have hS : supportedBy rho (identityTensorReference (A := A) sigma) := by
        by_contra hS; exact h ⟨hgt, hS⟩
      unfold log2Extended; rw [if_neg (h5 hS t ht).ne', ← EReal.coe_mul]; exact EReal.coe_ne_top _

lemma Tr_PR (K1 K2 : Matrix ((A × B) × (C × D)) ((A × B) × (C × D)) ℂ)
    (h1 : K1.IsHermitian) (h2 : K2.IsHermitian) (t : ℝ) (ht : 0 < t) :
    Tr (PR A B C D * K1 * (PR A B C D)ᴴ) (PR A B C D * K2 * (PR A B C D)ᴴ) t = Tr K1 K2 t :=
  Tr_conj eR K1 K2 h1 h2 t ht

theorem fa_add [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (tau : Matrix (C × D) (C × D) ℂ) (omega : Matrix D D ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (htau : IsDensityMatrix tau) (homega : IsDensityMatrix omega)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≠ 1) :
    finiteAlpha (independentProduct rho tau) (sigma ⊗ₖ omega) t =
      finiteAlpha rho sigma t + finiteAlpha tau omega t := by
  set R := independentProduct rho tau
  set N1 := identityTensorReference (A := A) sigma
  set N2 := identityTensorReference (A := C) omega
  set NR := identityTensorReference (A := A × C) (sigma ⊗ₖ omega)
  have hR : IsDensityMatrix R := iP_density hrho htau
  have hM : IsDensityMatrix (sigma ⊗ₖ omega) := kron_density hsigma homega
  have hN1 : N1.PosSemidef := N_psd sigma hsigma.1
  have hN2 : N2.PosSemidef := N_psd omega homega.1
  obtain ⟨p1, p2, p3, p4, p5⟩ := pack rho sigma hrho hsigma
  obtain ⟨q1, q2, q3, q4, q5⟩ := pack tau omega htau homega
  obtain ⟨r1, r2, r3, r4, r5⟩ := pack R (sigma ⊗ₖ omega) hR hM
  have hTR : ∀ s, 0 < s → (Tr R NR s).re = (Tr rho N1 s).re * (Tr tau N2 s).re := by
    intro s hs
    have : Tr R NR s = Tr rho N1 s * Tr tau N2 s := by
      simp only [R, NR]
      rw [iP_eq, iT_eq, Tr_PR _ _ (hrho.1.kronecker htau.1).isHermitian
        (hN1.kronecker hN2).isHermitian s hs, Tr_kron hrho.1 hN1 htau.1 hN2 s hs]
    rw [this, p1 s, q1 s, ← Complex.ofReal_mul, Complex.ofReal_re]
    simp only [Complex.ofReal_re]
  have hsuppR : supportedBy R NR ↔ supportedBy rho N1 ∧ supportedBy tau N2 := by
    rw [r3, p3, q3, hTR 1 one_pos]
    have a0 := p2 1 one_pos
    have b0 := q2 1 one_pos
    constructor
    · intro h
      constructor <;> nlinarith
    · rintro ⟨h1, h2⟩; rw [h1, h2, one_mul]
  rw [fa_form R _ t ht1, fa_form rho sigma t ht1, fa_form tau omega t ht1]
  by_cases hbad : 1 < t ∧ ¬ (supportedBy rho N1 ∧ supportedBy tau N2)
  · rw [if_pos ⟨hbad.1, by rw [hsuppR]; exact hbad.2⟩]
    have h1 := fa_ne_top rho sigma hrho hsigma t ht
    have h2 := fa_ne_top tau omega htau homega t ht
    rw [fa_form rho sigma t ht1] at h1
    rw [fa_form tau omega t ht1] at h2
    by_cases hs1 : supportedBy rho N1
    · have hs2 : ¬ supportedBy tau N2 := fun h => hbad.2 ⟨hs1, h⟩
      rw [if_neg (fun h => h.2 hs1), if_pos ⟨hbad.1, hs2⟩, EReal.add_bot]
    · rw [if_pos ⟨hbad.1, hs1⟩, EReal.bot_add]
  · rw [if_neg (by rw [hsuppR]; exact hbad)]
    have c1 : ¬ (1 < t ∧ ¬ supportedBy rho N1) := fun h => hbad ⟨h.1, fun h' => h.2 h'.1⟩
    have c2 : ¬ (1 < t ∧ ¬ supportedBy tau N2) := fun h => hbad ⟨h.1, fun h' => h.2 h'.2⟩
    rw [if_neg c1, if_neg c2, hTR t ht, L_mul (p2 t ht) (q2 t ht), emul_add _ _ _ (L_ne_top _) (L_ne_top _)]

end X5AD
end X5mod_AD_Add

section X5mod_EO_Thm
open Matrix Filter Set
open scoped ComplexOrder Kronecker Topology ENNReal

namespace X5EO
set_option linter.unusedSectionVars false
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23 X5OL X5AD
open QAlgorithms.Papers.Independent.Gap20.P03 (fixedMin)

attribute [local instance] Classical.propDecidable

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

lemma logterm (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ) (hsigma : sigma.IsHermitian) :
    (rho * cfc (fun x : ℝ => Real.logb 2 x) (identityTensorReference (A := A) sigma)).trace.re =
      (traceLeft rho * cfc (Real.logb 2) sigma).trace.re := by
  unfold identityTensorReference
  rw [x5ai_kron A sigma hsigma]
  exact congrArg Complex.re (pt_kron rho _)

lemma vn_eq (P : Matrix B B ℂ) (hP : P.IsHermitian) :
    vnEntropy P = -(P * cfc (Real.logb 2) P).trace.re := by
  unfold vnEntropy
  congr 3
  conv_rhs => arg 1; rw [← cfc_id' ℝ P hP.isSelfAdjoint]
  rw [← cfc_mul (hf := X5LS.cont P _) (hg := X5LS.cont P _)]

theorem fvn_le [Nonempty A] [Nonempty B] (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    fixedVonNeumann rho sigma ≤ (conditionalEntropyBitsAB rho : EReal) := by
  unfold fixedVonNeumann
  split_ifs with hS
  · rw [EReal.coe_le_coe_iff, logterm rho sigma hsigma.1.isHermitian]
    have hB := tl_density hrho
    have hk := klein hB.1 hB.2 hsigma.1 hsigma.2 (supp_tl_of hS)
    unfold conditionalEntropyBitsAB
    rw [vn_eq _ hB.1.isHermitian]
    linarith
  · exact bot_le

theorem fvn_eq [Nonempty A] [Nonempty B] (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho) :
    fixedVonNeumann rho (traceLeft rho) = (conditionalEntropyBitsAB rho : EReal) := by
  have hB := tl_density hrho
  unfold fixedVonNeumann
  have hs : supportedBy rho (identityTensorReference (A := A) (traceLeft rho)) := supp_tl hrho.1
  rw [if_pos hs, logterm rho _ hB.1.isHermitian]
  unfold conditionalEntropyBitsAB
  rw [vn_eq _ hB.1.isHermitian]
  congr 1; ring

theorem fixedMin_le [Nonempty A] [Nonempty B] (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    fixedMin rho sigma ≤ finiteAlpha rho sigma 2 := by
  unfold fixedMin
  refine sSup_le ?_
  rintro _ ⟨r, rfl, hr⟩
  set S := identityTensorReference (A := A) sigma
  have hSp : S.PosSemidef := N_psd sigma hsigma.1
  set c := Real.rpow 2 (-r) with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
  have hr' : ((c : ℂ) • S - rho).PosSemidef := hr
  have hT := X5LS.tr_sq_inv hrho.1 hrho.2 hSp c hc0 hr'
  have hsupp : supportedBy rho S := X5LS.ker_of_le hrho.1 c hr'
  obtain ⟨-, -, -, -, p5⟩ := pack rho sigma hrho hsigma
  have hpos := p5 hsupp 2 (by norm_num)
  rw [fa_form rho sigma 2 (by norm_num), if_neg (fun h => h.2 hsupp)]
  unfold log2Extended
  rw [if_neg hpos.ne', ← EReal.coe_mul, EReal.coe_le_coe_iff]
  have hT' : (Tr rho S 2).re ≤ c := hT
  have hlog : Real.logb 2 (Tr rho S 2).re ≤ Real.logb 2 c :=
    Real.logb_le_logb_of_le (by norm_num) hpos hT'
  have hlc : Real.logb 2 c = -r := by
    rw [hc, show Real.rpow 2 (-r) = (2 : ℝ) ^ (-r) from rfl, Real.logb_rpow (by norm_num) (by norm_num)]
  norm_num
  linarith

theorem half_le [Nonempty A] [Nonempty B] (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho) :
    finiteAlpha rho (traceLeft rho) (1 / 2) ≤ dualMaxEntropy rho := by
  have hB := tl_density hrho
  set S := identityTensorReference (A := A) (traceLeft rho)
  have hSp : S.PosSemidef := N_psd _ hB.1
  obtain ⟨-, p2, -, -, -⟩ := pack rho (traceLeft rho) hrho hB
  set T := (Tr rho S (1 / 2)).re with hTdef
  have hT0 : 0 ≤ T := p2 _ (by norm_num)
  set F := rootFidelity rho S with hFdef
  -- T ≤ F
  have hTF : T ≤ F := by
    have e1 : cfc (fun x : ℝ => x ^ (1 / 2 : ℝ)) rho = cfc Real.sqrt rho :=
      cfc_congr fun x _ => (Real.sqrt_eq_rpow x).symm
    have e2 : cfc (fun x : ℝ => if x = 0 then 0 else x ^ (1 - (1 / 2 : ℝ))) S = cfc Real.sqrt S := by
      refine cfc_congr fun x _ => ?_
      split_ifs with h
      · rw [h, Real.sqrt_zero]
      · rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, Real.sqrt_eq_rpow]
    have hM := X5LS.tn (cfc Real.sqrt rho * cfc Real.sqrt S)
    have hMM : cfc Real.sqrt rho * cfc Real.sqrt S * (cfc Real.sqrt rho * cfc Real.sqrt S)ᴴ =
        cfc Real.sqrt rho * S * cfc Real.sqrt rho := by
      rw [conjTranspose_mul, (X5LS.herm_cfc rho Real.sqrt).eq, (X5LS.herm_cfc S Real.sqrt).eq]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (cfc Real.sqrt S), X5LS.sq_mul_sq hSp, Matrix.mul_assoc]
    rw [hMM] at hM
    simp only [hTdef, hFdef, Tr, rootFidelity]
    rw [e1, e2]
    exact hM
  have hle : finiteAlpha rho (traceLeft rho) (1 / 2) ≤ log2Extended (F ^ 2) := by
    rw [fa_form rho _ (1 / 2) (by norm_num), if_neg (fun h => by norm_num at h)]
    rw [show (1 : ℝ) / (1 - 1 / 2) = 2 by norm_num]
    unfold log2Extended
    rcases hT0.lt_or_eq with hT | hT
    · have hF : 0 < F := lt_of_lt_of_le hT hTF
      rw [← hTdef, if_neg hT.ne', if_neg (pow_ne_zero 2 hF.ne'), ← EReal.coe_mul, EReal.coe_le_coe_iff,
        Real.logb_pow]
      push_cast
      have := Real.logb_le_logb_of_le (b := 2) (by norm_num) hT hTF
      linarith
    · rw [← hTdef, ← hT, if_pos rfl, EReal.coe_mul_bot_of_pos (by norm_num)]
      exact bot_le
  exact hle.trans (le_sSup ⟨traceLeft rho, hB, rfl⟩)

theorem eo_main [Nonempty A] [Nonempty B] (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho) :
    minEntropy rho ≤ (conditionalEntropyBitsAB rho : EReal) ∧
      (conditionalEntropyBitsAB rho : EReal) ≤ dualMaxEntropy rho := by
  have e1 : ∀ (sigma : Matrix B B ℂ), finiteAlpha rho sigma 1 = fixedVonNeumann rho sigma := fun _ => by
    unfold finiteAlpha; rw [if_pos rfl]
  constructor
  · unfold minEntropy
    refine sSup_le ?_
    rintro _ ⟨sigma, hsigma, rfl⟩
    calc fixedMin rho sigma ≤ finiteAlpha rho sigma 2 := fixedMin_le rho sigma hrho hsigma
      _ ≤ finiteAlpha rho sigma 1 :=
          fa_anti rho sigma hrho hsigma (by norm_num : (1 : ℝ) ∈ Ioi 0) (by norm_num : (2 : ℝ) ∈ Ioi 0)
            (by norm_num)
      _ = fixedVonNeumann rho sigma := e1 sigma
      _ ≤ _ := fvn_le rho sigma hrho hsigma
  · have hB := tl_density hrho
    calc (conditionalEntropyBitsAB rho : EReal) = fixedVonNeumann rho (traceLeft rho) := (fvn_eq rho hrho).symm
      _ = finiteAlpha rho (traceLeft rho) 1 := (e1 _).symm
      _ ≤ finiteAlpha rho (traceLeft rho) (1 / 2) :=
          fa_anti rho _ hrho hB (by norm_num : (1 / 2 : ℝ) ∈ Ioi 0) (by norm_num : (1 : ℝ) ∈ Ioi 0)
            (by norm_num)
      _ ≤ _ := half_le rho hrho

end X5EO
end X5mod_EO_Thm

section X5mod_T7_Thm
open Matrix Filter Set
open scoped ComplexOrder Topology ENNReal

namespace X5T7
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23 X5OL
open QAlgorithms.Papers.Independent.Gap20.P03 (fixedMin)
open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized)

attribute [local instance] Classical.propDecidable

/-- for ε ≥ 1 the zero operator is in the ball and has fixed min-entropy +∞ -/
lemma smooth_top' {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ) (hsigma : sigma.PosSemidef)
    (epsilon : ℝ) (he : 1 ≤ epsilon) : sineSmoothFixedMin rho sigma epsilon = ⊤ := by
  have hball : inBall rho 0 epsilon := by
    refine ⟨⟨PosSemidef.zero, by simp⟩, ?_⟩
    unfold fidelityDistance
    refine le_trans ?_ he
    rw [Real.sqrt_le_one]
    nlinarith [sq_nonneg (rootFidelity rho 0)]
  have hmin : fixedMin (0 : Matrix (A × B) (A × B) ℂ) sigma = ⊤ := by
    rw [EReal.eq_top_iff_forall_lt]
    intro y
    refine lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (lt_add_one y)) (le_sSup ⟨y + 1, rfl, ?_⟩)
    rw [sub_zero]
    exact (Matrix.PosSemidef.kronecker Matrix.PosSemidef.one hsigma).smul
      (Complex.zero_le_real.2 (Real.rpow_nonneg (by norm_num) _))
  refine eq_top_iff.2 ?_
  rw [← hmin]
  exact le_sSup ⟨0, hball, rfl⟩

section gen
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma tr_cfc {X : Matrix I I ℂ} (hX : X.IsHermitian) (f : ℝ → ℝ) :
    (cfc f X).trace.re = ∑ i, f (hX.eigenvalues i) := by
  have hcfc1 : cfc (fun _ : ℝ => (1 : ℝ)) X = 1 := cfc_const_one ℝ X hX.isSelfAdjoint
  have := tr_cfc_cfc hX hX f (fun _ => 1)
  rw [hcfc1, Matrix.mul_one] at this
  rw [this, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_sum]
  simp only [Complex.ofReal_re, mul_one]
  rw [← Finset.mul_sum, w_row hX hX, mul_one]

lemma conj_diag (U : Matrix I I ℂ) (M : Matrix I I ℂ) (i : I) :
    (Uᴴ * M * U) i i = star (fun a => U a i) ⬝ᵥ (M *ᵥ fun a => U a i) := by
  simp only [mul_apply, conjTranspose_apply, dotProduct, mulVec, Pi.star_apply, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma diag_re_nonneg {M : Matrix I I ℂ} (hM : M.PosSemidef) (U : Matrix I I ℂ) (i : I) :
    0 ≤ ((Uᴴ * M * U) i i).re := by
  have := (hM.conjTranspose_mul_mul_same U).diag_nonneg (i := i)
  exact (Complex.nonneg_iff.1 this).1

/-- scalar step (23) of the paper -/
lemma scalar (r s lam alpha : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (hlam : 0 < lam) (halpha : 1 < alpha)
    (hz : s = 0 → r = 0) :
    max (r - lam * s) 0 ≤ lam ^ (1 - alpha) * (r ^ alpha * s ^ (1 - alpha)) := by
  have hnn : 0 ≤ lam ^ (1 - alpha) * (r ^ alpha * s ^ (1 - alpha)) := by positivity
  rcases le_or_gt (r - lam * s) 0 with h | h
  · rw [max_eq_right h]; exact hnn
  rw [max_eq_left h.le]
  have hr0 : 0 < r := by nlinarith [mul_nonneg hlam.le hs]
  have hs0 : 0 < s := by
    rcases hs.lt_or_eq with h' | h'
    · exact h'
    · exact absurd (hz h'.symm) hr0.ne'
  have hratio : 1 ≤ r / (lam * s) := by
    rw [one_le_div (by positivity)]; linarith
  have h1 : r ≤ r * (r / (lam * s)) ^ (alpha - 1) := by
    have := Real.one_le_rpow hratio (by linarith : 0 ≤ alpha - 1)
    nlinarith
  have h2 : r * (r / (lam * s)) ^ (alpha - 1) = lam ^ (1 - alpha) * (r ^ alpha * s ^ (1 - alpha)) := by
    rw [Real.div_rpow hr0.le (by positivity), Real.mul_rpow hlam.le hs0.le]
    have e1 : r * r ^ (alpha - 1) = r ^ alpha := by
      rw [← Real.rpow_one_add' hr0.le (by linarith)]; ring_nf
    have e2 : lam ^ (1 - alpha) = (lam ^ (alpha - 1))⁻¹ := by
      rw [← Real.rpow_neg hlam.le]; ring_nf
    have e3 : s ^ (1 - alpha) = (s ^ (alpha - 1))⁻¹ := by
      rw [← Real.rpow_neg hs0.le]; ring_nf
    rw [e2, e3, ← e1]
    field_simp
  have := mul_nonneg hlam.le hs
  linarith

end gen

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem main [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (epsilon alpha : ℝ) (hepsilon : 0 < epsilon) (halpha : 1 < alpha) (halpha2 : alpha ≤ 2) :
    finiteAlpha rho sigma alpha -
      ((Real.logb 2 (2 / epsilon ^ 2) / (alpha - 1) : ℝ) : EReal) ≤
        sineSmoothFixedMin rho sigma epsilon := by
  set N := identityTensorReference (A := A) sigma with hNdef
  have hNpsd : N.PosSemidef := N_psd sigma hsigma.1
  by_cases he1 : 1 ≤ epsilon
  · rw [smooth_top' _ _ hsigma.1 epsilon he1]; exact le_top
  push Not at he1
  by_cases hS : supportedBy rho N
  swap
  · have : finiteAlpha rho sigma alpha = ⊥ := by
      unfold finiteAlpha; rw [if_neg (by linarith), if_pos ⟨halpha, hS⟩]
    rw [this, EReal.bot_sub]; exact bot_le
  have hsuppB : supportedBy (traceLeft rho) sigma := X5EO.supp_tl_of hS
  obtain ⟨lam, hlam, hrad, hmin⟩ :=
    positiveThresholdExists rho sigma hrho hsigma hsuppB epsilon hepsilon.le he1.le
  -- the operator X = ρ - λ N and its eigenbasis
  set X := rho - (lam : ℂ) • N with hXdef
  have hX : X.IsHermitian := hrho.1.isHermitian.sub (hNpsd.smul (Complex.zero_le_real.2 hlam.le)).isHermitian
  set U := (hX.eigenvectorUnitary : Matrix (A × B) (A × B) ℂ) with hU
  set r := fun i => ((Uᴴ * rho * U) i i).re
  set s := fun i => ((Uᴴ * N * U) i i).re
  have hr : ∀ i, 0 ≤ r i := fun i => diag_re_nonneg hrho.1 U i
  have hs : ∀ i, 0 ≤ s i := fun i => diag_re_nonneg hNpsd U i
  have heig : ∀ i, hX.eigenvalues i = r i - lam * s i := by
    intro i
    rw [hX.eigenvalues_eq i]
    have hcol : (⇑(hX.eigenvectorBasis i) : A × B → ℂ) = fun a => U a i := by
      funext a; rw [hU, Matrix.IsHermitian.eigenvectorUnitary_apply]
    rw [hcol]
    simp only [r, s, conj_diag, hXdef, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul,
      RCLike.re_to_complex, Complex.sub_re, smul_eq_mul, Complex.re_ofReal_mul]
  have hz : ∀ i, s i = 0 → r i = 0 := by
    intro i hi
    have hq : star (fun a => U a i) ⬝ᵥ (N *ᵥ fun a => U a i) = 0 := by
      have h0 := conj_diag U N i
      have him : ((Uᴴ * N * U) i i).im = 0 := by
        have := (hNpsd.conjTranspose_mul_mul_same U).diag_nonneg (i := i)
        exact ((Complex.nonneg_iff.1 this).2).symm
      rw [← h0]; exact Complex.ext hi him
    have hNv := (hNpsd.dotProduct_mulVec_zero_iff _).1 hq
    have hρv : rho *ᵥ (fun a => U a i) = 0 := by
      have := hS (show (fun a => U a i) ∈ LinearMap.ker N.mulVecLin by
        simp only [LinearMap.mem_ker, mulVecLin_apply]; exact hNv)
      simpa only [LinearMap.mem_ker, mulVecLin_apply] using this
    simp only [r]; rw [conj_diag, hρv, dotProduct_zero, Complex.zero_re]
  -- tr Δ = ε²/2
  set T := (cfc (fun x : ℝ => x ^ alpha) rho *
      cfc (fun x : ℝ => if x = 0 then 0 else x ^ (1 - alpha)) N).trace.re with hT
  have htrΔ : (cfc (fun x : ℝ => max x 0) X).trace.re = epsilon ^ 2 / 2 := by
    unfold thresholdRadius at hrad
    rw [← hNdef, ← hXdef] at hrad
    set y := (cfc (fun x : ℝ => max x 0) X).trace.re
    rcases le_or_gt 0 y with hy | hy
    · have := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 2 * y)
      rw [hrad] at this; linarith
    · rw [Real.sqrt_eq_zero'.2 (by linarith)] at hrad; linarith
  have hchild := pinchingQuasiMonotone rho N hrho.1 hNpsd hS hX.eigenvectorUnitary alpha halpha halpha2
  have hkey : epsilon ^ 2 / 2 ≤ lam ^ (1 - alpha) * T := by
    rw [← htrΔ, tr_cfc hX]
    calc ∑ i, max (hX.eigenvalues i) 0 ≤ ∑ i, lam ^ (1 - alpha) * (r i ^ alpha * s i ^ (1 - alpha)) :=
          Finset.sum_le_sum fun i _ => by
            rw [heig]; exact scalar _ _ _ _ (hr i) (hs i) hlam halpha (hz i)
      _ = lam ^ (1 - alpha) * ∑ i, r i ^ alpha * s i ^ (1 - alpha) := by rw [Finset.mul_sum]
      _ ≤ lam ^ (1 - alpha) * T := mul_le_mul_of_nonneg_left hchild (by positivity)
  have hTpos : 0 < T := by
    have h1 : 0 < lam ^ (1 - alpha) * T := lt_of_lt_of_le (by positivity) hkey
    exact pos_of_mul_pos_right h1 (by positivity)
  have hFA : finiteAlpha rho sigma alpha = ((1 / (1 - alpha) * Real.logb 2 T : ℝ) : EReal) := by
    unfold finiteAlpha
    rw [if_neg (by linarith), if_neg (fun h => h.2 hS)]
    unfold log2Extended
    rw [← hNdef, ← hT, if_neg hTpos.ne', ← EReal.coe_mul]
  rw [hFA, ← EReal.coe_sub]
  refine le_trans (EReal.coe_le_coe_iff.2 ?_) hmin
  -- real inequality: λ^{α-1} ≤ 2T/ε²
  have hb : 0 < alpha - 1 := by linarith
  have hpow : lam ^ (alpha - 1) ≤ 2 / epsilon ^ 2 * T := by
    have e : lam ^ (1 - alpha) = (lam ^ (alpha - 1))⁻¹ := by
      rw [← Real.rpow_neg hlam.le]; ring_nf
    rw [e] at hkey
    have hl : 0 < lam ^ (alpha - 1) := by positivity
    have h3 : epsilon ^ 2 / 2 * lam ^ (alpha - 1) ≤ T := by
      have := mul_le_mul_of_nonneg_right hkey hl.le
      rwa [mul_comm (lam ^ (alpha - 1))⁻¹ T, mul_assoc, inv_mul_cancel₀ hl.ne', mul_one] at this
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [h3]
  have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hpow
  rw [Real.logb_rpow_eq_mul_logb_of_pos hlam, Real.logb_mul (by positivity) hTpos.ne'] at hlog
  have : 1 / (1 - alpha) * Real.logb 2 T = -(Real.logb 2 T / (alpha - 1)) := by
    rw [show (1 : ℝ) - alpha = -(alpha - 1) by ring]; field_simp
  rw [this, show -(Real.logb 2 T / (alpha - 1)) - Real.logb 2 (2 / epsilon ^ 2) / (alpha - 1) =
    -((Real.logb 2 (2 / epsilon ^ 2) + Real.logb 2 T) / (alpha - 1)) by ring, neg_le_neg_iff,
    le_div_iff₀ hb]
  linarith

end X5T7
end X5mod_T7_Thm

noncomputable section

open Filter

open scoped ENNReal ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23

theorem solution {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (epsilon alpha : ℝ) (hepsilon : 0 < epsilon) (halpha : 1 < alpha) (halpha2 : alpha ≤ 2) :
    finiteAlpha rho sigma alpha -
      ((Real.logb 2 (2 / epsilon ^ 2) / (alpha - 1) : ℝ) : EReal) ≤
        sineSmoothFixedMin rho sigma epsilon :=
  X5T7.main rho sigma hrho hsigma epsilon alpha hepsilon halpha halpha2

end
