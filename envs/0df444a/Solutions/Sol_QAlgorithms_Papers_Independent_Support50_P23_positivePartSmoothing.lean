-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P23.positivePartSmoothing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T10:39:21.743758+00:00
-- url     : https://prove2.me/submissions/f8474064-e23d-40e8-884e-d3fd33be94dd

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P23

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

section X5mod_LS_Thm
open Matrix
open scoped ComplexOrder

namespace X5LS
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23

theorem main {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    ((-Real.logb 2 lambda : ℝ) : EReal) ≤
      sineSmoothFixedMin rho sigma (thresholdRadius rho sigma lambda) := by
  set S := (lambda : ℂ) • identityTensorReference (A := A) sigma with hS
  have hK : (identityTensorReference (A := A) sigma).PosSemidef :=
    Matrix.PosSemidef.kronecker Matrix.PosSemidef.one hsigma.1
  have hSp : S.PosSemidef := hK.smul (by exact_mod_cast hlambda.le)
  obtain ⟨τ, hτ, hτtr, hSτ, hF⟩ := core rho S hrho.1 hrho.2 hSp
  set t := (cfc (fun x : ℝ => max x 0) (rho - S)).trace.re with ht
  have hF0 : 0 ≤ (cfc Real.sqrt (cfc Real.sqrt rho * τ * cfc Real.sqrt rho)).trace.re := by
    have h1 : (cfc Real.sqrt rho * τ * cfc Real.sqrt rho).PosSemidef := conj_psd hτ (herm_cfc _ _)
    have h2 := cfc_psd h1.isHermitian Real.sqrt fun x _ => Real.sqrt_nonneg x
    exact (Complex.nonneg_iff.mp h2.trace_nonneg).1
  refine le_sSup_of_le ⟨τ, ⟨⟨hτ, hτtr⟩, ?_⟩, rfl⟩ ?_
  · unfold fidelityDistance thresholdRadius rootFidelity
    rw [← hS, ← ht]
    apply Real.sqrt_le_sqrt
    set F := (cfc Real.sqrt (cfc Real.sqrt rho * τ * cfc Real.sqrt rho)).trace.re
    rcases le_total t 1 with h | h
    · have := mul_le_mul hF hF (by linarith) hF0
      nlinarith [sq_nonneg t]
    · nlinarith [sq_nonneg F]
  · unfold QAlgorithms.Papers.Independent.Gap20.P03.fixedMin
    refine le_sSup ⟨-Real.logb 2 lambda, rfl, ?_⟩
    have e : Real.rpow 2 (-(-Real.logb 2 lambda)) = lambda := by
      rw [neg_neg]; exact Real.rpow_logb (by norm_num) (by norm_num) hlambda
    rw [e]
    exact hSτ

end X5LS

end X5mod_LS_Thm

noncomputable section

open Filter

open scoped ENNReal ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23

theorem solution {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    ((-Real.logb 2 lambda : ℝ) : EReal) ≤
      sineSmoothFixedMin rho sigma (thresholdRadius rho sigma lambda) :=
  X5LS.main rho sigma hrho hsigma lambda hlambda

end
