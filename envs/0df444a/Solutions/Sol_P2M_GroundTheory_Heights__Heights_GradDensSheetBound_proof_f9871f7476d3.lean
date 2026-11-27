-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GradDensSheetBound_proof_f9871f7476d3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:55:48.01902+00:00
-- url     : https://prove2.me/submissions/a4bcceb3-efdc-4bd6-b222-015dc737a178

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGradDensSheetBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradDensSheetBound_vecMulVec_real_smul_897eed499e88
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradDensSheetBound_two_abs_re_mdisc_le_c35b36d2ca9c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradDensSheetBound_abs_le_of_forall_pos_19b8f3740a14
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradDensSheetBound_exists_hessC_bound_31a6c909ca72
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradDensSheetBound_posSemidef_transpose_mul_mul_conj_ecf514a418de
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_euclPot_53e03a97724f
import Theorems.Thm_ReciprocityTheory_AnForm_A_gradMat_eq_vecMulVec
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessC_comp
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessC_sum_normSq
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_cons_smul_fst
import Theorems.Thm_ReciprocityTheory_AnForm_A_re_mdisc_cons_vecMulVec_nonneg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix
open scoped ComplexOrder
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace GradDensSheetBound
theorem _root_.solution : GradDensSheetBound.Statement := by
  intro n d φ U K hU hK hKU hφ
  obtain ⟨c, hc, hcK⟩ := exists_hessC_bound φ U K hU hK hKU hφ
  refine ⟨3 ^ (d + 1) * c ^ d, by positivity, fun s y v w hs hsy => ?_⟩
  have hE : ContDiffAt ℝ 2 (euclPot : (Fin n → ℂ) → ℝ) (s y) :=
    ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
  have hW : hessC (euclPot ∘ s) y = (jacC s y)ᵀ * (1 : Matrix (Fin n) (Fin n) ℂ) * (jacC s y).map (starRingEnd ℂ) := by
    have e : (euclPot : (Fin n → ℂ) → ℝ) = fun w => ∑ i, Complex.normSq (w i) := by
      funext w; simp [euclPot, Complex.normSq_eq_norm_sq]
    rw [hessC_comp _ _ _ hs hE, e, hessC_sum_normSq]
  have hA : ∀ i, hessC (φ i ∘ s) y =
      (jacC s y)ᵀ * hessC (φ i) (s y) * (jacC s y).map (starRingEnd ℂ) := fun i =>
    hessC_comp _ _ _ hs ((hφ i).contDiffAt (hU.mem_nhds (hKU hsy)))
  have hle : ∀ i, ((c : ℂ) • hessC (euclPot ∘ s) y - hessC (φ i ∘ s) y).PosSemidef := by
    intro i
    have e : (c : ℂ) • ((jacC s y)ᵀ * (1 : Matrix (Fin n) (Fin n) ℂ) * (jacC s y).map (starRingEnd ℂ)) -
        (jacC s y)ᵀ * hessC (φ i) (s y) * (jacC s y).map (starRingEnd ℂ) =
        (jacC s y)ᵀ * ((c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - hessC (φ i) (s y)) * (jacC s y).map (starRingEnd ℂ) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [hW, hA, e]
    exact posSemidef_transpose_mul_mul_conj _ (hcK _ hsy i).1
  have hge : ∀ i, (hessC (φ i ∘ s) y + (c : ℂ) • hessC (euclPot ∘ s) y).PosSemidef := by
    intro i
    have e : (jacC s y)ᵀ * hessC (φ i) (s y) * (jacC s y).map (starRingEnd ℂ) +
        (c : ℂ) • ((jacC s y)ᵀ * (1 : Matrix (Fin n) (Fin n) ℂ) * (jacC s y).map (starRingEnd ℂ)) =
        (jacC s y)ᵀ * (hessC (φ i) (s y) + (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) * (jacC s y).map (starRingEnd ℂ) := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [hW, hA, e]
    exact posSemidef_transpose_mul_mul_conj _ (hcK _ hsy i).2
  have hWpsd : (hessC (euclPot ∘ s) y).PosSemidef := by
    rw [hW]; exact posSemidef_transpose_mul_mul_conj _ PosSemidef.one
  unfold gradDens
  simp only [gradMat_eq_vecMulVec]
  generalize (fun j => dz j (cplx v) y) = a
  generalize (fun k => dz k (cplx w) y) = b
  generalize hessC (euclPot ∘ s) y = W at hle hge hWpsd ⊢
  have hN : (0 : ℝ) ≤ ((d + 1).factorial : ℝ) * (2 / Real.pi) ^ (d + 1) := by positivity
  set N : ℝ := ((d + 1).factorial : ℝ) * (2 / Real.pi) ^ (d + 1) with hNdef
  set X := (mdisc (Fin.cons (vecMulVec a (star b)) (fun i => hessC (φ i ∘ s) y) :
    Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)).re with hXdef
  set P := (mdisc (Fin.cons (vecMulVec a (star a)) (fun _ : Fin d => W) :
    Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)).re with hPdef
  set Q := (mdisc (Fin.cons (vecMulVec b (star b)) (fun _ : Fin d => W) :
    Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)).re with hQdef
  have hP : 0 ≤ P := re_mdisc_cons_vecMulVec_nonneg a (fun _ : Fin d => W) (fun _ => hWpsd)
  have hQ : 0 ≤ Q := re_mdisc_cons_vecMulVec_nonneg b (fun _ : Fin d => W) (fun _ => hWpsd)
  have key : |X| ≤ 3 ^ (d + 1) * c ^ d * Real.sqrt P * Real.sqrt Q := by
    refine abs_le_of_forall_pos hP hQ (by positivity) fun u hu => ?_
    have hsu := Real.sqrt_pos.2 hu
    have ht := two_abs_re_mdisc_le ((Real.sqrt u : ℂ) • a) ((((Real.sqrt u)⁻¹ : ℝ) : ℂ) • b)
      (fun i => hessC (φ i ∘ s) y) (fun _ => W) c hc hle hge
    rw [vecMulVec_real_smul, vecMulVec_real_smul, vecMulVec_real_smul, mul_inv_cancel₀ hsu.ne',
      Complex.ofReal_one, one_smul, mdisc_cons_smul_fst, mdisc_cons_smul_fst, Complex.re_ofReal_mul,
      Complex.re_ofReal_mul, Real.mul_self_sqrt hu.le, ← mul_inv, Real.mul_self_sqrt hu.le] at ht
    exact ht
  rw [abs_mul, abs_of_nonneg hN, Real.sqrt_mul hN, Real.sqrt_mul hN]
  have sN := Real.mul_self_sqrt hN
  calc N * |X| ≤ N * (3 ^ (d + 1) * c ^ d * Real.sqrt P * Real.sqrt Q) :=
        mul_le_mul_of_nonneg_left key hN
    _ = 3 ^ (d + 1) * c ^ d * (Real.sqrt N * Real.sqrt P) * (Real.sqrt N * Real.sqrt Q) := by
        linear_combination (-(3 ^ (d + 1) * c ^ d * Real.sqrt P * Real.sqrt Q)) * sN
end GradDensSheetBound
end GroundTheory.Heights₂.Heights
