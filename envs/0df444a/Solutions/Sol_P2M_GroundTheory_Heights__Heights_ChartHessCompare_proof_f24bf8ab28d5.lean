-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartHessCompare_proof_f24bf8ab28d5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:56:32.469795+00:00
-- url     : https://prove2.me/submissions/3b84336a-f473-4543-b58a-6b24e932b530

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChartGramHess
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_norm_sq_toLp_mulVec_782ab3756c0f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_toLp_mulVec_ne_zero_ab75d852d29d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_hess_form_eq_6de19faee787
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_hess_isHermitian_36e14e4d0526
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_hessForm_le_428f2adefc09
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_hessForm_eq_d57766978758
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_hessForm_pos_734925469169
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_exists_conjTranspose_mul_self_3bc270d4f9d5


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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix
open scoped ComplexOrder InnerProductSpace
noncomputable section
open ChartHessianComparison
namespace GroundTheory.Heights₂.Heights
namespace ChartHessCompare
theorem _root_.solution (hCmp : HermFormCompare.Statement) : ChartHessCompare.Statement := by
  intro e M N hM hN
  obtain ⟨B, hMB, hB⟩ := ChartDensityIntegrableAlt.exists_conjTranspose_mul_self hM
  obtain ⟨B', hNB, hB'⟩ := ChartDensityIntegrableAlt.exists_conjTranspose_mul_self hN
  obtain ⟨a, ha, hMN⟩ := hCmp (e + 1) M N hM hN
  obtain ⟨a', ha', hNM⟩ := hCmp (e + 1) N M hN hM
  subst hMB hNB
  refine ⟨a * a', fun y => ⟨?_, ?_⟩⟩
  · refine PosDef.of_dotProduct_mulVec_pos (hess_isHermitian B hB y) fun x hx => ?_
    rw [hess_form_eq B hB]
    exact Complex.zero_lt_real.mpr (hessForm_pos B hB y hx)
  · rw [posSemidef_iff_dotProduct_mulVec]
    refine ⟨((hess_isHermitian B' hB' y).smul ?_).sub (hess_isHermitian B hB y), fun x => ?_⟩
    · show star ((a * a' : ℝ) : ℂ) = ((a * a' : ℝ) : ℂ)
      simp
    rw [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, hess_form_eq B hB,
      hess_form_eq B' hB', smul_eq_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
    refine Complex.zero_le_real.mpr (sub_nonneg.mpr ?_)
    obtain ⟨s, hs⟩ := hessForm_eq B' y x
    have h1 := hessForm_le B hB y x s
    rw [hs]
    set w := (Fin.cons 0 (star x) : Fin (e + 1) → ℂ) - s • Fin.cons 1 y with hw
    set v := (Fin.cons 1 y : Fin (e + 1) → ℂ) with hv
    have hv0 : v ≠ 0 := fun h => by simpa [hv] using congrFun h 0
    have hqv : 0 < (star v ⬝ᵥ ((Bᴴ * B) *ᵥ v)).re := by
      rw [← norm_sq_toLp_mulVec]
      have := norm_pos_iff.mpr (toLp_mulVec_ne_zero B hB hv0)
      positivity
    have hqv' : 0 < (star v ⬝ᵥ ((B'ᴴ * B') *ᵥ v)).re := by
      rw [← norm_sq_toLp_mulVec]
      have := norm_pos_iff.mpr (toLp_mulVec_ne_zero B' hB' hv0)
      positivity
    have hqw' : 0 ≤ (star w ⬝ᵥ ((B'ᴴ * B') *ᵥ w)).re := by
      rw [← norm_sq_toLp_mulVec]
      positivity
    refine h1.trans ?_
    rw [div_le_iff₀ (by positivity)]
    set r := (star w ⬝ᵥ ((B'ᴴ * B') *ᵥ w)).re / (2 * (star v ⬝ᵥ ((B'ᴴ * B') *ᵥ v)).re) with hr
    have hr0 : 0 ≤ r := by positivity
    have e1 : (star w ⬝ᵥ ((B'ᴴ * B') *ᵥ w)).re = r * (2 * (star v ⬝ᵥ ((B'ᴴ * B') *ᵥ v)).re) := by
      rw [hr, div_mul_cancel₀ _ (by positivity)]
    calc (star w ⬝ᵥ ((Bᴴ * B) *ᵥ w)).re ≤ a * (star w ⬝ᵥ ((B'ᴴ * B') *ᵥ w)).re := hMN w
      _ = a * r * 2 * (star v ⬝ᵥ ((B'ᴴ * B') *ᵥ v)).re := by rw [e1]; ring
      _ ≤ a * r * 2 * (a' * (star v ⬝ᵥ ((Bᴴ * B) *ᵥ v)).re) := by gcongr; exact hNM v
      _ = a * a' * r * (2 * (star v ⬝ᵥ ((Bᴴ * B) *ᵥ v)).re) := by ring
end ChartHessCompare
end GroundTheory.Heights₂.Heights
