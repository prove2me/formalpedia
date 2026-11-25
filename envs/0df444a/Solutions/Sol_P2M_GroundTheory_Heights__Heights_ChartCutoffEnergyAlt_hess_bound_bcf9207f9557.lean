-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_hess_bound_bcf9207f9557
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:12:08.555459+00:00
-- url     : https://prove2.me/submissions/ec1eea5c-a119-4430-ab47-e5bcc3780956

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartCutoffEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartCutoffEnergy
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_sqn_nonneg_fadf2dd021f1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_hessC_eq_cxHessian_ae8a5d56a517
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_star_dotProduct_self_eq_691e76ba67ec
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_exists_conjTranspose_mul_self_3bc270d4f9d5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartDensityIntegrable_proof_2baed358c155
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessCompare_proof_f24bf8ab28d5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_hessForm_le_428f2adefc09
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_hess_form_eq_6de19faee787
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_hess_isHermitian_36e14e4d0526
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermFormCompare_proof_2b7fad7c2fe0


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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm Matrix MeasureTheory Filter
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartCutoffEnergyAlt
open ReciprocityTheory.AnForm.A
namespace GroundTheory.Heights₂.Heights.ChartCutoffEnergyAlt
theorem _root_.solution {e : ℕ} {M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hM : M.PosDef) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Fin e → ℂ, (hessC (hermChartPot M) y).PosSemidef ∧
      ((((C / (1 + sqn y)) : ℝ) : ℂ) • (1 : Matrix (Fin e) (Fin e) ℂ) - hessC (hermChartPot M) y).PosSemidef := by
  obtain ⟨C0, hC0⟩ := ChartHessCompare.proof HermFormCompare.proof e M M hM hM
  obtain ⟨a, ha, hMa⟩ := HermFormCompare.proof (e + 1) M 1 hM PosDef.one
  obtain ⟨a', ha', haM⟩ := HermFormCompare.proof (e + 1) 1 M PosDef.one hM
  obtain ⟨B, hMB, hB⟩ := ChartDensityIntegrableAlt.exists_conjTranspose_mul_self hM
  refine ⟨a * a' / 2, by positivity, fun y => ⟨?_, ?_⟩⟩
  · rw [hessC_eq_cxHessian]; exact (hC0 y).1.posSemidef
  subst hMB
  rw [hessC_eq_cxHessian, posSemidef_iff_dotProduct_mulVec]
  refine ⟨(isHermitian_one.smul ?_).sub (ChartHessianComparison.hess_isHermitian B hB y), fun x => ?_⟩
  · show star (((a * a' / 2 / (1 + sqn y)) : ℝ) : ℂ) = _
    simp
  rw [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul,
    ChartHessianComparison.hess_form_eq B hB, star_dotProduct_self_eq, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
  refine Complex.zero_le_real.mpr (sub_nonneg.mpr ?_)
  have hle := ChartHessianComparison.hessForm_le B hB y x 0
  simp only [zero_smul, sub_zero] at hle
  set w : Fin (e + 1) → ℂ := Fin.cons 0 (star x) with hw
  set v : Fin (e + 1) → ℂ := Fin.cons 1 y with hv
  have hw1 := hMa w
  have hv1 := haM v
  rw [one_mulVec, star_dotProduct_self_eq, Complex.ofReal_re] at hw1 hv1
  have hsw : sqn w = sqn x := by
    simp [sqn, hw, Fin.sum_univ_succ]
  have hsv : sqn v = 1 + sqn y := by
    simp [sqn, hv, Fin.sum_univ_succ]
  rw [hsw] at hw1
  rw [hsv] at hv1
  set qw := (star w ⬝ᵥ ((Bᴴ * B) *ᵥ w)).re
  set qv := (star v ⬝ᵥ ((Bᴴ * B) *ᵥ v)).re
  have hS := sqn_nonneg y
  have hX := sqn_nonneg x
  have hqv : 0 < qv := pos_of_mul_pos_right (show 0 < a' * qv by linarith) ha'.le
  have hr : 1 ≤ a' * qv / (1 + sqn y) := (one_le_div (by linarith)).mpr hv1
  calc _ ≤ qw / (2 * qv) := hle
    _ ≤ a * sqn x / (2 * qv) := by gcongr
    _ ≤ a * a' / 2 / (1 + sqn y) * sqn x := by
      rw [div_le_iff₀ (by positivity)]
      calc a * sqn x = a * sqn x * 1 := (mul_one _).symm
        _ ≤ a * sqn x * (a' * qv / (1 + sqn y)) := by gcongr
        _ = _ := by ring
end GroundTheory.Heights₂.Heights.ChartCutoffEnergyAlt
