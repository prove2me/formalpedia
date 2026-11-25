-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.STD.dc_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:55:42.619021+00:00
-- url     : https://prove2.me/submissions/12dc6c61-4d3e-4201-8e7e-70e1b117938e

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffC
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_STD_hermL_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_STD_herm_v


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology Function
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
open PositivityTheory.Rg.Sw.LVs.STD
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.STD
theorem _root_.solution {Ψ : Matrix (Fin n) (Fin n) ℂ → ℂ} {x : Vr n} (hΨ : DifferentiableAt ℂ Ψ (herm x))
    (a : Fin n × Fin n) :
    dc a (fun y => Ψ (herm y)) x = fderiv ℂ Ψ (herm x) (Matrix.single a.1 a.2 1) := by
  have hd : HasFDerivAt (fun y => Ψ (hermL n y)) (((fderiv ℂ Ψ (herm x)).restrictScalars ℝ).comp (hermL n)) x :=
    (hΨ.hasFDerivAt.restrictScalars ℝ).comp x (hermL n).hasFDerivAt
  have hf : fderiv ℝ (fun y => Ψ (herm y)) x = ((fderiv ℂ Ψ (herm x)).restrictScalars ℝ).comp (hermL n) :=
    hd.fderiv
  simp only [dc, hf, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars', hermL_apply]
  rw [← herm_v, map_add, map_smul, smul_eq_mul]
end PositivityTheory.Rg.Sw.LVs.STD
