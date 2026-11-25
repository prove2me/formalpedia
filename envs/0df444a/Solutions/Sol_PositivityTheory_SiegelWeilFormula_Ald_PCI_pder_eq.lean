-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.Ald.PCI.pder_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:55:34.116808+00:00
-- url     : https://prove2.me/submissions/ac74d18b-13d1-4c50-966a-c0ee8635577f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzVanishingDecomposition
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LagrangianDecomposition_IteratedFDerivIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ContDiff
open MeasureTheory Set Filter Topology
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.Ald PositivityTheory.SiegelWeilFormula.Ald.PCI
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace PositivityTheory.SiegelWeilFormula.Ald.PCI
theorem _root_.solution (n : ℕ) {Θ : V × ℝ → ℂ} (hΘ : ContDiff ℝ ∞ Θ) (p : V × ℝ) :
    pder n Θ p = (iteratedFDeriv ℝ n Θ p).compContinuousLinearMap (fun _ => ContinuousLinearMap.inl ℝ V ℝ) := by
  have e : (fun y => Θ (y, p.2)) = (fun z => Θ (z + (0, p.2))) ∘ ContinuousLinearMap.inl ℝ V ℝ := by
    funext y; simp
  have hg : ContDiff ℝ ∞ (fun z => Θ (z + (0, p.2))) := hΘ.comp (contDiff_id.add contDiff_const)
  rw [pder, e, ContinuousLinearMap.iteratedFDeriv_comp_right _ hg _ (by exact_mod_cast le_top),
    iteratedFDeriv_comp_add_right]
  simp
end PositivityTheory.SiegelWeilFormula.Ald.PCI
