-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.Ald.PCI.contDiff_pder
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:02:44.042898+00:00
-- url     : https://prove2.me/submissions/d89f7058-6a1a-40f6-a647-5467a9cc6aad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzVanishingDecomposition
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LagrangianDecomposition_IteratedFDerivIntegral
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_Ald_PCI_pder_eq

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
theorem _root_.solution (n : ℕ) {Θ : V × ℝ → ℂ} (hΘ : ContDiff ℝ ∞ Θ) : ContDiff ℝ ∞ (pder n Θ) := by
  have : pder n Θ = (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin n => ContinuousLinearMap.inl ℝ V ℝ)) ∘ iteratedFDeriv ℝ n Θ := by
    funext p; rw [pder_eq n hΘ p]; rfl
  rw [this]
  exact (ContinuousLinearMap.contDiff _).comp (hΘ.iteratedFDeriv_right (by norm_cast))
end PositivityTheory.SiegelWeilFormula.Ald.PCI
