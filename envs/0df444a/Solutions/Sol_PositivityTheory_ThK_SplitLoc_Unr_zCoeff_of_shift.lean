-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.zCoeff_of_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:20:10.303596+00:00
-- url     : https://prove2.me/submissions/c0ed02e8-4ec7-45c0-91af-0cd018b23176

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_zCoeff_eq
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_cst_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.SplitLoc PositivityTheory.ThK.SplitLoc.Unr
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SmGL
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution {ϖ : kˣ} (hϖ : IsUnif ϖ) {ν : kˣ →* ℂˣ} (hν : IsUnram ν) (d : ℕ) {n : ℕ}
    {φ ψ : Matrix (Fin n) (Fin n) k → ℂ} (hφ : φ ∈ SB _) (hψ : ψ ∈ SB _) {o : ℤ}
    (h : ∀ m, Jm n ψ m = Jm n φ (m + o)) :
    zCoeff n d ϖ ν ψ = fun m => (cst d ϖ ν ^ o)⁻¹ * zCoeff n d ϖ ν φ (m + o) := by
  funext m
  have hc := cst_ne_zero d ϖ ν
  have hco := zpow_ne_zero o hc
  rw [zCoeff_eq hϖ hν d hψ, zCoeff_eq hϖ hν d hφ, h, zpow_add₀ hc]
  field_simp
end PositivityTheory.ThK.SplitLoc.Unr
