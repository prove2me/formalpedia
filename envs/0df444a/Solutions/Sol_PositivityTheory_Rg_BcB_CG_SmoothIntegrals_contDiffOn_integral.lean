-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.CG.SmoothIntegrals.contDiffOn_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:51:58.159607+00:00
-- url     : https://prove2.me/submissions/cebe9a96-cb32-479f-b519-05340e9ab65e

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_HeckeFubiniCompatibility_PSmoothA
import Theorems.Thm_PositivityTheory_Rg_BcB_CG_SmoothIntegrals_contDiffOn_integral_nat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric Set
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.CG.SmoothIntegrals
variable {X M T : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup M] [NormedSpace ℝ M]
  [TopologicalSpace T] [T2Space T] [MeasurableSpace T] [OpensMeasurableSpace T]
variable {μ : Measure T} [IsFiniteMeasureOnCompacts μ] {U : Set X} {W : Set M} {p : T → M}
namespace PositivityTheory.Rg.BcB.CG.SmoothIntegrals
theorem _root_.solution (hU : IsOpen U) (hW : IsOpen W) (hp : Continuous p) (hpW : ∀ y, p y ∈ W) {V : Type}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {Q : X × M → V}
    (hQ : ContDiffOn ℝ ∞ Q (U ×ˢ W)) (hs : ∀ x ∈ U, ∃ K, IsCompact K ∧ ∀ᶠ x' in 𝓝 x, ∀ y ∉ K, Q (x', p y) = 0) :
    ContDiffOn ℝ ∞ (fun x => ∫ y, Q (x, p y) ∂μ) U :=
  contDiffOn_infty.2 fun n => contDiffOn_integral_nat hU hW hp hpW n V Q hQ hs
end PositivityTheory.Rg.BcB.CG.SmoothIntegrals
