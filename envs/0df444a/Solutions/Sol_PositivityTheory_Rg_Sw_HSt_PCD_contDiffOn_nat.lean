-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.HSt.PCD.contDiffOn_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:39:39.280364+00:00
-- url     : https://prove2.me/submissions/76a27f2e-13c0-4a60-bf06-d2844b75e561

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_ParamCD
import Theorems.Thm_PositivityTheory_Rg_Sw_HSt_PCD_Good_dK
import Theorems.Thm_PositivityTheory_Rg_Sw_HSt_PCD_Good_hasFDerivAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.PCD
variable {F X : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X] [SecondCountableTopology X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Set F} {K : F → X → E}
omit [NormedSpace ℝ E]
namespace PositivityTheory.Rg.Sw.HSt.PCD
theorem _root_.solution (hΩ : IsOpen Ω) (ν : Measure X) [IsFiniteMeasureOnCompacts ν] (N : ℕ) :
    ∀ (E' : Type) [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E'] (K : F → X → E'), Good Ω K →
      ContDiffOn ℝ N (fun x => ∫ u, K x u ∂ν) Ω := by
  induction N with
  | zero =>
    intro E' _ _ _ K hK
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun x hx => (hK.hasFDerivAt hΩ ν hx).continuousAt.continuousWithinAt
  | succ N ih =>
    intro E' _ _ _ K hK
    rw [show ((N + 1 : ℕ) : WithTop ℕ∞) = (N : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiffOn_succ_iff_fderiv_of_isOpen hΩ]
    refine ⟨fun x hx => (hK.hasFDerivAt hΩ ν hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    refine (ih (F →L[ℝ] E') _ (hK.dK hΩ)).congr fun x hx => ?_
    exact (hK.hasFDerivAt hΩ ν hx).fderiv
end PositivityTheory.Rg.Sw.HSt.PCD
