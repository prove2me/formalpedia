-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.weak_bounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:23:41.08095+00:00
-- url     : https://prove2.me/submissions/c57be162-db2a-4c7c-b90c-5bb3f6ba0cbc

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IteratedFDerivSubApply
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_SliceAn
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_norming

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped SchwartzMap NNReal
variable {S : Type} [AddCommGroup S] [Module ℂ S]
variable [TopologicalSpace S] [IsTopologicalAddGroup S]
namespace PositivityTheory.ThKG.Loc.Bump
theorem _root_.solution {ι : Type} (g : ι → S) (h : ∀ T : S →L[ℂ] ℂ, ∃ C, ∀ i, ‖T (g i)‖ ≤ C) (q : Seminorm ℂ S) (hq : Continuous q) :
    ∃ C, ∀ i, q (g i) ≤ C := by
  let e : ι → (Sy q →L[ℂ] ℂ) →L[ℂ] ℂ := fun i => ContinuousLinearMap.apply ℂ ℂ (g i : Sy q)
  obtain ⟨C, hC⟩ := banach_steinhaus (g := e) fun f =>
    h (toCLM q hq (f : Sy q →ₗ[ℂ] ℂ) ‖f‖ fun x => f.le_opNorm x)
  refine ⟨max C 0, fun i => ?_⟩
  obtain ⟨T, h1, h2⟩ := norming q (g i)
  let f : Sy q →L[ℂ] ℂ := LinearMap.mkContinuous (E := Sy q) T 1 fun x => by rw [one_mul]; exact h2 x
  have hf : ‖f‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
  calc q (g i) = ‖e i f‖ := h1.symm
    _ ≤ ‖e i‖ * ‖f‖ := (e i).le_opNorm f
    _ ≤ max C 0 * 1 := mul_le_mul ((hC i).trans (le_max_left _ _)) hf (norm_nonneg _) (le_max_right _ _)
    _ = _ := mul_one _
end PositivityTheory.ThKG.Loc.Bump
