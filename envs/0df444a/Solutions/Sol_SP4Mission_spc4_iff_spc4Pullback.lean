-- Prove2me | solution 1 for SP4Mission.spc4_iff_spc4Pullback
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T05:57:36.382479+00:00
-- url     : https://prove2.me/submissions/2311d1a4-d972-42f2-a6bb-8371df590ac3

import Definitions.Def_SP4Sphere
import Definitions.Def_SP4PullbackForm
import Definitions.Def_SP4TransportBridge

set_option autoImplicit false

namespace SP4Mission

open scoped Manifold ContDiff

noncomputable section

section Transport

variable {N : Type} [TopologicalSpace N]

end Transport

section Bridge

open Set ChartedSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners 𝕜 E H'}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H' X]
  {X' : Type*} [TopologicalSpace X'] [ChartedSpace H' X']
  {m : ℕ∞ω} [IsManifold I m X] [IsManifold I m X']

end Bridge

theorem spc4Pullback_implies_spc4 (hP : SPC4Pullback) : SPC4 := by
  intro M _ _ _ _ _ hM
  obtain ⟨e⟩ := hM
  obtain ⟨σ⟩ := hP M e
  have στ := @Structomorph.trans (EuclideanSpace ℝ (Fin 4)) M M S4 _ _ _ _ _
    (contDiffGroupoid ∞ (𝓡 4)) e.sp4MissionPullbackChartedSpace _ σ
    (e.sp4MissionPullbackStructomorph (contDiffGroupoid ∞ (𝓡 4)))
  exact ⟨στ.sp4MissionToDiffeomorph⟩

theorem spc4_implies_spc4Pullback (h : SPC4) : SPC4Pullback := by
  intro N _ _ _ cs _ e
  obtain ⟨φ⟩ := h N ⟨e⟩
  exact ⟨@Structomorph.trans (EuclideanSpace ℝ (Fin 4)) N S4 N _ _ cs _ _
    (contDiffGroupoid ∞ (𝓡 4)) _ e.sp4MissionPullbackChartedSpace
    φ.sp4MissionToStructomorph
    (@Structomorph.symm (EuclideanSpace ℝ (Fin 4)) N S4 _ _
      e.sp4MissionPullbackChartedSpace _ (contDiffGroupoid ∞ (𝓡 4)) _
      (e.sp4MissionPullbackStructomorph (contDiffGroupoid ∞ (𝓡 4))))⟩

end

end SP4Mission

open scoped Manifold ContDiff
open SP4Mission in
theorem solution : SPC4 ↔ SPC4Pullback :=
  ⟨spc4_implies_spc4Pullback, spc4Pullback_implies_spc4⟩
