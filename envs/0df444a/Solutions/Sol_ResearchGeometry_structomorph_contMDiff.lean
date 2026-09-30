-- Prove2me | solution 1 for ResearchGeometry.structomorph_contMDiff
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T06:02:09.410712+00:00
-- url     : https://prove2.me/submissions/3316daaf-e78e-4b8f-a93e-280518242c83

import Definitions.Def_SP4TransportBridge

set_option autoImplicit false

open Set ChartedSpace
open scoped Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
  {n : ℕ∞ω} [hM : IsManifold I n M] [hM' : IsManifold I n M']

include hM hM'

theorem solution (h : Structomorph (contDiffGroupoid n I) M M') :
    ContMDiff I I n h.toHomeomorph := by
  exact h.sp4MissionContMDiff
