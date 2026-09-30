-- Prove2me | solution 1 for ResearchGeometry.homeomorph_structomorph_iff
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T06:02:22.691403+00:00
-- url     : https://prove2.me/submissions/0d87fef6-f303-4b19-b635-a809aa811262

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

theorem solution (e : M ≃ₜ M') :
    (∃ h : Structomorph (contDiffGroupoid n I) M M', h.toHomeomorph = e) ↔
    ContMDiff I I n e ∧ ContMDiff I I n e.symm := by
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h.sp4MissionContMDiff, h.symm.sp4MissionContMDiff⟩
  · rintro ⟨hf, hg⟩
    let d : M ≃ₘ^n⟮I, I⟯ M' :=
      { toEquiv := e.toEquiv, contMDiff_toFun := hf, contMDiff_invFun := hg }
    exact ⟨d.sp4MissionToStructomorph, rfl⟩
