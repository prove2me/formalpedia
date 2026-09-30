-- Prove2me | solution 1 for ResearchGeometry.structomorph_diffeomorph_equiv
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T06:02:56.255237+00:00
-- url     : https://prove2.me/submissions/60f92d06-f6b9-45d5-bc88-0e8235ab4893

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

theorem solution :
    ∃ e : Structomorph (contDiffGroupoid n I) M M' ≃ (M ≃ₘ^n⟮I, I⟯ M'),
      ∀ h, (e h).toHomeomorph = h.toHomeomorph := by
  let e : Structomorph (contDiffGroupoid n I) M M' ≃ (M ≃ₘ^n⟮I, I⟯ M') :=
    { toFun := Structomorph.sp4MissionToDiffeomorph
      invFun := Diffeomorph.sp4MissionToStructomorph
      left_inv := by
        intro h
        cases h
        rfl
      right_inv := by
        intro d
        apply Diffeomorph.toEquiv_injective
        rfl }
  exact ⟨e, fun _ => rfl⟩
