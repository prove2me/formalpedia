-- Prove2me | solution 1 for ThompsonAmenability.not_isAmenable_H_bot
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T08:32:25.607711+00:00
-- url     : https://prove2.me/submissions/38b8c230-5eb3-469d-a491-b3fbb49317b3

import Mathlib
import Definitions.Def_Garrido_Amenability
import Definitions.Def_CannonFloydParry
import Definitions.Def_Monod_PiecewiseProjective
import Theorems.Thm_Garrido_isAmenable_subgroup
import Theorems.Thm_ThompsonAmenability_not_isAmenable_F
import Theorems.Thm_ThompsonAmenability_exists_injective_monoidHom_F_H_bot

namespace ThompsonAmenability.P12

open scoped Pointwise

/-- Amenability transfers backwards along a group isomorphism. -/
theorem isAmenable_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : H ≃* G)
    (hG : Garrido.IsAmenable G) : Garrido.IsAmenable H := by
  obtain ⟨m, ⟨h0, hadd⟩, h1, hinv⟩ := hG
  refine ⟨fun s => m (e '' s), ⟨by simpa using h0, ?_⟩, ?_, ?_⟩
  · intro s t hst
    simp only [Set.image_union]
    exact hadd _ _ ((Set.disjoint_image_iff e.injective).2 hst)
  · simpa [Set.image_univ_of_surjective e.surjective] using h1
  · intro g s
    show m (e '' (g • s)) = m (e '' s)
    rw [show e '' (g • s) = e g • (e '' s) from Set.image_smul_distrib e g s]
    exact hinv _ _

theorem not_isAmenable_H_bot' : ¬ Garrido.IsAmenable (Monod.H ⊥) := by
  intro hH
  obtain ⟨φ, hφ⟩ := ThompsonAmenability.exists_injective_monoidHom_F_H_bot
  exact ThompsonAmenability.not_isAmenable_F
    (isAmenable_of_mulEquiv (MonoidHom.ofInjective hφ) (Garrido.isAmenable_subgroup hH _))

end ThompsonAmenability.P12

theorem solution : ¬ Garrido.IsAmenable (Monod.H ⊥) :=
  ThompsonAmenability.P12.not_isAmenable_H_bot'
