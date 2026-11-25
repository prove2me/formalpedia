-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2.exists_normal_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:48:20.152516+00:00
-- url     : https://prove2.me/submissions/057c990a-0c72-432b-a238-d914eed2bfaf

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HomFInjective
import Definitions.Def_ReciprocityTheory_GroupCohomology_ResNormalHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_Shapiro
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_SubsingletonHOfSubsingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
open ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationRestrictionInvariants ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {G' : Type u} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
theorem _root_.solution {H : Type*} [Group H] [Finite H] [Nontrivial H] (l : ℕ) [hl : Fact l.Prime]
    (hH : IsPGroup l H) : ∃ N : Subgroup H, N.Normal ∧ N.index = l := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hH
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact absurd hk (Finite.one_lt_card (α := H)).ne'
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := H) l (n := j) (by rw [hk]; exact pow_dvd_pow _ (Nat.le_succ j))
  have hidx : K.index = l := by
    have := K.card_mul_index
    rw [hK, hk, pow_succ] at this
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hl.1.pos j) this
  refine ⟨K, Subgroup.normal_of_index_eq_minFac_card ?_, hidx⟩
  rw [hidx, hk, Nat.Prime.pow_minFac hl.1 (Nat.succ_ne_zero j)]
end ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
