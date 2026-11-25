-- Prove2me | solution 1 for ReciprocityTheory.Coh.FiniteLevelCohomology.torsion_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:03:33.914846+00:00
-- url     : https://prove2.me/submissions/5bc60687-3986-4e5f-8459-edbfacc832de

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ResNormalHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiniteLevel
import Theorems.Thm_ReciprocityTheory_Coh_FiniteLevelCohomology_H_succ_trivial
import Theorems.Thm_ReciprocityTheory_Coh_cor_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Topology
open scoped Pointwise
universe u
open ReciprocityTheory.Coh.FiniteLevelCohomology
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace ReciprocityTheory.Coh.FiniteLevelCohomology
theorem _root_.solution {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [DiscreteTopology H] [Finite H] (Q : TRep R H) (m : ℕ) (y : Q.H (m + 1)) :
    Nat.card H • y = 0 := by
  have : Subsingleton (⊥ : Subgroup H) :=
    ⟨fun a b => Subtype.ext ((Subgroup.mem_bot.1 a.2).trans (Subgroup.mem_bot.1 b.2).symm)⟩
  obtain ⟨cor, -, hcor⟩ := cor_holds R H Q ⊥ (isOpen_discrete _)
  have h := hcor (m + 1) y
  rw [H_succ_trivial _ m ((Pair.res Q (⊥ : Subgroup H).subtype continuous_subtype_val).hom.H (m + 1) y),
    map_zero, Subgroup.index_bot] at h
  exact h.symm
end ReciprocityTheory.Coh.FiniteLevelCohomology
