-- Prove2me | solution 1 for ReciprocityTheory.Coh.FiniteLevelCohomology.H_succ_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:17:49.559514+00:00
-- url     : https://prove2.me/submissions/21be3ea5-6817-4300-bd0f-868a47093ea8

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ResNormalHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiniteLevel
import Theorems.Thm_ReciprocityTheory_Coh_FiniteLevelCohomology_dn_subsingleton

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
theorem _root_.solution {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [Subsingleton K] (M : TRep R K) (m : ℕ) (z : M.H (m + 1)) : z = 0 := by
  classical
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [Submodule.Quotient.mk_eq_zero]
  have hwf : ∀ g, dn M.rho (m + 1) w.1.1 g = 0 := fun g => by
    have h := congrArg (fun x : M.coch.X (m + 1 + 1) => x.1 g) w.2
    exact h
  show (w : M.coch.X (m + 1)) ∈ LinearMap.range (M.coch.d m)
  rcases Nat.even_or_odd m with hm | hm
  · have h1 : w.1.1 (fun _ => 1) = 0 := by
      have h := hwf (fun _ => 1)
      rwa [dn_subsingleton, if_neg (Nat.even_add_one.not.mpr (not_not.mpr hm)), one_smul] at h
    refine ⟨0, ?_⟩
    rw [map_zero]
    symm
    apply Subtype.ext
    funext g
    show w.1.1 g = 0
    rw [Subsingleton.elim g (fun _ => 1)]
    exact h1
  · refine ⟨⟨fun _ => w.1.1 (fun _ => 1), ?_⟩, ?_⟩
    · exact continuous_const
    · apply Subtype.ext
      funext g
      show dn M.rho m (fun _ => w.1.1 (fun _ => 1)) g = w.1.1 g
      rw [dn_subsingleton, if_neg (Nat.not_even_iff_odd.mpr hm), one_smul]
      rw [Subsingleton.elim g (fun _ => 1)]
end ReciprocityTheory.Coh.FiniteLevelCohomology
