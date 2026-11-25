-- Prove2me | solution 1 for ReciprocityTheory.Coh.FiniteLevelCohomology.dn_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:06:01.805916+00:00
-- url     : https://prove2.me/submissions/b62a9f75-c992-479a-8cfe-9d2b6efec3fd

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ResNormalHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiniteLevel
import Theorems.Thm_ReciprocityTheory_Coh_FiniteLevelCohomology_sum_neg_one_pow
import Theorems.Thm_ReciprocityTheory_Gal_dn_apply


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
theorem _root_.solution {K : Type u} [Group K] [TopologicalSpace K] [Subsingleton K]
    (M : TRep R K) (k : ℕ) (f : (Fin k → K) → M.V) (g : Fin (k + 1) → K) :
    dn M.rho k f g = (if Even k then (0 : R) else 1) • f (fun _ => 1) := by
  have e : ∀ x : Fin k → K, f x = f (fun _ => 1) := fun x => congrArg f (Subsingleton.elim _ _)
  have hs : (∑ j : Fin (k + 1), (-1 : R) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g)) =
      ∑ j : Fin (k + 1), (-1 : R) ^ ((j : ℕ) + 1) • f (fun _ => 1) :=
    Finset.sum_congr rfl fun j _ => by rw [e (Fin.contractNth j (· * ·) g)]
  rw [dn_apply, Subsingleton.elim (g 0) 1, map_one, e (fun i => g i.succ), hs, ← Finset.sum_smul,
    ← sum_neg_one_pow k, add_smul, one_smul]
  rfl
end ReciprocityTheory.Coh.FiniteLevelCohomology
