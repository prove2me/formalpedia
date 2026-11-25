-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.exists_finset_inf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:01:13.253916+00:00
-- url     : https://prove2.me/submissions/9c8aa725-b178-4fcc-9510-dc7fe092f9fd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_KerCoreSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_DescPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FunKerPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_KerCorePf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped TensorProduct
open TensorProduct
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
theorem _root_.solution {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (S : Set (Submodule K V)) : ∃ t : Finset (Submodule K V), (t : Set _) ⊆ S ∧ ∀ N ∈ S, t.inf id ≤ N := by
  classical
  have hwf : WellFoundedLT (Submodule K V) := inferInstance
  obtain ⟨N0, ⟨t0, ht0S, rfl⟩, hmin⟩ := hwf.wf.has_min
    {N | ∃ t : Finset (Submodule K V), (t : Set (Submodule K V)) ⊆ S ∧ N = t.inf id}
    ⟨⊤, ∅, by simp, by simp⟩
  refine ⟨t0, ht0S, fun N hN => ?_⟩
  have hmem : (insert N t0).inf id ∈
      {N | ∃ t : Finset (Submodule K V), (t : Set (Submodule K V)) ⊆ S ∧ N = t.inf id} :=
    ⟨insert N t0, by
      rw [Finset.coe_insert, Set.insert_subset_iff]
      exact ⟨hN, ht0S⟩, rfl⟩
  have hle : (insert N t0).inf id ≤ t0.inf id := Finset.inf_mono (Finset.subset_insert _ _)
  have heq : (insert N t0).inf id = t0.inf id := eq_of_le_of_not_lt hle (hmin _ hmem)
  rw [Finset.inf_insert] at heq
  calc t0.inf id = N ⊓ t0.inf id := heq.symm
    _ ≤ N := inf_le_left
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
