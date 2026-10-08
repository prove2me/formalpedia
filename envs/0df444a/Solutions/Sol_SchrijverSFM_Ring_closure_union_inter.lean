-- Prove2me | solution 1 for SchrijverSFM.Ring.closure_union_inter
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T01:51:59.375664+00:00
-- url     : https://prove2.me/submissions/b519a8b1-f574-4c4f-b8f4-d9978f711709

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SchrijverSFM_Ring_Setting

namespace SchrijverSFM.Ring
variable {V : Type} [Fintype V] [DecidableEq V]

theorem inf_mem (C : Set (Finset V)) (hC : IsRingFamily C)
    (hu : Finset.univ ∈ C) (s : Finset (Finset V)) (hs : ∀ Y ∈ s, Y ∈ C) :
    s.inf id ∈ C := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hu
  | @insert a s ha ih =>
    rw [Finset.inf_insert]
    exact (hC a (hs a (by simp)) (s.inf id) (ih (by aesop))).2

theorem sup_mem (C : Set (Finset V)) (hC : IsRingFamily C)
    (he : ∅ ∈ C) (s : Finset (Finset V)) (hs : ∀ Y ∈ s, Y ∈ C) :
    s.sup id ∈ C := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using he
  | @insert a s ha ih =>
    rw [Finset.sup_insert]
    exact (hC a (hs a (by simp)) (s.sup id) (ih (by aesop))).1

theorem cl_spec (C : Set (Finset V)) (hC : IsRingFamily C)
    (hu : Finset.univ ∈ C) (X : Finset V) :
    closure C X ∈ C ∧ X ⊆ closure C X ∧ ∀ Y ∈ C, X ⊆ Y → closure C X ⊆ Y := by
  classical
  refine ⟨inf_mem C hC hu _ (by simp_all), ?_, ?_⟩
  · exact Finset.le_inf fun Y hY => (Finset.mem_filter.mp hY).2.2
  · intro Y hY hXY
    exact Finset.inf_le (by simp [hY, hXY])

theorem cl_mono (C : Set (Finset V)) (hC : IsRingFamily C)
    (hu : Finset.univ ∈ C) {X Y : Finset V} (h : X ⊆ Y) : closure C X ⊆ closure C Y :=
  (cl_spec C hC hu X).2.2 _ (cl_spec C hC hu Y).1 (h.trans (cl_spec C hC hu Y).2.1)

theorem cl_eq (C : Set (Finset V)) (hC : IsRingFamily C)
    (hu : Finset.univ ∈ C) {X : Finset V} (hX : X ∈ C) : closure C X = X :=
  Finset.Subset.antisymm ((cl_spec C hC hu X).2.2 X hX (by rfl)) (cl_spec C hC hu X).2.1

theorem closure_union_inter {V : Type} [Fintype V] [DecidableEq V]
    (C : Set (Finset V)) (hC : IsRingFamily C) (huniv : Finset.univ ∈ C) :
    (∀ X : Finset V, closure C X ∈ C ∧ X ⊆ closure C X ∧
        ∀ Y ∈ C, X ⊆ Y → closure C X ⊆ Y) ∧
      ∀ X Y : Finset V, closure C X ∪ closure C Y = closure C (X ∪ Y) ∧
        closure C (X ∩ Y) ⊆ closure C X ∩ closure C Y := by
  refine ⟨cl_spec C hC huniv, ?_⟩
  intro X Y
  constructor
  · apply Finset.Subset.antisymm
    · exact Finset.union_subset (cl_mono C hC huniv Finset.subset_union_left)
        (cl_mono C hC huniv Finset.subset_union_right)
    · apply (cl_spec C hC huniv (X ∪ Y)).2.2
      · exact (hC _ (cl_spec C hC huniv X).1 _ (cl_spec C hC huniv Y).1).1
      · exact Finset.union_subset_union (cl_spec C hC huniv X).2.1 (cl_spec C hC huniv Y).2.1
  · exact Finset.subset_inter (cl_mono C hC huniv Finset.inter_subset_left)
      (cl_mono C hC huniv Finset.inter_subset_right)

end SchrijverSFM.Ring

open SchrijverSFM.Ring
theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (C : Set (Finset V)) (hC : IsRingFamily C) (huniv : Finset.univ ∈ C) :
    (∀ X : Finset V, closure C X ∈ C ∧ X ⊆ closure C X ∧
        ∀ Y ∈ C, X ⊆ Y → closure C X ⊆ Y) ∧
      ∀ X Y : Finset V, closure C X ∪ closure C Y = closure C (X ∪ Y) ∧
        closure C (X ∩ Y) ⊆ closure C X ∩ closure C Y :=
  closure_union_inter C hC huniv
#print axioms solution
