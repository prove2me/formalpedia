-- Prove2me | solution 1 for SchrijverSFM.Ring.lower_ideal_representation
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T01:52:00.35632+00:00
-- url     : https://prove2.me/submissions/b35c8252-9799-4fa2-befb-d292d81c84b5

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


theorem m_spec (C : Set (Finset V)) (hC : IsRingFamily C)
    (hu : Finset.univ ∈ C) (v : V) :
    M C v ∈ C ∧ v ∈ M C v ∧ ∀ Y ∈ C, v ∈ Y → M C v ⊆ Y := by
  have h := cl_spec C hC hu {v}
  simpa [M, Finset.singleton_subset_iff] using h

theorem m_trans (C : Set (Finset V)) (hC : IsRingFamily C)
    (hu : Finset.univ ∈ C) {u v : V} (h : u ∈ M C v) : M C u ⊆ M C v :=
  (m_spec C hC hu u).2.2 _ (m_spec C hC hu v).1 h

theorem biUnion_mem (C : Set (Finset V)) (hC : IsRingFamily C) (he : ∅ ∈ C)
    (s : Finset V) (a : V → Finset V) (ha : ∀ v ∈ s, a v ∈ C) : s.biUnion a ∈ C := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using he
  | @insert v s hv ih =>
    rw [Finset.biUnion_insert]
    exact (hC _ (ha v (by simp)) _ (ih (by aesop))).1

theorem ideals (C : Set (Finset V)) (hC : IsRingFamily C)
    (he : ∅ ∈ C) (hu : Finset.univ ∈ C) (X : Finset V) :
    X ∈ C ↔ ∀ u v, u ∈ M C v → v ∈ X → u ∈ X := by
  classical
  constructor
  · intro hX u v huv hv
    exact (m_spec C hC hu v).2.2 X hX hv huv
  · intro hX
    have heq : X.biUnion (M C) = X := by
      ext u
      simp only [Finset.mem_biUnion]
      constructor
      · rintro ⟨v, hv, huv⟩
        exact hX u v huv hv
      · intro huX
        exact ⟨u, huX, (m_spec C hC hu u).2.1⟩
    rw [← heq]
    exact biUnion_mem C hC he X (M C) (fun v _ => (m_spec C hC hu v).1)

theorem lower_ideal_representation {V : Type} [Fintype V] [DecidableEq V]
    (C : Set (Finset V)) (hC : IsRingFamily C) (hempty : ∅ ∈ C) (huniv : Finset.univ ∈ C)
    (hM : ∀ u v : V, u ≠ v → M C u ≠ M C v) :
    ∃ r : V → V → Prop,
      (∀ v, r v v) ∧ (∀ u v w, r u v → r v w → r u w) ∧ (∀ u v, r u v → r v u → u = v) ∧
      ∀ X : Finset V, X ∈ C ↔ ∀ u v, r u v → v ∈ X → u ∈ X := by
  refine ⟨fun u v => u ∈ M C v, fun v => (m_spec C hC huniv v).2.1, ?_, ?_, ideals C hC hempty huniv⟩
  · intro u v w huv hvw
    exact m_trans C hC huniv hvw huv
  · intro u v huv hvu
    by_contra hne
    exact hM u v hne (Finset.Subset.antisymm (m_trans C hC huniv huv) (m_trans C hC huniv hvu))

end SchrijverSFM.Ring
open SchrijverSFM.Ring
theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (C : Set (Finset V)) (hC : IsRingFamily C) (hempty : ∅ ∈ C) (huniv : Finset.univ ∈ C)
    (hM : ∀ u v : V, u ≠ v → M C u ≠ M C v) :
    ∃ r : V → V → Prop,
      (∀ v, r v v) ∧ (∀ u v w, r u v → r v w → r u w) ∧ (∀ u v, r u v → r v u → u = v) ∧
      ∀ X : Finset V, X ∈ C ↔ ∀ u v, r u v → v ∈ X → u ∈ X :=
  lower_ideal_representation C hC hempty huniv hM
#print axioms solution

