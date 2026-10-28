-- Prove2me | solution 2 for SchrijverSFM.Ring.ring_family_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T10:19:55.122989+00:00
-- url     : https://prove2.me/submissions/3caa4b80-ddfd-431c-a468-81442fcee572

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SchrijverSFM_Ring_Setting
import Theorems.Thm_SchrijverSFM_Ring_g_submodular

-- carved verbatim out of submission cfa24019-2442-47c9-8608-1639026a3865, lines 319-328

section
open SchrijverSFM
open SchrijverSFM.Ring
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

theorem cl_spec (C : Set (Finset V)) (hC : IsRingFamily C)
    (hu : Finset.univ ∈ C) (X : Finset V) :
    closure C X ∈ C ∧ X ⊆ closure C X ∧ ∀ Y ∈ C, X ⊆ Y → closure C X ⊆ Y := by
  classical
  refine ⟨inf_mem C hC hu _ (by simp_all), ?_, ?_⟩
  · exact Finset.le_inf fun Y hY => (Finset.mem_filter.mp hY).2.2
  · intro Y hY hXY
    exact Finset.inf_le (by simp [hY, hXY])

theorem cl_eq (C : Set (Finset V)) (hC : IsRingFamily C)
    (hu : Finset.univ ∈ C) {X : Finset V} (hX : X ∈ C) : closure C X = X :=
  Finset.Subset.antisymm ((cl_spec C hC hu X).2.2 X hX (by rfl)) (cl_spec C hC hu X).2.1

theorem c_mono (C : Set (Finset V)) (f : Finset V → ℝ) {X Y : Finset V}
    (hXY : X ⊆ Y) : csum C f X ≤ csum C f Y := by
  classical
  exact Finset.sum_le_sum_of_subset_of_nonneg hXY (fun v _ _ => le_max_left _ _)

theorem minimizer_transfer {V : Type} [Fintype V] [DecidableEq V]
    (C : Set (Finset V)) (hC : IsRingFamily C) (huniv : Finset.univ ∈ C)
    (f : Finset V → ℝ) (U : Finset V)
    (hU : ∀ W : Finset V, g C f U - csum C f U ≤ g C f W - csum C f W) :
    closure C U ∈ C ∧ ∀ T ∈ C, f (closure C U) ≤ f T := by
  refine ⟨(cl_spec C hC huniv U).1, ?_⟩
  intro T hT
  have hm := c_mono C f (cl_spec C hC huniv U).2.1
  have h := hU T
  unfold g at h
  rw [cl_eq C hC huniv hT] at h
  linarith

theorem ring_family_reduction {V : Type} [Fintype V] [DecidableEq V]
    (C : Set (Finset V)) (hC : IsRingFamily C) (hempty : ∅ ∈ C) (huniv : Finset.univ ∈ C)
    (hM : ∀ u v : V, u ≠ v → M C u ≠ M C v) (f : Finset V → ℝ) (hf : SubmodularOn C f) :
    NonmonotoneSubmod.Shared.Submodular (g C f) ∧
      ∀ U : Finset V, (∀ W : Finset V, g C f U - csum C f U ≤ g C f W - csum C f W) →
        closure C U ∈ C ∧ ∀ T ∈ C, f (closure C U) ≤ f T := by
  exact ⟨g_submodular C hC hempty huniv hM f hf, minimizer_transfer C hC huniv f⟩

end

section
open SchrijverSFM.Ring

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (C : Set (Finset V)) (hC : IsRingFamily C) (hempty : ∅ ∈ C) (huniv : Finset.univ ∈ C)
    (hM : ∀ u v : V, u ≠ v → M C u ≠ M C v) (f : Finset V → ℝ) (hf : SubmodularOn C f) :
    NonmonotoneSubmod.Shared.Submodular (g C f) ∧
      ∀ U : Finset V, (∀ W : Finset V, g C f U - csum C f U ≤ g C f W - csum C f W) →
        closure C U ∈ C ∧ ∀ T ∈ C, f (closure C U) ≤ f T :=
  ring_family_reduction C hC hempty huniv hM f hf

end
