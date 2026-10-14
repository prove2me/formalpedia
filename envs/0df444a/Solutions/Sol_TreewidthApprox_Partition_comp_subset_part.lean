-- Prove2me | solution 1 for TreewidthApprox.Partition.comp_subset_part
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:28:06.876186+00:00
-- url     : https://prove2.me/submissions/4c717ea9-42bd-4d0e-a4ed-eee3843ec27e

import Mathlib
import Definitions.Def_TreewidthApprox_Partition_Setting

open TreewidthApprox.Partition TreewidthApprox.Pushed

private theorem reach_stays {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (X M : Finset V)
    (hc : ∀ a ∈ M, ∀ b ∉ X, G.Adj a b → b ∈ M) :
    ∀ u ∈ M, avoidComp G X u ⊆ M := by
  classical
  have hw : ∀ {u v : V} (p : G.Walk u v), u ∈ M →
      (∀ w ∈ p.support, w ∉ X) → v ∈ M := by
    intro u v p
    induction p with
    | nil => intro hu h; exact hu
    | @cons u v w huv p ih =>
      intro hu h
      apply ih
      · exact hc u hu v (h v (by simp)) huv
      · intro z hz
        exact h z (by simp [hz])
  intro u hu v hv
  obtain ⟨p,hp⟩ := (Finset.mem_filter.mp hv).2
  exact hw p hu hp

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (X M₁ M₂ M₃ : Finset V)
    (hpart : Disjoint M₁ M₂ ∧ Disjoint M₁ M₃ ∧ Disjoint M₂ M₃ ∧
      M₁ ∪ M₂ ∪ M₃ = Finset.univ \ X)
    (hedge : TreewidthApprox.Pushed.NoEdge G M₁ M₂ ∧ TreewidthApprox.Pushed.NoEdge G M₁ M₃ ∧ TreewidthApprox.Pushed.NoEdge G M₂ M₃) :
    (∀ u ∈ M₁, TreewidthApprox.Pushed.avoidComp G X u ⊆ M₁) ∧
    (∀ u ∈ M₂, TreewidthApprox.Pushed.avoidComp G X u ⊆ M₂) ∧
    (∀ u ∈ M₃, TreewidthApprox.Pushed.avoidComp G X u ⊆ M₃) := by
  classical
  have hcover (v : V) (hv : v ∉ X) : v ∈ M₁ ∨ v ∈ M₂ ∨ v ∈ M₃ := by
    have h : v ∈ M₁ ∪ M₂ ∪ M₃ := by rw [hpart.2.2.2]; simp [hv]
    simpa [or_assoc] using h
  refine ⟨reach_stays G X M₁ ?_, reach_stays G X M₂ ?_, reach_stays G X M₃ ?_⟩
  · intro a ha b hb hab
    rcases hcover b hb with h | h | h
    · exact h
    · exact (hedge.1 a ha b h hab).elim
    · exact (hedge.2.1 a ha b h hab).elim
  · intro a ha b hb hab
    rcases hcover b hb with h | h | h
    · exact (hedge.1 b h a ha hab.symm).elim
    · exact h
    · exact (hedge.2.2 a ha b h hab).elim
  · intro a ha b hb hab
    rcases hcover b hb with h | h | h
    · exact (hedge.2.1 b h a ha hab.symm).elim
    · exact (hedge.2.2 b h a ha hab.symm).elim
    · exact h
