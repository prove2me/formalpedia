-- Prove2me | solution 1 for Set.PairwiseDisjoint.injOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:51:32.051323+00:00
-- url     : https://prove2.me/submissions/87662a4e-a815-4e96-957f-33293095bd3c

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity

set_option autoImplicit true
@[expose] public section
public section
namespace Set.PairwiseDisjoint
theorem _root_.solution {ι α : Type*} [Lattice α] [OrderBot α] {f : ι → α}
    {s : Set ι} (h : s.PairwiseDisjoint f) (hne : ∀ i ∈ s, f i ≠ ⊥) : s.InjOn f := by
  intro i hi j hj hij
  by_contra hij'
  have hd : Disjoint (f i) (f j) := h hi hj hij'
  rw [← hij] at hd
  exact hne i hi (disjoint_self.1 hd)
end Set.PairwiseDisjoint
