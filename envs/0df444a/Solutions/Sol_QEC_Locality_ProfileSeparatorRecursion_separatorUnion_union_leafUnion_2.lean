-- Prove2me | solution 2 for QEC.Locality.ProfileSeparatorRecursion.separatorUnion_union_leafUnion
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:29:53.605767+00:00
-- url     : https://prove2.me/submissions/e14f17c3-4422-4418-8c28-e5feea58e569

import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_Recursion
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem solution
    {G : ConnectivityGraph ι} {r : Nat} {vertices : Finset ι}
    (tree : ProfileSeparatorRecursion G r vertices) :
    tree.separatorUnion ∪ tree.leafUnion = tree.root := by
  induction tree with
  | leaf hcard =>
    simp [ProfileSeparatorRecursion.separatorUnion, ProfileSeparatorRecursion.leafUnion,
      ProfileSeparatorRecursion.root]
  | @split vertices left separator right hpartition hminimum hleft hright leftTree rightTree ihl ihr =>
    simp only [ProfileSeparatorRecursion.separatorUnion, ProfileSeparatorRecursion.leafUnion,
      ProfileSeparatorRecursion.root] at ihl ihr ⊢
    obtain ⟨hsub, hunion, hdisj, -, -, -⟩ := hpartition
    ext x
    have hl := Finset.ext_iff.1 ihl x
    have hr := Finset.ext_iff.1 ihr x
    have hu := Finset.ext_iff.1 hunion x
    simp only [Finset.mem_union, Finset.mem_sdiff] at hl hr hu ⊢
    constructor
    · rintro (((h | h) | h) | h | h)
      · exact hsub h
      · have := hl.1 (Or.inl h)
        exact (hu.1 (Or.inl this)).1
      · have := hr.1 (Or.inl h)
        exact (hu.1 (Or.inr this)).1
      · have := hl.1 (Or.inr h)
        exact (hu.1 (Or.inl this)).1
      · have := hr.1 (Or.inr h)
        exact (hu.1 (Or.inr this)).1
    · intro hx
      by_cases hs : x ∈ separator
      · exact Or.inl (Or.inl (Or.inl hs))
      · have := (hu.2 ⟨hx, hs⟩)
        rcases this with h | h
        · rcases hl.2 h with h' | h'
          · exact Or.inl (Or.inl (Or.inr h'))
          · exact Or.inr (Or.inl h')
        · rcases hr.2 h with h' | h'
          · exact Or.inl (Or.inr h')
          · exact Or.inr (Or.inr h')
