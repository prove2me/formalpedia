-- Prove2me | solution 2 for QEC.Locality.ProfileSeparatorRecursion_leaves_length_le_card
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:29:50.877512+00:00
-- url     : https://prove2.me/submissions/3c14be7c-704b-4168-b541-2138e8f1896f

import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_Recursion
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem solution
    {G : ConnectivityGraph ι} {r : Nat} {vertices : Finset ι}
    (tree : ProfileSeparatorRecursion G r vertices) :
    tree.leaves.length ≤ tree.root.card := by
  induction tree with
  | leaf hcard =>
    simp only [ProfileSeparatorRecursion.leaves, ProfileSeparatorRecursion.root]
    split_ifs with h
    · simp
    · simpa using Finset.nonempty_iff_ne_empty.2 h |>.card_pos
  | @split vertices left separator right hpartition hminimum hleft hright leftTree rightTree ihl ihr =>
    simp only [ProfileSeparatorRecursion.leaves, ProfileSeparatorRecursion.root,
      List.length_append] at ihl ihr ⊢
    obtain ⟨hsub, hunion, hdisj, -, -, -⟩ := hpartition
    have h1 : left.card + right.card ≤ vertices.card := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
      exact Finset.card_le_card Finset.sdiff_subset
    omega
