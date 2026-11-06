-- Prove2me | solution 2 for QEC.Locality.ProfileSeparatorRecursion.mem_leaves_card_le
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:29:51.8747+00:00
-- url     : https://prove2.me/submissions/7916d768-3a11-440d-b3d6-b34fe604e315

import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_Recursion
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem solution
    {G : ConnectivityGraph ι} {r : Nat} {vertices leaf : Finset ι}
    (tree : ProfileSeparatorRecursion G r vertices) (hleaf : leaf ∈ tree.leaves) :
    leaf.card ≤ r := by
  induction tree with
  | leaf hcard =>
    simp only [ProfileSeparatorRecursion.leaves] at hleaf
    split_ifs at hleaf with h
    · simp at hleaf
    · simp at hleaf
      subst hleaf
      exact hcard
  | split hpartition hminimum hleft hright leftTree rightTree ihl ihr =>
    simp only [ProfileSeparatorRecursion.leaves, List.mem_append] at hleaf
    rcases hleaf with h | h
    · exact ihl h
    · exact ihr h
