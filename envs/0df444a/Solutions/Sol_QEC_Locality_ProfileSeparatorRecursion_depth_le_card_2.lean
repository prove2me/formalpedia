-- Prove2me | solution 2 for QEC.Locality.ProfileSeparatorRecursion_depth_le_card
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:29:49.987009+00:00
-- url     : https://prove2.me/submissions/c52f2415-12cc-4c81-aaf9-d9a0f5238bb1

import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_Recursion
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem solution
    {G : ConnectivityGraph ι} {r : Nat} {vertices : Finset ι}
    (tree : ProfileSeparatorRecursion G r vertices) :
    tree.depth ≤ tree.root.card := by
  induction tree with
  | leaf hcard =>
    simp [ProfileSeparatorRecursion.depth]
  | @split vertices left separator right hpartition hminimum hleft hright leftTree rightTree ihl ihr =>
    simp only [ProfileSeparatorRecursion.depth, ProfileSeparatorRecursion.root] at ihl ihr ⊢
    omega
