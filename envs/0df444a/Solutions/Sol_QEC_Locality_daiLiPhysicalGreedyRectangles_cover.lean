-- Prove2me | solution 1 for QEC.Locality.daiLiPhysicalGreedyRectangles_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:59:27.66082+00:00
-- url     : https://prove2.me/submissions/89f43222-cfea-4b15-9f75-f372e1bac6a7

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Theorems.Thm_QEC_Locality_DaiLiHorizontalAtomization_atomQubitsCover
import Theorems.Thm_QEC_Locality_daiLiPhysicalGreedySubdivision_join
import Theorems.Thm_QEC_Locality_daiLiPhysicalGreedySubdivision_admissible
import Theorems.Thm_QEC_Locality_daiLiPhysicalGreedySubdivision_infix
import Theorems.Thm_QEC_Locality_DaiLiHorizontalAtomization_infix_atomization
import Theorems.Thm_QEC_Locality_daiLiRectangleQubitsCover_groups

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ]
namespace QEC.Locality
theorem _root_.solution
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right ell : ℝ)
    {lower upper : ℝ} {atoms : List (ℝ × ℝ)}
    (hEll : 0 < ell)
    (hAtoms : DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding)
      ell lower upper atoms)
    (d : Nat) :
    daiLiRectangleQubitsCover embedding
        (daiLiPhysicalGreedyRectangles P embedding threshold left right d atoms) =
      embedding.qubitsInRectangle (left, lower) (right, upper) := by
  let groups := daiLiPhysicalGreedySubdivision P embedding threshold left right d atoms
  have hGroups : ∀ group ∈ groups,
      embedding.qubitsInRectangle (daiLiAtomGroupRectangle left right group).1
          (daiLiAtomGroupRectangle left right group).2 =
        daiLiAtomQubitsCover embedding left right group := by
    intro group hGroup
    have hAdmissible := daiLiPhysicalGreedySubdivision_admissible
      P embedding threshold left right d atoms group hGroup
    have hGroupAtoms := hAtoms.infix_atomization
      (daiLiPhysicalGreedySubdivision_infix P embedding threshold left right d atoms group hGroup)
      hAdmissible.1
    exact (hGroupAtoms.atomQubitsCover embedding left right hEll).symm
  change daiLiRectangleQubitsCover embedding
      (groups.map (daiLiAtomGroupRectangle left right)) = _
  calc
    _ = daiLiAtomQubitsCover embedding left right groups.flatten :=
      daiLiRectangleQubitsCover_groups embedding left right groups hGroups
    _ = daiLiAtomQubitsCover embedding left right atoms := by
      rw [daiLiPhysicalGreedySubdivision_join P embedding threshold left right d atoms]
    _ = _ := hAtoms.atomQubitsCover embedding left right hEll
end QEC.Locality
