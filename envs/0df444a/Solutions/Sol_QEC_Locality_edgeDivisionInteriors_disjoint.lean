-- Prove2me | solution 1 for QEC.Locality.edgeDivisionInteriors_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:21:23.40703+00:00
-- url     : https://prove2.me/submissions/e053c634-e479-4826-ada3-46f4a39d0f97

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
import Theorems.Thm_QEC_Locality_mem_edgeDivisionSharedBoundary_iff

set_option autoImplicit false
open QEC QEC.Locality
open QEC Semantics Coding
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution {m : Type w} [DecidableEq m]
    (regions : m → Finset (ι × ι)) (active : Finset m)
    {i j : m} (hi : i ∈ active) (hj : j ∈ active) (hij : i ≠ j) :
    Disjoint (edgeDivisionInterior regions active i)
      (edgeDivisionInterior regions active j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  have hxi' := Finset.mem_sdiff.mp hxi
  have hxj' := Finset.mem_sdiff.mp hxj
  exact hxi'.2 ((mem_edgeDivisionSharedBoundary_iff regions active x).2
    ⟨i, hi, j, hj, hij, hxi'.1, hxj'.1⟩)
end QEC.Locality
