-- Prove2me | solution 1 for QEC.Locality.daiLiAtomQubits_subset_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:47:29.688477+00:00
-- url     : https://prove2.me/submissions/45f2b9fe-b2e9-44ab-bd03-190b2077e49b

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Theorems.Thm_QEC_Locality_mem_daiLiAtomQubitsCover

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
    (embedding : UnitSeparatedEmbedding2D ι) (left right : ℝ)
    (atoms : List (ℝ × ℝ)) (atom : ℝ × ℝ) (hAtom : atom ∈ atoms) :
    daiLiAtomQubits embedding left right atom ⊆
      daiLiAtomQubitsCover embedding left right atoms := by
  intro q hq
  exact (mem_daiLiAtomQubitsCover embedding left right atoms q).2 ⟨atom, hAtom, hq⟩
end QEC.Locality
