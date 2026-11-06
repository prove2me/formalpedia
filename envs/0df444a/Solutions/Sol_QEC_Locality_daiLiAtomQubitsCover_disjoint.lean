-- Prove2me | solution 1 for QEC.Locality.daiLiAtomQubitsCover_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:52:33.919048+00:00
-- url     : https://prove2.me/submissions/e04af3b8-65df-4ecb-b642-9b314959ae72

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
    (first second : List (ℝ × ℝ))
    (hDisjoint : ∀ firstAtom ∈ first, ∀ secondAtom ∈ second,
      Disjoint (daiLiAtomQubits embedding left right firstAtom)
        (daiLiAtomQubits embedding left right secondAtom)) :
    Disjoint (daiLiAtomQubitsCover embedding left right first)
      (daiLiAtomQubitsCover embedding left right second) := by
  apply Finset.disjoint_left.mpr
  intro q hFirst hSecond
  rcases (mem_daiLiAtomQubitsCover embedding left right first q).1 hFirst with
    ⟨firstAtom, hFirstAtom, hqFirst⟩
  rcases (mem_daiLiAtomQubitsCover embedding left right second q).1 hSecond with
    ⟨secondAtom, hSecondAtom, hqSecond⟩
  exact (Finset.disjoint_left.mp (hDisjoint firstAtom hFirstAtom secondAtom hSecondAtom))
    hqFirst hqSecond
end QEC.Locality
