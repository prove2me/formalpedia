-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.AdjacentLevelOwnerIncidence.correction_mem_of_owner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:36:27.621009+00:00
-- url     : https://prove2.me/submissions/a744e565-8491-4b3f-8845-fd1bbbc9b009

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Definitions.Def_QEC_Locality_Graph_Core
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale

set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.MultiscaleDecoder
open scoped BigOperators
universe u v w x y z a
variable {depth : Nat}
open BDL26CochainFamily
open QEC.Coding.MultiscaleDecoder.AdjacentLevelOwnerIncidence
variable {depth : Nat}
variable {V : LevelIndex depth → Type v}
variable [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable {SyndromeCoord : LevelIndex depth → Type w}
variable [∀ i, Fintype (SyndromeCoord i)]
  [∀ i, DecidableEq (SyndromeCoord i)]
variable {CorrectionCoord : LevelIndex depth → Type x}
variable [∀ i, Fintype (CorrectionCoord i)]
  [∀ i, DecidableEq (CorrectionCoord i)]
variable {G : DecodingGraphFamily depth V}
namespace QEC.Coding.MultiscaleDecoder.AdjacentLevelOwnerIncidence
theorem _root_.solution
    (A : AdjacentLevelOwnerIncidence depth V SyndromeCoord CorrectionCoord G)
    (i : LevelIndex depth) (c : CorrectionCoord i) (v : V i)
    (h : A.correctionOwner i c = some v) :
    c ∈ A.correctionRegion i v :=
  (A.correctionOwner_mem_iff i v c).mp h
end QEC.Coding.MultiscaleDecoder.AdjacentLevelOwnerIncidence
