-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.AdjacentLevelOwnerIncidence.parent_mem_of_incidence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:36:31.764547+00:00
-- url     : https://prove2.me/submissions/74526692-4e73-454a-bcaf-0b1470ab59f8

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
    (i : StepIndex depth) (u : V i.castSucc) (v : V i.succ)
    (h : A.parentIncidence i v = some u) :
    G.interLevel i u v = true :=
  (A.parentIncidence_mem_iff i u v).mp h
end QEC.Coding.MultiscaleDecoder.AdjacentLevelOwnerIncidence
