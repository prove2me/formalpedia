-- Prove2me | solution 1 for QEC.Coding.BDL26BareLogicalPair.logicalZ_normalizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T07:26:00.824323+00:00
-- url     : https://prove2.me/submissions/9f0ebbcf-38e5-4006-98ee-d80d365da05b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BareLogicalPair
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_partnerWord_kernel
import Theorems.Thm_QEC_Coding_PauliSymplectic_inBinaryNormalizer_binaryCSSStabilizerCodeOfParityChecks_iff


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BareLogicalPair
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian
open scoped BigOperators
variable (S : OddScale) (m : Nat)
namespace QEC.Coding.BDL26BareLogicalPair
theorem _root_.solution : (stabilizer S m).InBinaryNormalizer (logicalZ S m) := by
  apply (inBinaryNormalizer_binaryCSSStabilizerCodeOfParityChecks_iff
    (zSyndrome S m) (xSyndrome S m) (row_orthogonal S m) _).mpr
  constructor
  · change zSyndrome S m 0 = 0
    exact map_zero _
  · change xSyndrome S m (partnerWord S m) = 0
    exact partnerWord_kernel S m
end QEC.Coding.BDL26BareLogicalPair
