-- Prove2me | solution 1 for QEC.Coding.BDL26BareLogicalPair.even_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:20:17.963685+00:00
-- url     : https://prove2.me/submissions/7855de46-5820-4077-8346-ad0c0e90c422

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BareLogicalPair
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_logicalZ_normalizer
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_logicalZ_not_generated
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_Xbar_Zbar_anticommute

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BareLogicalPair
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian
open scoped BigOperators
variable (S : OddScale) (m : Nat)
namespace QEC.Coding.BDL26BareLogicalPair
theorem _root_.solution (k : Nat) :
    (stabilizer S (2*k)).InBinaryNormalizer (logicalX S (2*k)) ∧
    (stabilizer S (2*k)).InBinaryNormalizer (logicalZ S (2*k)) ∧
    ¬ (stabilizer S (2*k)).InGeneratedGroupUpToSign (logicalX S (2*k)) ∧
    ¬ (stabilizer S (2*k)).InGeneratedGroupUpToSign (logicalZ S (2*k)) ∧
    Xbar S (2*k) * Zbar S (2*k) = -(Zbar S (2*k) * Xbar S (2*k)) :=
  ⟨logicalX_normalizer S (2*k), logicalZ_normalizer S (2*k), logicalX_not_generated S (2*k),
    logicalZ_not_generated S (2*k), Xbar_Zbar_anticommute S (2*k)⟩
end QEC.Coding.BDL26BareLogicalPair
