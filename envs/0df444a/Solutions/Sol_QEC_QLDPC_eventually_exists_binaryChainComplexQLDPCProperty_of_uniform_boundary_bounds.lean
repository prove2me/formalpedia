-- Prove2me | solution 1 for QEC.QLDPC.eventually_exists_binaryChainComplexQLDPCProperty_of_uniform_boundary_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:09:42.700808+00:00
-- url     : https://prove2.me/submissions/46e59f4a-bf7e-49fb-b36d-98b91e0f07a7

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QLDPC_Core
import Theorems.Thm_QEC_QLDPC_exists_binaryChainComplexQLDPCProperty_of_boundary_bounds

set_option autoImplicit false
open QEC
universe u v w x
open scoped Classical
open QEC.QLDPC
namespace QEC.QLDPC
theorem _root_.solution
    {ι κ lambda : Nat → Type u}
    [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    [∀ n, Fintype (κ n)] [∀ n, Fintype (lambda n)]
    (validIndex : Nat → Prop) (start : Nat)
    (K : ∀ n, Coding.ChainComplexData
      (ZMod 2) (Coding.Word (ZMod 2) (κ n))
      (Coding.Word (ZMod 2) (ι n))
      (Coding.Word (ZMod 2) (lambda n)))
    (parameters : ∀ n, Coding.CodeParameters (ZMod 2) (ι n))
    {w variableDegree : Nat}
    (hrow1 : ∀ n, start ≤ n → validIndex n → ∀ k,
      Coding.HammingWeight
        (Coding.wordLinearMapTranspose (K n).boundary1
          (Coding.canonicalBasisWord (F := ZMod 2) k)) ≤ w)
    (hrow2 : ∀ n, start ≤ n → validIndex n → ∀ l,
      Coding.HammingWeight ((K n).boundary2
        (Coding.canonicalBasisWord (F := ZMod 2) l)) ≤ w)
    (hcol : ∀ n, start ≤ n → validIndex n → ∀ q,
      ((chainComplexBoundaryIncidence (K n)).variableSupport q).card ≤ variableDegree) :
    ∀ n, start ≤ n → validIndex n →
      ∃ P : Coding.QLDPCProperty (ZMod 2) (ι n)
        (Semantics.Qubit.QubitRegister (ι n))
        (Coding.Word (ZMod 2) (κ n))
        (Coding.Word (ZMod 2) (ι n))
        (Coding.Word (ZMod 2) (lambda n)),
        P.chainCode = (K n).binaryChainComplexCode ∧
        P.parameters = parameters n ∧
        P.locality = (chainComplexBoundaryIncidence (K n)).localityProfile ∧
        P.localityBound = max w variableDegree := by
  intro n hn hvalid
  exact exists_binaryChainComplexQLDPCProperty_of_boundary_bounds
    (K n)
    (parameters n)
    (hrow1 n hn hvalid)
    (hrow2 n hn hvalid)
    (hcol n hn hvalid)
end QEC.QLDPC
