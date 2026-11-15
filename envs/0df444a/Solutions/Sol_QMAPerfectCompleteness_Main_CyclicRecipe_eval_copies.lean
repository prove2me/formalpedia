-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.CyclicRecipe.eval_copies
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:53:12.15143+00:00
-- url     : https://prove2.me/submissions/c3783cae-04a8-405e-b349-fdb9632534f4

/- Generated from Solutions.CyclicRecipePreparation by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockClockCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockImplements
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockLogicalActions
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockLogicalSelect
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockProgramPlacement
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockStateCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockTaggedActions
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockVerifierCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanFraming
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateBlockCompilerCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateBlockCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateClosingActions
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateClosingCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateEtaTransport
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateHadamardCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateHistoryCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateHistoryPrograms
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateInitialization
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateLogicalSelect
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterHistory
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterReadout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMixture
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateOldPrograms
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificatePostCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificatePreparation
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateQuantumTransports
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateRangeCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateReadout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateStageActions
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateThresholdLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateValidity
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateValidityCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateValidityPreparation
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateVerifierCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateVerifierLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitRecipe
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentAcceptance
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentCertificate
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentReadout
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicRawCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicRawCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicRawLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicRecipe
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicVerifier
import Definitions.Def_QMAPerfectCompleteness_Proof_Dyadic
import Definitions.Def_QMAPerfectCompleteness_Proof_DynamicBlockCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_DynamicRangeLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_IndexHadamards
import Definitions.Def_QMAPerfectCompleteness_Proof_PointwiseSetup
import Definitions.Def_QMAPerfectCompleteness_Proof_PolyTimeComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_RawArithmeticGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCertificateGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_RawControlGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RawG2Gadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RawThresholdGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeNormalization
import Definitions.Def_QMAPerfectCompleteness_Proof_RegisterCopies
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_ThresholdLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_ThresholdPreparation
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableAddition
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableComparison
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableHistoryEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierAnalysis
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.Certificate
end QMAPerfectCompleteness.Main.Certificate
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof
namespace QMAPerfectCompleteness.Main.BlockComposition
end QMAPerfectCompleteness.Main.BlockComposition
namespace QMAPerfectCompleteness.Main.BlockTransport
end QMAPerfectCompleteness.Main.BlockTransport
namespace QMAPerfectCompleteness.Main.BlockHistoryCoordinates
end QMAPerfectCompleteness.Main.BlockHistoryCoordinates
namespace QMAPerfectCompleteness.Main.BlockHadamardCoordinates
end QMAPerfectCompleteness.Main.BlockHadamardCoordinates
namespace QMAPerfectCompleteness.Main.CoordinateFibers
end QMAPerfectCompleteness.Main.CoordinateFibers
namespace QMAPerfectCompleteness.Main.CertificateClaimBits
end QMAPerfectCompleteness.Main.CertificateClaimBits
namespace QMAPerfectCompleteness.Main.CertificateReadoutEffect
end QMAPerfectCompleteness.Main.CertificateReadoutEffect
namespace QMAPerfectCompleteness.Main.CertificateVerifierEffect
end QMAPerfectCompleteness.Main.CertificateVerifierEffect

/- Inline helpers retained from Solutions.RecipeGadgets. -/
section


/-! Finite recipes realizing the linear reversible circuit templates. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace QMAPerfectCompleteness.Main.CircuitRecipe

namespace Expr

@[simp] theorem eval_plug (e v : Expr) (env : Environment) (ctx : List ℕ) (w : ℕ) :
    (e.plug v).eval env ctx w=e.eval env ctx (v.eval env ctx w) := by
  induction e <;> simp_all [plug,eval]
end Expr

namespace Gadgets
open RawG2 RawEncoding





@[simp] theorem eval_add (a b : Expr) (env : Environment) (ctx : List ℕ) (w : ℕ) :
    (a+b).eval env ctx w=a.eval env ctx w+b.eval env ctx w := rfl
@[simp] theorem eval_sub (a b : Expr) (env : Environment) (ctx : List ℕ) (w : ℕ) :
    (a-b).eval env ctx w=a.eval env ctx w-b.eval env ctx w := rfl
@[simp] theorem eval_nat (n : ℕ) (env : Environment) (ctx : List ℕ) (w : ℕ) :
    (OfNat.ofNat n : Expr).eval env ctx w=n := rfl






@[simp] theorem eval_cn (a b : Expr) (env : Environment) (ctx : List ℕ) (src) :
    (cn a b).eval env ctx src=[RawG2.cn (a.eval env ctx) (b.eval env ctx)] := rfl




/-- Match the syntactic finite index enumeration with the loop counter enumeration. -/
theorem finRange_val (n : ℕ) : (List.finRange n).map Fin.val=List.range n := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

















































































end Gadgets
end QMAPerfectCompleteness.Main.CircuitRecipe

end

/- Inline helpers retained from Solutions.CyclicRecipeCorrectness. -/
section


/-! Exact realization of the coherent verifier by a finite circuit-generator recipe. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace QMAPerfectCompleteness.Main.CyclicRecipe
open CircuitRecipe CircuitRecipe.Gadgets RawEncoding RawG2





@[simp] theorem eval_k (P : CyclicRaw.Meta) (ctx : List ℕ) (w : ℕ) :
    k.eval P.env ctx w=P.k := rfl






















@[simp] theorem eval_word (P : CyclicRaw.Meta) (d : ℕ) (ctx : List ℕ) (w : ℕ) :
    (word d).eval P.env ctx w=P.word d w := rfl
@[simp] theorem eval_cert (P : CyclicRaw.Meta) (d : ℕ) (ctx : List ℕ) (w : ℕ) :
    (cert d).eval P.env ctx w=P.certificate d w := rfl




























end QMAPerfectCompleteness.Main.CyclicRecipe

end



/-! The finite arithmetic prefix recipe matches the proved clean adder circuits. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace QMAPerfectCompleteness.Main.CyclicRecipe
end QMAPerfectCompleteness.Main.CyclicRecipe
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.CyclicRecipe
open CircuitRecipe CircuitRecipe.Gadgets RawEncoding RawG2

lemma QMAPerfectCompleteness.Main.CyclicRecipe.copyIndex_eq {k : ℕ} (j : Fin (4*k)) (d : Fin 4) (i : Fin k)
    (h : j.val=i.val+k*d.val) : finProdFinEquiv.symm j=(d,i) := by
  apply finProdFinEquiv.injective
  rw [finProdFinEquiv.apply_symm_apply]
  exact Fin.ext h

@[simp] theorem solution (P : CyclicRaw.Meta) (ctx : List ℕ) (src) :
    copies.eval P.env ctx src=RawG2.compile (RawG2.thresholdCopies P.thresholds) := by
  simp only [copies,Recipe.eval,Expr.eval,eval_k,Expr.eval_lift,eval_cn,Expr.eval_plug,
    eval_sub,eval_add,eval_nat,eval_cert,eval_word,List.getElem?_cons_zero,Option.getD_some,
    CyclicRaw.Meta.env]
  rw [←finRange_val,List.flatMap_map]
  unfold RawG2.compile RawG2.thresholdCopies ThresholdPreparation.Layout.copyIndices
  rw [List.map_map,List.map_map]
  conv_rhs => rw [List.map_eq_flatMap]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro j _
  by_cases h0 : j.val<P.k
  · have he := copyIndex_eq j 0 ⟨j.val,h0⟩ (by simp)
    simp only [h0,if_true,Function.comp_def,he]
    rfl
  · by_cases h1 : j.val<2*P.k
    · have hi : j.val-P.k<P.k := by omega
      have he := copyIndex_eq j 1 ⟨j.val-P.k,hi⟩ (by simp; omega)
      simp only [h0,if_false,h1,if_true,Function.comp_def,he]
      norm_num [RawG2.compileCommand,CyclicRaw.Meta.thresholds,ThresholdPreparation.Layout.targetPosition]
    · by_cases h2 : j.val<3*P.k
      · have hi : j.val-2*P.k<P.k := by omega
        have he := copyIndex_eq j 2 ⟨j.val-2*P.k,hi⟩ (by norm_num; omega)
        simp only [h0,if_false,h1,h2,if_true,Function.comp_def,he]
        norm_num [RawG2.compileCommand,CyclicRaw.Meta.thresholds,ThresholdPreparation.Layout.targetPosition]
      · have hi : j.val-3*P.k<P.k := by have := j.isLt; omega
        have he := copyIndex_eq j 3 ⟨j.val-3*P.k,hi⟩ (by norm_num; omega)
        simp only [h0,if_false,h1,h2,Function.comp_def,he]
        norm_num [RawG2.compileCommand,CyclicRaw.Meta.thresholds,ThresholdPreparation.Layout.targetPosition]
