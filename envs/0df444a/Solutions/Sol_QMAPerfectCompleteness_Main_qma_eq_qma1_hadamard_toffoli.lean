-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.qma_eq_qma1_hadamard_toffoli
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T17:35:14.720526+00:00
-- url     : https://prove2.me/submissions/0daa3a16-c6e6-4508-a931-74afdc02914c

/- Generated from Solutions.Sol_QMAPerfectCompleteness_Main_qma_eq_qma1_hadamard_toffoli by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Gates
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.DeriveFintype
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Proof_BinaryComposition
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
import Definitions.Def_QMAPerfectCompleteness_Proof_BoundedWriterTM
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
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitExprTM
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitProvisionalWriter
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitRecipe
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClassTransport
import Definitions.Def_QMAPerfectCompleteness_Proof_ClearStacksTM
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentAcceptance
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentCertificate
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentReadout
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ConcreteUniformity
import Definitions.Def_QMAPerfectCompleteness_Proof_ConditionalWriterTM
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_CountedWriterLoops
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicClockMetadata
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicClockPrefixTM
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicFullMetadata
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicIndexMetadataCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicIndexMetadataIO
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicIndexMetadataTM
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicMetadataTM
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicProvisionalCode
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicRawCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicRawCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicRawLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicRecipe
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicRecipeRealization
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicVerifier
import Definitions.Def_QMAPerfectCompleteness_Proof_Dyadic
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicCompilerTM
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicPreservation
import Definitions.Def_QMAPerfectCompleteness_Proof_DynamicBlockCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_DynamicRangeLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_FinitePlanCompilerTM
import Definitions.Def_QMAPerfectCompleteness_Proof_FixedBlockCopy
import Definitions.Def_QMAPerfectCompleteness_Proof_GateCompilation
import Definitions.Def_QMAPerfectCompleteness_Proof_HPToffoli
import Definitions.Def_QMAPerfectCompleteness_Proof_HTCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_HTCompilerTM
import Definitions.Def_QMAPerfectCompleteness_Proof_HTEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_HTPreservation
import Definitions.Def_QMAPerfectCompleteness_Proof_HadamardToffoli
import Definitions.Def_QMAPerfectCompleteness_Proof_IndexHadamards
import Definitions.Def_QMAPerfectCompleteness_Proof_InstructionBuffersTM
import Definitions.Def_QMAPerfectCompleteness_Proof_PointwiseSetup
import Definitions.Def_QMAPerfectCompleteness_Proof_PolyTimeComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_RawArithmeticGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCertificateGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_RawControlGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RawG2Gadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RawThresholdGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RealSimulation
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeCompositeWriters
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeLeafWriter
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeNormalization
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeSerializerContinuation
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeSerializerSetup
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeSerializerTM
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeVerifierContext
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeWriterContext
import Definitions.Def_QMAPerfectCompleteness_Proof_RecountGatesCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_RecountGatesTM
import Definitions.Def_QMAPerfectCompleteness_Proof_RegisterCopies
import Definitions.Def_QMAPerfectCompleteness_Proof_Repetition
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionCompilerBounds
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionCompilerInterface
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionCompilerTM
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionUniformity
import Definitions.Def_QMAPerfectCompleteness_Proof_ReverseCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_ReverseCompilerTM
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_SourceBuffersTM
import Definitions.Def_QMAPerfectCompleteness_Proof_SourceInstructionMapper
import Definitions.Def_QMAPerfectCompleteness_Proof_SourceWriter
import Definitions.Def_QMAPerfectCompleteness_Proof_SourceWriterBounds
import Definitions.Def_QMAPerfectCompleteness_Proof_SourceWriterTM
import Definitions.Def_QMAPerfectCompleteness_Proof_StackEmbedding
import Definitions.Def_QMAPerfectCompleteness_Proof_StackTransfers
import Definitions.Def_QMAPerfectCompleteness_Proof_StreamWriterTM
import Definitions.Def_QMAPerfectCompleteness_Proof_StructuredStackCode
import Definitions.Def_QMAPerfectCompleteness_Proof_ThresholdLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_ThresholdPreparation
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryDispatch
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryEvaluator
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryFieldCode
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryMetadataArithmetic
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryNextPowerCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryNextPowerPhases
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryNextPowerTM
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryStackOps
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableAddition
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableComparison
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableHistoryEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierAnalysis
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding
import Theorems.Thm_QMAPerfectCompleteness_Main_CircuitProof_acceptance_complement_posSemidef
import Theorems.Thm_QMAPerfectCompleteness_Main_ClassTransport_reverse
import Theorems.Thm_QMAPerfectCompleteness_Main_ClassTransport_transport
import Theorems.Thm_QMAPerfectCompleteness_Main_CyclicRecipe_class_reduction
import Theorems.Thm_QMAPerfectCompleteness_Main_DyadicCompiler_compileVerifier_acceptanceOperator
import Theorems.Thm_QMAPerfectCompleteness_Main_HTCompiler_compileVerifier_acceptanceOperator
import Theorems.Thm_QMAPerfectCompleteness_Main_Repetition_CircuitProof_acceptanceOperator_pi

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof
namespace QMAPerfectCompleteness.Uniformity.Expansion
end QMAPerfectCompleteness.Uniformity.Expansion
namespace QMAPerfectCompleteness.Main.Certificate
end QMAPerfectCompleteness.Main.Certificate
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
namespace QMAPerfectCompleteness.Uniformity.UnaryNatArithmetic
end QMAPerfectCompleteness.Uniformity.UnaryNatArithmetic

/- Inline helpers retained from Solutions.EuclideanStates. -/
section


open Matrix
open scoped ComplexOrder MatrixOrder

namespace QMAPerfectCompleteness.Main.VerifierAnalysis

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma euclidNorm_nonneg (v : ι → ℂ) : 0 ≤ euclidNorm v := Real.sqrt_nonneg _

lemma euclidNorm_sq (v : ι → ℂ) : euclidNorm v ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)















lemma pureDensity_posSemidef (v : ι → ℂ) : (pureDensity v).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star v

lemma pureDensity_trace [DecidableEq ι] (v : ι → ℂ) :
    (pureDensity v).trace = ((euclidNorm v ^ 2 : ℝ) : ℂ) := by
  rw [pureDensity, Matrix.trace_vecMulVec, euclidNorm_sq]
  simp [dotProduct, Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma pureDensity_trace_one [DecidableEq ι] (v : ι → ℂ) (hv : euclidNorm v = 1) :
    (pureDensity v).trace = 1 := by rw [pureDensity_trace, hv]; norm_num

lemma pureDensity_expectation [DecidableEq ι] (E : Matrix ι ι ℂ) (v : ι → ℂ) :
    (E * pureDensity v).trace = star v ⬝ᵥ (E *ᵥ v) := by
  rw [pureDensity, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]



/-- The trace pairing of positive matrices is nonnegative even when they do not commute. -/
lemma trace_mul_posSemidef_nonneg [DecidableEq ι] (A R : Matrix ι ι ℂ)
    (hA : A.PosSemidef) (hR : R.PosSemidef) : 0 ≤ (A * R).trace.re := by
  obtain ⟨S, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hR.nonneg
  have hp := (hA.mul_mul_conjTranspose_same S).trace_nonneg
  have ht : (S * A * Sᴴ).trace = (A * (star S * S)).trace := by
    rw [Matrix.trace_mul_cycle, star_eq_conjTranspose, Matrix.trace_mul_comm]
  rw [ht] at hp
  exact (Complex.nonneg_iff.mp hp).1



end QMAPerfectCompleteness.Main.VerifierAnalysis

end

/- Inline helpers retained from Solutions.Cyclic. -/
section


open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.CyclicProof

variable {G : GateSet}























open VerifierAnalysis











open scoped ComplexOrder

/-- Positivity of the acceptance operator follows directly from its compression formula. -/
theorem acceptance_posSemidef (V : Verifier G) : V.acceptanceOperator.PosSemidef := by
  have hp : V.acceptProjector.PosSemidef := by
    unfold Verifier.acceptProjector
    apply Matrix.PosSemidef.diagonal
    intro w
    change 0 ≤ (if w V.output then (1 : ℂ) else 0)
    split <;> simp
  have h := hp.conjTranspose_mul_mul_same (V.unitary * V.ancillaZero)
  simpa only [Verifier.acceptanceOperator, Matrix.conjTranspose_mul, Matrix.mul_assoc] using h

/-- Soundness bounds every eigenvalue, using a normalized pure eigenstate as the proof. -/
theorem acceptance_eigenvalue_le (V : Verifier G)
    (hno : V.AcceptsAllProofsAtMost (1 / 3)) (i : V.Proof) :
    (acceptance_hermitian V).eigenvalues i ≤ (1 / 3 : ℝ) := by
  let h := acceptance_hermitian V
  let v : V.Proof → ℂ := ⇑(h.eigenvectorBasis i)
  have hv : euclidNorm v = 1 := by
    have hv := h.eigenvectorBasis.orthonormal.1 i
    simpa only [EuclideanSpace.norm_eq, euclidNorm, v] using hv
  have hb := hno (pureDensity v) ⟨pureDensity_posSemidef v, pureDensity_trace_one v hv⟩
  change (V.acceptanceOperator * pureDensity v).trace.re ≤ (1 / 3 : ℝ) at hb
  rw [pureDensity_expectation] at hb
  rw [h.eigenvalues_eq]
  exact hb

open scoped Matrix.Norms.L2Operator

/-- The spectral theorem turns the eigenvalue interval [0,1/3] into a Euclidean operator bound. -/
theorem acceptance_opNorm_le (V : Verifier G)
    (hno : V.AcceptsAllProofsAtMost (1 / 3)) : ‖V.acceptanceOperator‖ ≤ (1 / 3 : ℝ) := by
  let h := acceptance_hermitian V
  rw [h.spectral_theorem, Unitary.conjStarAlgAut_apply]
  simp only [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
    CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3)).2
  intro i
  change ‖((h.eigenvalues i : ℝ) : ℂ)‖ ≤ (1 / 3 : ℝ)
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ((acceptance_posSemidef V).eigenvalues_nonneg i)]
  exact acceptance_eigenvalue_le V hno i





end QMAPerfectCompleteness.Main.CyclicProof

end

/- Inline helpers retained from Solutions.DiagonalWitness. -/
section


open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
namespace QMAPerfectCompleteness.Main.DiagonalProof
open CyclicProof VerifierAnalysis

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma psd_opNorm_le (A : Matrix ι ι ℂ) (hA : A.PosSemidef) (s : ℝ)
    (hs : 0 ≤ s) (hbound : ∀ i, hA.1.eigenvalues i ≤ s) : ‖A‖ ≤ s := by
  rw [hA.1.spectral_theorem, Unitary.conjStarAlgAut_apply]
  simp only [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
    CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg hs).2
  intro i
  change ‖((hA.1.eigenvalues i : ℝ) : ℂ)‖ ≤ s
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hA.eigenvalues_nonneg i)]
  exact hbound i

lemma quadratic_le_of_opNorm_le (A : Matrix ι ι ℂ) (s : ℝ) (hs : ‖A‖ ≤ s)
    (v : ι → ℂ) : (star v ⬝ᵥ (A *ᵥ v)).re ≤ s * euclidNorm v ^ 2 := by
  have hn (w : ι → ℂ) : ‖(WithLp.toLp 2 w : EuclideanSpace ℂ ι)‖ = euclidNorm w := by
    rw [EuclideanSpace.norm_eq]
    rfl
  have hinner := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 v : EuclideanSpace ℂ ι)
    (WithLp.toLp 2 (A *ᵥ v) : EuclideanSpace ℂ ι)
  have hmul := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 v)
  change ‖(WithLp.toLp 2 (A *ᵥ v) : EuclideanSpace ℂ ι)‖ ≤
    ‖A‖ * ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖ at hmul
  rw [hn, hn] at hmul
  rw [EuclideanSpace.inner_eq_star_dotProduct, hn, hn] at hinner
  change ‖(A *ᵥ v) ⬝ᵥ star v‖ ≤ euclidNorm v * euclidNorm (A *ᵥ v) at hinner
  rw [dotProduct_comm] at hinner
  have hre := Complex.re_le_norm (star v ⬝ᵥ (A *ᵥ v))
  have hb : euclidNorm (A *ᵥ v) ≤ s * euclidNorm v :=
    hmul.trans (mul_le_mul_of_nonneg_right hs (euclidNorm_nonneg v))
  nlinarith [euclidNorm_nonneg v]



















end QMAPerfectCompleteness.Main.DiagonalProof

end

/- Inline helpers retained from Solutions.RealSimulation. -/
section


open Matrix
open scoped ComplexOrder

namespace QMAPerfectCompleteness.Main.RealSimulation

variable {ι κ τ : Type*}







@[simp] theorem realRep_one [DecidableEq ι] : realRep (1 : Matrix ι ι ℂ) = 1 := by
  ext ⟨b, i⟩ ⟨c, j⟩
  cases b <;> cases c <;> by_cases h : i = j <;> simp [realRep, Matrix.one_apply, h]

/-- The map is multiplicative, as asserted in the proof of Lemma 3.1. -/
theorem realRep_mul [Fintype κ] (A : Matrix ι κ ℂ) (B : Matrix κ τ ℂ) :
    realRep (A * B) = realRep A * realRep B := by
  ext ⟨b, i⟩ ⟨c, j⟩
  cases b <;> cases c <;>
    simp [realRep, Matrix.mul_apply, Fintype.sum_prod_type, Complex.re_sum, Complex.im_sum,
      Complex.mul_re, Complex.mul_im, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_neg_distrib] <;> ring

/-- Adjoint becomes ordinary real transpose. -/
theorem realRep_conjTranspose (A : Matrix ι κ ℂ) : realRep Aᴴ = (realRep A)ᵀ := by
  ext ⟨b, i⟩ ⟨c, j⟩
  cases b <;> cases c <;> simp [realRep, Matrix.conjTranspose_apply, Complex.star_def]











































@[simp] theorem realRep_sub (A B : Matrix ι κ ℂ) : realRep (A - B) = realRep A - realRep B := by
  ext ⟨b, i⟩ ⟨c, j⟩
  cases b <;> cases c <;> simp [realRep] <;> ring

@[simp] theorem realRep_real_smul (r : ℝ) (A : Matrix ι κ ℂ) :
    realRep ((r : ℂ) • A) = r • realRep A := by
  ext ⟨b, i⟩ ⟨c, j⟩
  cases b <;> cases c <;> simp [realRep, Complex.mul_re, Complex.mul_im] <;> ring





open scoped Kronecker



end QMAPerfectCompleteness.Main.RealSimulation

end

/- Inline helpers retained from Solutions.DyadicCompiler. -/
section


open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.DyadicCompiler
open GateCompilation



















































lemma complexRealRep_mul {ι κ τ : Type*} [Fintype κ]
    (A : Matrix ι κ ℂ) (B : Matrix κ τ ℂ) :
    complexRealRep (A * B) = complexRealRep A * complexRealRep B := by
  unfold complexRealRep
  rw [RealSimulation.realRep_mul]
  exact Matrix.map_mul (f := Complex.ofRealHom)

@[simp] lemma complexRealRep_one {ι : Type*} [DecidableEq ι] :
    complexRealRep (1 : Matrix ι ι ℂ) = 1 := by
  simp [complexRealRep]








































































lemma complexRealRep_conjTranspose {ι κ : Type*} (A : Matrix ι κ ℂ) :
    complexRealRep Aᴴ = (complexRealRep A)ᴴ := by
  unfold complexRealRep
  rw [RealSimulation.realRep_conjTranspose]
  ext y x
  simp [Matrix.conjTranspose_apply]



















end QMAPerfectCompleteness.Main.DyadicCompiler

end

/- Inline helpers retained from Solutions.DyadicPreservation. -/
section


open Matrix
open scoped ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.DyadicCompiler
open VerifierAnalysis CyclicProof

/-- The complex-cast real representation preserves positive semidefiniteness. -/
theorem complexRealRep_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.PosSemidef) : (complexRealRep A).PosSemidef := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [hB, Matrix.star_eq_conjTranspose, complexRealRep_mul, complexRealRep_conjTranspose]
  exact Matrix.posSemidef_conjTranspose_mul_self _

lemma complexRealRep_trace {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) :
    (complexRealRep A).trace = (2 : ℂ) * (A.trace.re : ℂ) := by
  simp [Matrix.trace, complexRealRep, RealSimulation.realRep, Fintype.sum_prod_type,
    Complex.re_sum, Complex.ofReal_sum]
  ring

lemma trace_submatrix_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix κ κ ℂ) (e : ι ≃ κ) : (A.submatrix e e).trace = A.trace := by
  exact e.sum_comp (fun i => A i i)



theorem simulatedDensity_state (V : Verifier gatesHP) (ρ : Matrix V.Proof V.Proof ℂ)
    (hρ : V.IsProofState ρ) : (compileVerifier V).IsProofState (simulatedDensity V ρ) := by
  constructor
  · exact ((complexRealRep_posSemidef ρ hρ.1).smul (by norm_num [Complex.nonneg_iff] : (0 : ℂ) ≤ 1/2)).submatrix _
  · calc
      (simulatedDensity V ρ).trace = (((1/2 : ℂ) • complexRealRep ρ)).trace :=
        trace_submatrix_equiv _ (splitProof V.proofQubits)
      _ = 1 := by
        rw [Matrix.trace_smul, complexRealRep_trace, hρ.2]
        norm_num

theorem simulatedDensity_acceptProb (V : Verifier gatesHP) (ρ : Matrix V.Proof V.Proof ℂ) :
    (compileVerifier V).acceptProb (simulatedDensity V ρ) = V.acceptProb ρ := by
  have hm : (compileVerifier V).acceptanceOperator * simulatedDensity V ρ =
      (complexRealRep V.acceptanceOperator * ((1/2 : ℂ) • complexRealRep ρ)).submatrix
        (splitProof V.proofQubits) (splitProof V.proofQubits) := by
    rw [compileVerifier_acceptanceOperator]
    exact Matrix.submatrix_mul_equiv _ _ _ (splitProof V.proofQubits) _
  calc
    (compileVerifier V).acceptProb (simulatedDensity V ρ) =
        (complexRealRep V.acceptanceOperator * ((1/2 : ℂ) • complexRealRep ρ)).trace.re := by
      unfold Verifier.acceptProb
      rw [hm]
      exact congrArg Complex.re (trace_submatrix_equiv _ (splitProof V.proofQubits))
    _ = V.acceptProb ρ := by
      rw [Matrix.mul_smul, ← complexRealRep_mul, Matrix.trace_smul, complexRealRep_trace]
      simp [Verifier.acceptProb]

/-- Exact completeness preservation, for any threshold. -/
theorem compileVerifier_acceptsSome (V : Verifier gatesHP) (c : ℝ)
    (hyes : V.AcceptsSomeProof c) : (compileVerifier V).AcceptsSomeProof c := by
  obtain ⟨ρ,hρ,hc⟩ := hyes
  exact ⟨simulatedDensity V ρ, simulatedDensity_state V ρ hρ,
    by simpa only [simulatedDensity_acceptProb] using hc⟩

lemma complexRealRep_sub {ι κ : Type*} (A B : Matrix ι κ ℂ) :
    complexRealRep (A - B) = complexRealRep A - complexRealRep B := by
  ext i j
  simp [complexRealRep]

lemma complexRealRep_real_smul {ι κ : Type*} (r : ℝ) (A : Matrix ι κ ℂ) :
    complexRealRep ((r : ℂ) • A) = (r : ℂ) • complexRealRep A := by
  unfold complexRealRep
  rw [RealSimulation.realRep_real_smul]
  ext i j
  simp [smul_eq_mul]

/-- The source soundness condition is precisely the operator bound E≤I/3. -/
theorem source_soundness_effect (V : Verifier gatesHP) (hno : V.AcceptsAllProofsAtMost (1/3)) :
    (((1/3 : ℂ) • (1 : Matrix V.Proof V.Proof ℂ)) - V.acceptanceOperator).PosSemidef := by
  have hHerm : (((1/3 : ℂ) • (1 : Matrix V.Proof V.Proof ℂ)) - V.acceptanceOperator).IsHermitian :=
    (Matrix.isHermitian_one.smul (show IsSelfAdjoint (1/3 : ℂ) by simp [IsSelfAdjoint])).sub
      (acceptance_hermitian V)
  have hquad := DiagonalProof.quadratic_le_of_opNorm_le V.acceptanceOperator (1/3)
    (acceptance_opNorm_le V hno)
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm
  intro v
  apply Complex.nonneg_iff.mpr
  refine ⟨?_, (hHerm.im_star_dotProduct_mulVec_self v).symm⟩
  have hs : star v ⬝ᵥ v = ((euclidNorm v ^ 2 : ℝ) : ℂ) := by
    rw [dotProduct_comm]
    simpa [pureDensity, Matrix.trace_vecMulVec] using pureDensity_trace v
  have hb := hquad v
  simpa [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
    dotProduct_smul, hs, Complex.mul_re, ← Complex.ofReal_pow] using sub_nonneg.mpr hb

/-- The compiler preserves the operator soundness bound, also on complex superpositions of c. -/
theorem compiled_soundness_effect (V : Verifier gatesHP) (hno : V.AcceptsAllProofsAtMost (1/3)) :
    (((1/3 : ℂ) • (1 : Matrix (compileVerifier V).Proof (compileVerifier V).Proof ℂ)) -
      (compileVerifier V).acceptanceOperator).PosSemidef := by
  have h := (complexRealRep_posSemidef _ (source_soundness_effect V hno)).submatrix
    (splitProof V.proofQubits)
  rw [complexRealRep_sub, show (1/3 : ℂ) = ((1/3 : ℝ) : ℂ) by norm_num,
    complexRealRep_real_smul, complexRealRep_one, Matrix.submatrix_sub,
    Matrix.submatrix_smul] at h
  simpa [Matrix.submatrix_one_equiv, ← compileVerifier_acceptanceOperator] using h

/-- Exact soundness preservation for arbitrary mixed proofs, including entanglement with c. -/
theorem compileVerifier_acceptsAll (V : Verifier gatesHP)
    (hno : V.AcceptsAllProofsAtMost (1/3)) :
    (compileVerifier V).AcceptsAllProofsAtMost (1/3) := by
  intro ρ hρ
  have h := trace_mul_posSemidef_nonneg _ ρ (compiled_soundness_effect V hno) hρ.1
  change ((compileVerifier V).acceptanceOperator * ρ).trace.re ≤ (1/3 : ℝ)
  simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_sub,
    Matrix.trace_smul, hρ.2] at h
  norm_num at h
  linarith

end QMAPerfectCompleteness.Main.DyadicCompiler

end

/- Inline helpers retained from Solutions.Repetition. -/
section


open Matrix
open scoped Kronecker ComplexOrder
namespace QMAPerfectCompleteness.Main.Repetition
open VerifierAnalysis DiagonalProof CyclicProof

universe u









variable {ι : Type u} [Fintype ι] [DecidableEq ι]

lemma tensorPower_posSemidef (E : Matrix ι ι ℂ) (hE : E.PosSemidef) (n : ℕ) :
    (tensorPower E n).PosSemidef := by
  induction n with
  | zero => exact Matrix.PosSemidef.one
  | succ n ih => exact hE.kronecker ih

lemma tensorPower_trace (E : Matrix ι ι ℂ) (n : ℕ) :
    (tensorPower E n).trace = E.trace ^ n := by
  induction n with
  | zero => simp [tensorPower, RepeatedIndex]
  | succ n ih => rw [tensorPower, Matrix.trace_kronecker, ih, pow_succ']

lemma tensorPower_mul (E F : Matrix ι ι ℂ) (n : ℕ) :
    tensorPower E n * tensorPower F n = tensorPower (E*F) n := by
  induction n with
  | zero => simp [tensorPower]
  | succ n ih =>
    simp only [tensorPower]
    rw [← Matrix.mul_kronecker_mul, ih]

lemma tensorPower_pairing (E ρ : Matrix ι ι ℂ) (n : ℕ) :
    (tensorPower E n * tensorPower ρ n).trace = (E*ρ).trace ^ n := by
  rw [tensorPower_mul, tensorPower_trace]

/-- Positivity bounds tensor products even for entangled inputs. -/
lemma tensor_upper {κ : Type*} [Fintype κ] [DecidableEq κ]
    (E : Matrix ι ι ℂ) (F : Matrix κ κ ℂ) (s t : ℝ)
    (hE : E.PosSemidef) (ht : 0 ≤ t)
    (hEs : ((s : ℂ) • 1 - E).PosSemidef)
    (hFt : ((t : ℂ) • 1 - F).PosSemidef) :
    (((s*t : ℝ) : ℂ) • 1 - E ⊗ₖ F).PosSemidef := by
  have hT : ((t : ℂ) • (1 : Matrix κ κ ℂ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (by exact_mod_cast ht : (0 : ℂ) ≤ t)
  have hp := (hEs.kronecker hT).add (hE.kronecker hFt)
  have heq : (((s*t : ℝ) : ℂ) • (1 : Matrix (ι × κ) (ι × κ) ℂ) - E ⊗ₖ F) =
      (((s : ℂ) • 1 - E) ⊗ₖ ((t : ℂ) • 1)) + E ⊗ₖ ((t : ℂ) • 1 - F) := by
    ext ⟨i,a⟩ ⟨j,b⟩
    by_cases hij : i = j <;> by_cases hab : a = b <;>
      simp [Matrix.kroneckerMap_apply, Matrix.one_apply, hij, hab, Prod.mk.injEq] <;> ring
  rw [heq]
  exact hp

lemma tensorPower_upper (E : Matrix ι ι ℂ) (s : ℝ) (hs : 0 ≤ s)
    (hE : E.PosSemidef) (hEs : ((s : ℂ) • 1 - E).PosSemidef) (n : ℕ) :
    (((s ^ n : ℝ) : ℂ) • 1 - tensorPower E n).PosSemidef := by
  induction n with
  | zero => simpa [tensorPower] using (Matrix.PosSemidef.zero (n := RepeatedIndex ι 0) (R := ℂ))
  | succ n ih =>
    simpa [tensorPower, pow_succ'] using tensor_upper E (tensorPower E n) s (s^n)
      hE (pow_nonneg hs n) hEs ih

/-- A PSD upper bound controls every density matrix on the whole tensor space. -/
lemma mixed_upper_of_posSemidef (E : Matrix ι ι ℂ) (s : ℝ)
    (hEs : ((s : ℂ) • 1 - E).PosSemidef)
    (ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1) :
    (E*ρ).trace.re ≤ s := by
  have hp := trace_mul_posSemidef_nonneg _ ρ hEs hρ
  simpa [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_sub,
    Matrix.trace_smul, htrace] using hp

/-- Density-matrix soundness implies an operator upper bound, via pure eigenstates. -/
lemma upper_of_all_states [Nonempty ι] (E : Matrix ι ι ℂ) (hE : E.PosSemidef) (s : ℝ)
    (hs : 0 ≤ s)
    (hbound : ∀ ρ : Matrix ι ι ℂ, ρ.PosSemidef → ρ.trace = 1 → (E*ρ).trace.re ≤ s) :
    ((s : ℂ) • 1 - E).PosSemidef := by
  have heigen (i : ι) : hE.1.eigenvalues i ≤ s := by
    let v : ι → ℂ := ⇑(hE.1.eigenvectorBasis i)
    have hv : euclidNorm v = 1 := by
      have hv := hE.1.eigenvectorBasis.orthonormal.1 i
      simpa only [EuclideanSpace.norm_eq, euclidNorm, v] using hv
    have hb := hbound (pureDensity v) (pureDensity_posSemidef v) (pureDensity_trace_one v hv)
    rw [pureDensity_expectation] at hb
    rw [hE.1.eigenvalues_eq]
    exact hb
  have hop := psd_opNorm_le E hE s hs heigen
  have hHerm : ((s : ℂ) • (1 : Matrix ι ι ℂ) - E).IsHermitian :=
    (Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint])).sub hE.1
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm
  intro v
  have hq := quadratic_le_of_opNorm_le E s hop v
  have hself : star v ⬝ᵥ v = ((euclidNorm v ^ 2 : ℝ) : ℂ) := by
    rw [dotProduct_comm]
    simpa [pureDensity, Matrix.trace_vecMulVec] using pureDensity_trace v
  apply Complex.nonneg_iff.mpr
  constructor
  · simpa [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, hself, ← Complex.ofReal_pow] using sub_nonneg.mpr hq
  · exact (hHerm.im_star_dotProduct_mulVec_self v).symm

lemma trace_pairing_real (E ρ : Matrix ι ι ℂ) (hE : E.IsHermitian) (hρ : ρ.IsHermitian) :
    (E*ρ).trace.im = 0 := by
  have hstar : star (E*ρ).trace = (E*ρ).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hE.eq, hρ.eq,
      Matrix.trace_mul_comm]
  have hi := congrArg Complex.im hstar
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

/-- Perfect completeness is witnessed by tensor products of the honest state. -/
lemma tensorPower_perfect (E ρ : Matrix ι ι ℂ) (hE : E.PosSemidef) (hρ : ρ.PosSemidef)
    (htrace : ρ.trace = 1) (haccept : (E*ρ).trace = 1) (n : ℕ) :
    (tensorPower ρ n).PosSemidef ∧ (tensorPower ρ n).trace = 1 ∧
      (tensorPower E n * tensorPower ρ n).trace = 1 := by
  refine ⟨tensorPower_posSemidef ρ hρ n, ?_, ?_⟩
  · rw [tensorPower_trace, htrace, one_pow]
  · rw [tensorPower_pairing, haccept, one_pow]

/-- Soundness s becomes s^n for arbitrary, possibly entangled, n-copy density matrices. -/
theorem tensorPower_soundness [Nonempty ι] (E : Matrix ι ι ℂ) (hE : E.PosSemidef)
    (s : ℝ) (hs : 0 ≤ s)
    (hbound : ∀ ρ : Matrix ι ι ℂ, ρ.PosSemidef → ρ.trace = 1 → (E*ρ).trace.re ≤ s)
    (n : ℕ) (ρ : Matrix (RepeatedIndex ι n) (RepeatedIndex ι n) ℂ)
    (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1) :
    (tensorPower E n * ρ).trace.re ≤ s ^ n := by
  exact mixed_upper_of_posSemidef _ _
    (tensorPower_upper E s hs hE (upper_of_all_states E hE s hs hbound) n) ρ hρ htrace

/-- Pointwise parallel repetition for an actual verifier's acceptance effect. -/
theorem verifier_repetition_semantics {G : GateSet} (V : Verifier G) (s : ℝ) (hs : 0 ≤ s)
    (hyes : V.AcceptsSomeProof 1) (hno : V.AcceptsAllProofsAtMost s) (n : ℕ) :
    (∃ ρ : Matrix (RepeatedIndex V.Proof n) (RepeatedIndex V.Proof n) ℂ,
      ρ.PosSemidef ∧ ρ.trace = 1 ∧ (tensorPower V.acceptanceOperator n * ρ).trace = 1) ∧
    (∀ ρ : Matrix (RepeatedIndex V.Proof n) (RepeatedIndex V.Proof n) ℂ,
      ρ.PosSemidef → ρ.trace = 1 → (tensorPower V.acceptanceOperator n * ρ).trace.re ≤ s ^ n) := by
  constructor
  · obtain ⟨ρ, hρ, hc⟩ := hyes
    have hupper := mixed_upper_of_posSemidef V.acceptanceOperator 1
      (by simpa using CircuitProof.acceptance_complement_posSemidef V) ρ hρ.1 hρ.2
    have haccept : (V.acceptanceOperator*ρ).trace = 1 := by
      apply Complex.ext
      · change (V.acceptanceOperator*ρ).trace.re = 1
        change 1 ≤ (V.acceptanceOperator*ρ).trace.re at hc
        linarith
      · simpa using trace_pairing_real _ _ (acceptance_hermitian V) hρ.1.1
    exact ⟨tensorPower ρ n, tensorPower_perfect _ _ (acceptance_posSemidef V) hρ.1 hρ.2 haccept n⟩
  · intro ρ hρ htrace
    exact tensorPower_soundness _ (acceptance_posSemidef V) s hs
      (fun ρ hp ht => hno ρ ⟨hp,ht⟩) n ρ hρ htrace

/-- The fixed repetition count used in the paper's final amplification. -/
lemma repetition_count_576 : ((1 : ℝ) - 1 / 576) ^ 576 ≤ 1 / 2 := by
  have h := one_add_mul_le_pow (by norm_num : (-2 : ℝ) ≤ 1 / 575) 576
  rw [show (1 : ℝ) + 1 / 575 = 576 / 575 by norm_num] at h
  have h2 : (2 : ℝ) ≤ (576 / 575 : ℝ) ^ 576 :=
    (by norm_num : (2 : ℝ) ≤ 1 + (576 : ℕ) * (1 / 575)).trans h
  have hi : ((576 / 575 : ℝ) ^ 576)⁻¹ ≤ (2 : ℝ)⁻¹ :=
    inv_anti₀ (by norm_num : (0 : ℝ) < 2) h2
  rw [← inv_pow, show (576 / 575 : ℝ)⁻¹ = 1 - 1 / 576 by norm_num,
    show (2 : ℝ)⁻¹ = 1 / 2 by norm_num] at hi
  exact hi

/-! ## Concrete gate list for repetition

The proof wires of the copies come first; each copy's ancillas follow, then n+1 prefix-AND flags.
No certificate or proof measurements occur between the copies. The final flag is the output.
-/

namespace Circuit

































end Circuit

end QMAPerfectCompleteness.Main.Repetition

end

/- Inline helpers retained from Solutions.RepetitionCircuit. -/
section


open Matrix
open scoped Kronecker ComplexOrder

set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.Repetition.CircuitProof
open Circuit ReversibleGadgets VerifierAnalysis








































/-! Generic finite tensor matrices on function-indexed copy registers. -/



































































universe u



lemma tensorPower_entry {α : Type u} [Fintype α] [DecidableEq α] (E : Matrix α α ℂ)
    (n : ℕ) (x y : RepeatedIndex α n) :
    tensorPower E n x y =
      piMatrix (fun _ : Fin n => E) (tensorIndexEquiv α n x) (tensorIndexEquiv α n y) := by
  induction n with
  | zero =>
    cases x
    cases y
    simp [tensorPower, piMatrix]
  | succ n ih =>
    obtain ⟨a,x⟩ := x
    obtain ⟨b,y⟩ := y
    simp only [tensorPower, Matrix.kroneckerMap_apply, tensorIndexEquiv, piMatrix,
      Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [ih]
    rfl



/-- Exact acceptance-operator bridge to the tensor power used in semantic soundness. -/
theorem acceptanceOperator_tensorPower (V : Verifier gatesG2) (n : ℕ) :
    (Circuit.verifier V n).acceptanceOperator =
      (tensorPower V.acceptanceOperator n).submatrix (proofTensorEquiv V n) (proofTensorEquiv V n) := by
  rw [acceptanceOperator_pi]
  ext p q
  simp only [Matrix.submatrix_apply, tensorPower_entry, proofTensorEquiv, Equiv.trans_apply,
    Equiv.apply_symm_apply]
  all_goals rfl

lemma trace_submatrix_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β)
    (M : Matrix β β ℂ) : (M.submatrix e e).trace = M.trace := by
  simpa only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply] using
    e.sum_comp (fun b => M b b)

lemma trace_pairing_submatrix {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β)
    (E : Matrix β β ℂ) (ρ : Matrix α α ℂ) :
    (E.submatrix e e * ρ).trace = (E * ρ.submatrix e.symm e.symm).trace := by
  have hρ : (ρ.submatrix e.symm e.symm).submatrix e e = ρ := by
    ext p q
    simp
  calc
    _ = ((E * ρ.submatrix e.symm e.symm).submatrix e e).trace := by
      rw [← Matrix.submatrix_mul_equiv _ _ e e e, hρ]
    _ = _ := trace_submatrix_equiv e _

/-- The concrete repeated G₂ verifier preserves perfect completeness. -/
theorem verifier_completeness (V : Verifier gatesG2) (n : ℕ) (hyes : V.AcceptsSomeProof 1) :
    (Circuit.verifier V n).AcceptsSomeProof 1 := by
  have hno : V.AcceptsAllProofsAtMost 1 := by
    intro ρ hρ
    exact mixed_upper_of_posSemidef _ 1
      (by simpa using QMAPerfectCompleteness.Main.CircuitProof.acceptance_complement_posSemidef V)
      ρ hρ.1 hρ.2
  obtain ⟨⟨ρ,hρ,htrace,haccept⟩,_⟩ := verifier_repetition_semantics V 1 (by norm_num) hyes hno n
  let e := proofTensorEquiv V n
  refine ⟨ρ.submatrix e e, ⟨hρ.submatrix e, ?_⟩, ?_⟩
  · rw [trace_submatrix_equiv, htrace]
  · change 1 ≤ ((Circuit.verifier V n).acceptanceOperator * ρ.submatrix e e).trace.re
    rw [acceptanceOperator_tensorPower, Matrix.submatrix_mul_equiv _ _ e e e,
      trace_submatrix_equiv, haccept]
    norm_num

/-- All witnesses for the actual circuit, including entangled witnesses, have soundness s^n. -/
theorem verifier_soundness (V : Verifier gatesG2) (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hno : V.AcceptsAllProofsAtMost s) : (Circuit.verifier V n).AcceptsAllProofsAtMost (s^n) := by
  intro ρ hρ
  let e := proofTensorEquiv V n
  have hp : (ρ.submatrix e.symm e.symm).PosSemidef := hρ.1.submatrix e.symm
  have ht : (ρ.submatrix e.symm e.symm).trace = 1 := by rw [trace_submatrix_equiv, hρ.2]
  have hb := tensorPower_soundness V.acceptanceOperator
    (QMAPerfectCompleteness.Main.CyclicProof.acceptance_posSemidef V) s hs
    (fun σ hp ht => hno σ ⟨hp,ht⟩) n (ρ.submatrix e.symm e.symm) hp ht
  change ((Circuit.verifier V n).acceptanceOperator * ρ).trace.re ≤ s^n
  rw [acceptanceOperator_tensorPower, trace_pairing_submatrix]
  exact hb



end QMAPerfectCompleteness.Main.Repetition.CircuitProof

end

/- Inline helpers retained from Solutions.HTPreservation. -/
section


open Matrix
open scoped Kronecker
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.HTCompiler
open HadamardToffoli ReversibleGadgets









































































theorem compileVerifier_acceptProb (V : Verifier gatesG2) (ρ : Matrix V.Proof V.Proof ℂ) :
    (compileVerifier V).acceptProb ρ = V.acceptProb ρ := by
  rw [Verifier.acceptProb, compileVerifier_acceptanceOperator]
  rfl

theorem compileVerifier_acceptsSome (V : Verifier gatesG2) (c : ℝ)
    (hyes : V.AcceptsSomeProof c) : (compileVerifier V).AcceptsSomeProof c := by
  obtain ⟨ρ,hρ,hc⟩ := hyes
  exact ⟨ρ,hρ,by simpa only [compileVerifier_acceptProb] using hc⟩

theorem compileVerifier_acceptsAll (V : Verifier gatesG2) (s : ℝ)
    (hno : V.AcceptsAllProofsAtMost s) : (compileVerifier V).AcceptsAllProofsAtMost s := by
  intro ρ hρ
  simpa only [compileVerifier_acceptProb] using hno ρ hρ

end QMAPerfectCompleteness.Main.HTCompiler

end

/- Inline helpers retained from Solutions.ClassTransport. -/
section


/-! Class assembly needs only continuations of generators whose outputs are verifier codes.
No general polynomial-time composition theorem, nor a runtime specification on malformed
compiler inputs, is required by these reductions. The runtime hypotheses below remain explicit. -/
namespace QMAPerfectCompleteness.Main.ClassTransport
open QAlgorithms.Complexity (Str PolyTimeComputable)





/-- Lemma 3.1's forward inclusion, reduced to its specific generator continuation. -/
theorem dyadic_forward
    (htime : UniformOnVerifierCodes gatesHP DyadicCompiler.executableCompile) :
    QMA ⊆ QMAClass gatesG2 (2/3) (1/3) := by
  exact transport DyadicCompiler.compileVerifier DyadicCompiler.executableCompile
    DyadicCompiler.executableCompile_encode htime
    (fun V => DyadicCompiler.compileVerifier_acceptsSome V (2/3))
    DyadicCompiler.compileVerifier_acceptsAll

/-- The actual 576-copy circuit gives the class reduction as soon as its specialized
code-generator continuation is supplied. Entangled-proof soundness is already proved. -/
theorem repeat_perfect
    (htime : UniformOnVerifierCodes gatesG2 (Repetition.Encoding.executableCompile 576)) :
    QMAClass gatesG2 1 (1-1/576) ⊆ QMA1 gatesG2 := by
  apply transport (fun V => Repetition.Circuit.verifier V 576)
    (Repetition.Encoding.executableCompile 576)
    (fun V => Repetition.Encoding.executableCompile_encode V 576) htime
  · exact fun V => Repetition.CircuitProof.verifier_completeness V 576
  · intro V hno ρ hρ
    exact (Repetition.CircuitProof.verifier_soundness V 576 (1-1/576)
      (by norm_num) hno ρ hρ).trans Repetition.repetition_count_576

/-- Exact finite synthesis preserves both thresholds; its only class-level hypothesis is
runtime of the concrete code continuation. -/
theorem to_hadamard_toffoli
    (htime : UniformOnVerifierCodes gatesG2 HTCompiler.executableCompile) :
    QMA1 gatesG2 ⊆ QMA1 gatesHT := by
  exact transport HTCompiler.compileVerifier HTCompiler.executableCompile
    HTCompiler.executableCompile_encode htime
    (fun V => HTCompiler.compileVerifier_acceptsSome V 1)
    (fun V => HTCompiler.compileVerifier_acceptsAll V (1/2))

end QMAPerfectCompleteness.Main.ClassTransport

end

/- Inline helpers retained from Solutions.ReverseCompilerTM. -/
section


/-! A finite unary-stream machine for the exact seventeen-gate reverse compiler. -/
set_option backward.isDefEq.respectTransparency false
open Turing StateTransition
namespace QMAPerfectCompleteness.Main.ReverseCompiler.TM
open QAlgorithms.Complexity (Str encNat)
open Uniformity


































































































































































































































/-- The exact reverse compiler preserves polynomial-time uniform generation on valid codes. -/
theorem uniformOnVerifierCodes : ClassTransport.UniformOnVerifierCodes gatesHT executableCompile := by
  intro gen V hgen henc
  obtain ⟨hf⟩ := hgen
  refine ⟨Uniformity.BinaryComposition.computableContinuation hf machine (Equiv.refl Bool)
    (Equiv.refl Bool) timePolynomial ?_⟩
  intro x
  simpa only [Equiv.refl,List.map_id_fun,henc x,id_eq,executableCompile] using outputs_verifier (V x)

end QMAPerfectCompleteness.Main.ReverseCompiler.TM

end

/- Inline helpers retained from Solutions.DyadicCompilerTM. -/
section


/-! Explicit unary-stream machine for the HP-to-G₂ real-simulation compiler. -/
set_option backward.isDefEq.respectTransparency false
open Turing StateTransition
namespace QMAPerfectCompleteness.Main.DyadicCompiler.TM
open QAlgorithms.Complexity (Str encNat)
open Uniformity




























































































































































































































































/-- Actual polynomial-time valid-code uniformity for the paper's real-simulation compiler. -/
theorem uniformOnVerifierCodes : ClassTransport.UniformOnVerifierCodes gatesHP executableCompile := by
  intro gen V hgen henc
  obtain ⟨hf⟩ := hgen
  refine ⟨Uniformity.BinaryComposition.computableContinuation hf machine (Equiv.refl Bool)
    (Equiv.refl Bool) timePolynomial ?_⟩
  intro x
  simpa only [Equiv.refl,List.map_id_fun,henc x,id_eq,executableCompile] using outputs_verifier (V x)

end QMAPerfectCompleteness.Main.DyadicCompiler.TM

end

/- Inline helpers retained from Solutions.HTCompilerTM. -/
section


/-! Instantiation of the generic finite-plan machine for the exact G₂-to-HT compiler. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
open Turing StateTransition
namespace QMAPerfectCompleteness.Main.HTCompiler.TM
open QAlgorithms.Complexity (Str encNat)
open Uniformity







































/-- Actual polynomial-time valid-code uniformity of the finite G₂-to-HT gate compiler. -/
theorem uniformOnVerifierCodes : ClassTransport.UniformOnVerifierCodes gatesG2 executableCompile := by
  intro gen V hgen henc
  obtain ⟨hf⟩ := hgen
  refine ⟨Uniformity.BinaryComposition.computableContinuation hf (Uniformity.FinitePlanCompiler.machine config) (Equiv.refl Bool)
    (Equiv.refl Bool) timePolynomial ?_⟩
  intro x
  simpa only [Equiv.refl,List.map_id_fun,henc x,id_eq,executableCompile] using outputs_verifier (V x)

end QMAPerfectCompleteness.Main.HTCompiler.TM

end

/- Inline helpers retained from Solutions.FixedBlockCopy. -/
section


/-! Explicit fixed-count whole-block duplication, with a direct source-generator continuation. -/
set_option backward.isDefEq.respectTransparency false
open Turing StateTransition
namespace QMAPerfectCompleteness.Uniformity.BlockCopy
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

























































/-- A fixed number of copies of any polynomial-time generator output is polynomial-time. -/
theorem polyTime_output_copy {f : List Bool → List Bool}
    (hf : QAlgorithms.Complexity.PolyTimeComputable f) (n : ℕ) :
    QAlgorithms.Complexity.PolyTimeComputable (fun s => (List.replicate n (f s)).flatten) := by
  obtain ⟨hf⟩ := hf
  exact ⟨computableInPolyTime hf n⟩



end QMAPerfectCompleteness.Uniformity.BlockCopy

end

/- Inline helpers retained from Solutions.RepetitionUniformity. -/
section


/-! Actual TM2 polynomial-time uniformity of fixed positive-count G₂ repetition. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
open Turing StateTransition
namespace QMAPerfectCompleteness.Main.Repetition.CompilerTM
open QAlgorithms.Complexity (Str encNat)
open Uniformity









/-- A fixed positive repetition count is uniformly computable by a concrete polynomial-time
TM2 continuation after the original generator, without any generic TM composition axiom. -/
theorem uniformOnVerifierCodes (n : ℕ) (hn : 0<n) :
    ClassTransport.UniformOnVerifierCodes gatesG2 (Encoding.executableCompile n) := by
  intro gen V hgen henc
  have hdup := BlockCopy.polyTime_output_copy hgen n
  obtain ⟨hf⟩ := hdup
  have hc := BinaryComposition.computableContinuation (g := duplicatedCompile n) hf (machine n)
    (Equiv.refl Bool) (Equiv.refl Bool) (timePolynomial n) (fun x => by
      simpa only [Equiv.refl,List.map_id_fun,id_eq,henc x] using outputs_verifier n hn (V x))
  have he : duplicatedCompile n ∘ (fun x => (List.replicate n (gen x)).flatten) =
      (fun x => Encoding.executableCompile n (gen x)) := by
    funext x
    simp only [Function.comp_def,henc x,duplicatedCompile_replicate n hn]
  rw [he] at hc
  exact ⟨hc⟩

theorem uniformOnVerifierCodes_two :
    ClassTransport.UniformOnVerifierCodes gatesG2 (Encoding.executableCompile 2) :=
  uniformOnVerifierCodes 2 (by decide)

theorem uniformOnVerifierCodes_576 :
    ClassTransport.UniformOnVerifierCodes gatesG2 (Encoding.executableCompile 576) :=
  uniformOnVerifierCodes 576 (by decide)

end QMAPerfectCompleteness.Main.Repetition.CompilerTM

end

/- Inline helpers retained from Solutions.PaperProof. -/
section


/-! Complete main assembly. Finite gate compilation, coherent certificate verification,
repetition semantics, exact code correspondence and finite-machine uniform generation are
all proved locally. -/
namespace QMAPerfectCompleteness.Main.ProofSetup
open ClassTransport

/-- Continue an HP verifier generator with the exact real-simulation code compiler. -/
theorem dyadic_generator_uniform :
    UniformOnVerifierCodes gatesHP DyadicCompiler.executableCompile :=
  DyadicCompiler.TM.uniformOnVerifierCodes

/-- Continue a G₂ verifier generator with the fixed 576-copy circuit compiler. -/
theorem repetition576_generator_uniform :
    UniformOnVerifierCodes gatesG2 (Repetition.Encoding.executableCompile 576) :=
  Repetition.CompilerTM.uniformOnVerifierCodes_576

/-- Continue a G₂ verifier generator with two copies, for the reverse inclusion. -/
theorem repetition2_generator_uniform :
    UniformOnVerifierCodes gatesG2 (Repetition.Encoding.executableCompile 2) :=
  Repetition.CompilerTM.uniformOnVerifierCodes_two

/-- Continue a G₂ verifier generator with the exact clean-workspace HT compiler. -/
theorem ht_generator_uniform :
    UniformOnVerifierCodes gatesG2 HTCompiler.executableCompile :=
  HTCompiler.TM.uniformOnVerifierCodes

/-- Continue an HT verifier generator with the exact seventeen-gate HP compiler. -/
theorem hp_generator_uniform :
    UniformOnVerifierCodes gatesHT ReverseCompiler.executableCompile :=
  ReverseCompiler.TM.uniformOnVerifierCodes

/-- Paper Lemma 3.1, only in the forward direction needed by the main proof. -/
theorem dyadic_verifiers_forward : QMA ⊆ QMAClass gatesG2 (2/3) (1/3) :=
  ClassTransport.dyadic_forward dyadic_generator_uniform

/-- Main proof, paragraphs 1–3: retain (z,a,b) coherently, reject invalid claims, initialize η,
apply the literal dynamic block circuit and reject precisely on the all-zero Z outcome.
The physical acceptance identity and actual finite-machine uniform generator are proved locally. -/
theorem cyclic_verifier :
    QMAClass gatesG2 (2/3) (1/3) ⊆ QMAClass gatesG2 1 (1-1/576) :=
  CyclicRecipe.class_reduction

/-- Concrete 576-copy amplification, with arbitrary entangled-proof soundness. -/
theorem perfect_completeness_repetition :
    QMAClass gatesG2 1 (1-1/576) ⊆ QMA1 gatesG2 :=
  ClassTransport.repeat_perfect repetition576_generator_uniform

/-- Exact G₂-to-HT synthesis, with three clean reusable ancillary wires. -/
theorem synthesize_hadamard_toffoli : QMA1 gatesG2 ⊆ QMA1 gatesHT :=
  ClassTransport.to_hadamard_toffoli ht_generator_uniform

/-- Exact HT→HP→G₂, two-copy amplification, then G₂→HT→HP; soundness is 1/4. -/
theorem qma1_hadamard_toffoli_subset_qma : QMA1 gatesHT ⊆ QMA :=
  ClassTransport.reverse dyadic_generator_uniform repetition2_generator_uniform
    ht_generator_uniform hp_generator_uniform

end QMAPerfectCompleteness.Main.ProofSetup

end



/-!
Theorem 1.1, assembled in the order of the paper's proof (main.tex, lines 945–960).
All mathematical and circuit arguments are local, with explicit finite-machine compiler proofs.
Every supporting lemma, including the cyclic serializer and its class reduction, is proved.
The target's own open platform theorem is never imported.
Standalone submission requires flattening local Solutions/ imports with the export script.
-/

open QMAPerfectCompleteness.Main
open QMAPerfectCompleteness.Main.ProofSetup

/-- The exact target type, with the platform-required top-level name. -/
theorem solution : QMA = QMA1 gatesHT := by
  apply Set.Subset.antisymm
  · intro L hL
    have hG2 : L ∈ QMAClass gatesG2 (2 / 3) (1 / 3) := by
      exact dyadic_verifiers_forward hL
    have hperfect : L ∈ QMAClass gatesG2 1 (1 - 1 / 576) := cyclic_verifier hG2
    have hrepeated : L ∈ QMA1 gatesG2 := perfect_completeness_repetition hperfect
    exact synthesize_hadamard_toffoli hrepeated
  · exact qma1_hadamard_toffoli_subset_qma
