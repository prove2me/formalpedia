-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.CyclicVerifier.completeness
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T17:25:42.323205+00:00
-- url     : https://prove2.me/submissions/1617ff71-c081-4e37-ae90-f2a715938e17

/- Generated from Solutions.CyclicVerifier by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Init.Data.BitVec.Bitblast
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
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentAcceptance
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentCertificate
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentReadout
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicVerifier
import Definitions.Def_QMAPerfectCompleteness_Proof_Dyadic
import Definitions.Def_QMAPerfectCompleteness_Proof_DynamicBlockCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_DynamicRangeLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_IndexHadamards
import Definitions.Def_QMAPerfectCompleteness_Proof_PointwiseSetup
import Definitions.Def_QMAPerfectCompleteness_Proof_RegisterCopies
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_ThresholdLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_ThresholdPreparation
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableAddition
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableComparison
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableHistoryEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierAnalysis
import Theorems.Thm_QMAPerfectCompleteness_Main_BlockProof_exact_block_identity
import Theorems.Thm_QMAPerfectCompleteness_Main_valid_certificate
import Theorems.Thm_QMAPerfectCompleteness_Main_cyclic_constraint
import Theorems.Thm_QMAPerfectCompleteness_Main_CyclicVerifier_acceptanceOperator

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

/- Inline helpers retained from Solutions.EuclideanStates. -/
section


open Matrix
open scoped ComplexOrder MatrixOrder

namespace QMAPerfectCompleteness.Main.VerifierAnalysis

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma euclidNorm_nonneg (v : ι → ℂ) : 0 ≤ euclidNorm v := Real.sqrt_nonneg _

lemma euclidNorm_sq (v : ι → ℂ) : euclidNorm v ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma euclidNorm_smul (c : ℂ) (v : ι → ℂ) :
    euclidNorm (c • v) = ‖c‖ * euclidNorm v := by
  simp only [euclidNorm, Pi.smul_apply, norm_smul, mul_pow]
  rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

lemma euclidNorm_eq_zero_iff (v : ι → ℂ) : euclidNorm v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have hs : ∑ i, ‖v i‖ ^ 2 = 0 := by rw [← euclidNorm_sq, h]; norm_num
    funext i
    have hi : ‖v i‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hs i (Finset.mem_univ i)
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (v i)])
  · rintro rfl
    simp [euclidNorm]

lemma euclidNorm_pos (v : ι → ℂ) (hv : v ≠ 0) : 0 < euclidNorm v := by
  exact lt_of_le_of_ne (euclidNorm_nonneg v) (Ne.symm (mt (euclidNorm_eq_zero_iff v).mp hv))



lemma normalize_euclidNorm (v : ι → ℂ) (hv : v ≠ 0) : euclidNorm (normalize v) = 1 := by
  rw [normalize, euclidNorm_smul]
  simp [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (euclidNorm_nonneg v), ne_of_gt (euclidNorm_pos v hv)]

lemma normalize_kernel (B : Matrix κ ι ℂ) (v : ι → ℂ) (h : B *ᵥ v = 0) :
    B *ᵥ normalize v = 0 := by
  simp [normalize, Matrix.mulVec_smul, h]



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







end QMAPerfectCompleteness.Main.VerifierAnalysis

end

/- Inline helpers retained from Solutions.PointwiseSetup. -/
section


/-!
# Pointwise main-proof lemmas, following §3 of the paper

The certificate, cyclic constraint, and algebraic block identity are proved locally.
Pointwise lemmas are separate from class assembly and contain no proof holes.
Keep platform sources in Definitions/ and Theorems/ verbatim; do proof work in Solutions/.
-/

open Matrix

namespace QMAPerfectCompleteness.Main.ProofSetup





/-- Lemmas 3.7 and 3.4(i): the honest certificate closes the unnormalized history cycle. -/
theorem honest_history (V : Verifier gatesG2) (hyes : V.AcceptsSomeProof (2 / 3)) :
    ∃ (z : V.Proof) (a b : ℕ), IsValidCertificate V a b ∧
      V.historyVector z ≠ 0 ∧
      (1 - V.cyclicOp z ((a : ℝ) / b)) *ᵥ V.historyVector z = 0 := by
  obtain ⟨z, a, b, hvalid, hratio, hgamma⟩ := QMAPerfectCompleteness.Main.valid_certificate V hyes
  obtain ⟨hne, hkernel⟩ := (QMAPerfectCompleteness.Main.cyclic_constraint V).1 hyes z _ hgamma hratio
  exact ⟨z, a, b, hvalid, hne, hkernel⟩

/-- Lemma 3.6 converts any kernel vector into zero rejection amplitude. -/
theorem rejectionBlock_mulVec_eq_zero (V : Verifier gatesG2) (z : V.Proof)
    (a b : ℕ) (hvalid : IsValidCertificate V a b) (ψ : History V → ℂ)
    (hkernel : (1 - V.cyclicOp z ((a : ℝ) / b)) *ᵥ ψ = 0) :
    rejectionBlock V z a b *ᵥ ψ = 0 := by
  rw [rejectionBlock, BlockProof.exact_block_identity V z a b hvalid, Matrix.smul_mulVec, hkernel]
  simp

/-- The completeness part of the final proof, at the amplitude level. Normalization and the
conversion to a trace-one density matrix are proved in `VerifierAnalysis`. -/
theorem honest_zero_rejection (V : Verifier gatesG2)
    (hyes : V.AcceptsSomeProof (2 / 3)) :
    ∃ (z : V.Proof) (a b : ℕ), IsValidCertificate V a b ∧
      V.historyVector z ≠ 0 ∧ rejectionBlock V z a b *ᵥ V.historyVector z = 0 := by
  obtain ⟨z, a, b, hvalid, hne, hkernel⟩ := honest_history V hyes
  exact ⟨z, a, b, hvalid, hne,
    rejectionBlock_mulVec_eq_zero V z a b hvalid _ hkernel⟩











end QMAPerfectCompleteness.Main.ProofSetup

end

/- Inline helpers retained from Solutions.CertificateMixture. -/
section


open Matrix
open scoped ComplexOrder

namespace QMAPerfectCompleteness.Main.CertificateMixture
open VerifierAnalysis

variable {ι C : Type*} [Fintype ι] [Fintype C] [DecidableEq ι] [DecidableEq C]

lemma blockDiagonal_mulVec (E : C → Matrix ι ι ℂ) (ψ : ι × C → ℂ) (i : ι) (c : C) :
    (Matrix.blockDiagonal E *ᵥ ψ) (i, c) = (E c *ᵥ fun j => ψ (j, c)) i := by
  simp [Matrix.mulVec, dotProduct, Matrix.blockDiagonal_apply, Fintype.sum_prod_type]





















lemma attachClaim_norm (c : C) (ψ : ι → ℂ) : euclidNorm (attachClaim c ψ) = euclidNorm ψ := by
  unfold euclidNorm attachClaim
  simp [Fintype.sum_prod_type, apply_ite]

lemma attachClaim_kernel (E : C → Matrix ι ι ℂ) (c : C) (ψ : ι → ℂ)
    (hker : E c *ᵥ ψ = 0) : Matrix.blockDiagonal E *ᵥ attachClaim c ψ = 0 := by
  ext ⟨i, d⟩
  rw [blockDiagonal_mulVec]
  by_cases h : d = c
  · subst d
    simpa [attachClaim] using congrFun hker i
  · simp [attachClaim, h, Matrix.mulVec, dotProduct]

/-- On a YES instance the full certificate/history rejection effect has a trace-one PSD
witness with expectation exactly zero. This is the semantic completeness of the construction;
the polynomial-time circuit realizing this effect is a separate remaining obligation. -/
theorem honest_full_state (V : Verifier gatesG2) (hyes : V.AcceptsSomeProof (2 / 3)) :
    ∃ ρ : Matrix (History V × Claim V) (History V × Claim V) ℂ,
      ρ.PosSemidef ∧ ρ.trace = 1 ∧ (Matrix.blockDiagonal (claimRejection V) * ρ).trace.re = 0 := by
  classical
  obtain ⟨z, a, b, hv, hne, hzero⟩ := ProofSetup.honest_zero_rejection V hyes
  let c : Claim V := (z, ⟨a, hv.2.2.1⟩, ⟨b, hv.2.2.2.1⟩)
  let ψ := normalize (V.historyVector z)
  have hψ : euclidNorm ψ = 1 := normalize_euclidNorm _ hne
  have hblock : ProofSetup.rejectionBlock V z a b *ᵥ ψ = 0 := normalize_kernel _ _ hzero
  have hclaim : claimRejection V c *ᵥ ψ = 0 := by
    dsimp [claimRejection, c]
    rw [if_pos hv, ← Matrix.mulVec_mulVec, hblock, Matrix.mulVec_zero]
  let Ψ := attachClaim c ψ
  have hnorm : euclidNorm Ψ = 1 := (attachClaim_norm c ψ).trans hψ
  refine ⟨pureDensity Ψ, pureDensity_posSemidef _, pureDensity_trace_one _ hnorm, ?_⟩
  rw [pureDensity_expectation, attachClaim_kernel _ _ _ hclaim]
  simp

end QMAPerfectCompleteness.Main.CertificateMixture

end

/- Inline helpers retained from Solutions.CoherentCertificate. -/
section


/-! Coherent certificate control, invalid-claim rejection, and the final acceptance bridge.
This module proves the measurement algebra independently of how the literal dynamic
comparison circuit is synthesized. -/
open Matrix
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.CoherentCertificate
open CertificateMixture VerifierAnalysis
















lemma trace_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (A : Matrix κ κ ℂ) : (A.submatrix e e).trace = A.trace :=
  e.sum_comp (fun i => A i i)

lemma trace_product_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (A B : Matrix κ κ ℂ) :
    (A.submatrix e e * B.submatrix e e).trace = (A*B).trace := by
  rw [Matrix.submatrix_mul_equiv]
  exact trace_reindex e _

/-- Any literal verifier with the exact analysed acceptance operator has perfect completeness.
The equivalence explicitly accounts for the physical ordering of certificate/history wires. -/
theorem acceptsSome_of_effect {G : GateSet} (V : Verifier gatesG2) (W : Verifier G)
    (e : W.Proof ≃ ProofReg V)
    (hE : W.acceptanceOperator =
      (1 - Matrix.blockDiagonal (claimRejection V)).submatrix e e)
    (hyes : V.AcceptsSomeProof (2/3)) : W.AcceptsSomeProof 1 := by
  obtain ⟨ρ,hρ,ht,hzero⟩ := honest_full_state V hyes
  refine ⟨ρ.submatrix e e,⟨hρ.submatrix _,(trace_reindex e ρ).trans ht⟩,?_⟩
  change (1 : ℝ) ≤ (W.acceptanceOperator * ρ.submatrix e e).trace.re
  rw [hE,trace_product_reindex,Matrix.sub_mul,Matrix.one_mul,Matrix.trace_sub,ht]
  simp only [Complex.sub_re,Complex.one_re,hzero,sub_zero,le_refl]



end QMAPerfectCompleteness.Main.CoherentCertificate

end



/-! The complete literal coherent-certificate verifier. It initializes η, computes the
certificate-dependent arithmetic and validity, executes the exact dynamic block circuit,
and sets one physical accepting output iff the certificate is valid and Z is nonzero. -/
open Matrix
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace QMAPerfectCompleteness.Main.CyclicVerifier
end QMAPerfectCompleteness.Main.CyclicVerifier
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.CyclicVerifier
open BlockCircuit CertificateCoordinates CertificateMasterLayout CertificateVerifierLayout
open CoherentCertificate CertificatePreparation






























/-- Honest certificates/history give acceptance exactly one in the literal physical verifier. -/
theorem solution (V : Verifier gatesG2) (hyes : V.AcceptsSomeProof (2/3)) :
    (compileVerifier V).AcceptsSomeProof 1 :=
  acceptsSome_of_effect V (compileVerifier V) (proofEquiv V) (acceptanceOperator V) hyes
