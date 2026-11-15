-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.CyclicVerifier.soundness
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T17:28:42.828436+00:00
-- url     : https://prove2.me/submissions/0c784a6c-e60a-4ab5-a059-3ca1a8c63ddc

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















lemma pureDensity_trace [DecidableEq ι] (v : ι → ℂ) :
    (pureDensity v).trace = ((euclidNorm v ^ 2 : ℝ) : ℂ) := by
  rw [pureDensity, Matrix.trace_vecMulVec, euclidNorm_sq]
  simp [dotProduct, Complex.mul_conj, Complex.normSq_eq_norm_sq]





/-- Squared norm as the quadratic form of a Gram matrix. -/
lemma gram_expectation [DecidableEq ι] (B : Matrix κ ι ℂ) (v : ι → ℂ) :
    star v ⬝ᵥ ((Bᴴ * B) *ᵥ v) = ((euclidNorm (B *ᵥ v) ^ 2 : ℝ) : ℂ) := by
  classical
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose,
    star_star, dotProduct_comm]
  simpa [pureDensity, Matrix.trace_vecMulVec] using pureDensity_trace (B *ᵥ v)

/-- The trace pairing of positive matrices is nonnegative even when they do not commute. -/
lemma trace_mul_posSemidef_nonneg [DecidableEq ι] (A R : Matrix ι ι ℂ)
    (hA : A.PosSemidef) (hR : R.PosSemidef) : 0 ≤ (A * R).trace.re := by
  obtain ⟨S, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hR.nonneg
  have hp := (hA.mul_mul_conjTranspose_same S).trace_nonneg
  have ht : (S * A * Sᴴ).trace = (A * (star S * S)).trace := by
    rw [Matrix.trace_mul_cycle, star_eq_conjTranspose, Matrix.trace_mul_comm]
  rw [ht] at hp
  exact (Complex.nonneg_iff.mp hp).1

/-- A uniform quadratic-form bound extends to every density matrix. -/
lemma mixed_bound_of_quadratic [DecidableEq ι] (E : Matrix ι ι ℂ) (q : ℝ)
    (hE : E.IsHermitian)
    (hq : ∀ v : ι → ℂ, q * euclidNorm v ^ 2 ≤ (star v ⬝ᵥ (E *ᵥ v)).re)
    (ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1) :
    q ≤ (E * ρ).trace.re := by
  have hpos : (E - (q : ℂ) • (1 : Matrix ι ι ℂ)).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · exact hE.sub (Matrix.isHermitian_one.smul (show IsSelfAdjoint (q : ℂ) from by simp [IsSelfAdjoint]))
    · intro v
      apply Complex.nonneg_iff.mpr
      constructor
      · have hv := hq v
        have hs : star v ⬝ᵥ v = ((euclidNorm v ^ 2 : ℝ) : ℂ) := by
          rw [dotProduct_comm]
          simpa [pureDensity, Matrix.trace_vecMulVec] using pureDensity_trace v
        simpa [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub,
          dotProduct_smul, hs, ← Complex.ofReal_pow] using sub_nonneg.mpr hv
      · exact ((hE.sub (Matrix.isHermitian_one.smul (show IsSelfAdjoint (q : ℂ) from by simp [IsSelfAdjoint]))).im_star_dotProduct_mulVec_self v).symm
  have hp := trace_mul_posSemidef_nonneg _ ρ hpos hρ
  simpa [Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul,
    htrace] using hp

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











/-- Validity enforces the claimed closing value Γ ≥ 2, including dishonest certificates. -/
theorem certificate_ratio_ge_two (V : Verifier gatesG2) (a b : ℕ)
    (hvalid : IsValidCertificate V a b) : 2 ≤ (a : ℝ) / b := by
  rcases hvalid with ⟨_, hb, _, _, _, _, hab⟩
  apply (le_div_iff₀ (by exact_mod_cast hb : (0 : ℝ) < b)).2
  exact_mod_cast hab

/-- Validity makes the exact block coefficient a constant fraction of the index space. -/
theorem certificate_coefficient_ge_eighth (V : Verifier gatesG2) (a b : ℕ)
    (hvalid : IsValidCertificate V a b) :
    (1 : ℝ) / 8 ≤ (a : ℝ) / (2 : ℝ) ^ indexQubits V := by
  rcases hvalid with ⟨_, _, _, _, hscale, _, _⟩
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ indexQubits V)).2
  have hscale' : (2 : ℝ) ^ indexQubits V ≤ 8 * (a : ℝ) := by exact_mod_cast hscale
  linarith

/-- Lemma 3.4(ii), specialized to every valid claimed certificate, not only the honest one. -/
theorem dishonest_history_gap (V : Verifier gatesG2)
    (hno : V.AcceptsAllProofsAtMost (1 / 3)) (z : V.Proof) (a b : ℕ)
    (hvalid : IsValidCertificate V a b) (ψ : History V → ℂ) :
    (1 / 3) * euclidNorm ψ ≤
      euclidNorm ((1 - V.cyclicOp z ((a : ℝ) / b)) *ᵥ ψ) := by
  exact (QMAPerfectCompleteness.Main.cyclic_constraint V).2 hno z _ (certificate_ratio_ge_two V a b hvalid) ψ





end QMAPerfectCompleteness.Main.ProofSetup

end

/- Inline helpers retained from Solutions.VerifierAnalysis. -/
section


open Matrix
open scoped ComplexOrder

namespace QMAPerfectCompleteness.Main.VerifierAnalysis



/-- Equation (8) of the paper, retaining exact rational coefficients. -/
theorem rejectionProbability_eq (V : Verifier gatesG2) (z : V.Proof) (a b : ℕ)
    (hv : IsValidCertificate V a b) (ψ : History V → ℂ) :
    rejectionProbability V z a b ψ =
      ((a : ℝ) / (2 : ℝ) ^ indexQubits V) ^ 2 *
        euclidNorm ((1 - V.cyclicOp z ((a : ℝ) / b)) *ᵥ ψ) ^ 2 := by
  unfold rejectionProbability ProofSetup.rejectionBlock
  rw [BlockProof.exact_block_identity V z a b hv, Matrix.smul_mulVec, euclidNorm_smul, mul_pow]
  simp





/-- Homogeneous soundness bound, before normalizing the history. -/
theorem dishonest_rejection_homogeneous (V : Verifier gatesG2)
    (hno : V.AcceptsAllProofsAtMost (1 / 3)) (z : V.Proof) (a b : ℕ)
    (hv : IsValidCertificate V a b) (ψ : History V → ℂ) :
    (1 : ℝ) / 576 * euclidNorm ψ ^ 2 ≤ rejectionProbability V z a b ψ := by
  rw [rejectionProbability_eq V z a b hv ψ]
  let r : ℝ := (a : ℝ) / (2 : ℝ) ^ indexQubits V
  let d : ℝ := euclidNorm ((1 - V.cyclicOp z ((a : ℝ) / b)) *ᵥ ψ)
  let n : ℝ := euclidNorm ψ
  have hr : (1 : ℝ) / 8 ≤ r := ProofSetup.certificate_coefficient_ge_eighth V a b hv
  have hd : (1 / 3) * n ≤ d := ProofSetup.dishonest_history_gap V hno z a b hv ψ
  have hn : 0 ≤ n := euclidNorm_nonneg ψ
  have hd0 : 0 ≤ d := euclidNorm_nonneg _
  have hr2 : (1 : ℝ) / 64 ≤ r ^ 2 := by nlinarith
  have hd2 : (1 : ℝ) / 9 * n ^ 2 ≤ d ^ 2 := by nlinarith
  calc
    (1 : ℝ) / 576 * n ^ 2 = (1 / 64) * ((1 / 9) * n ^ 2) := by ring
    _ ≤ r ^ 2 * d ^ 2 := mul_le_mul hr2 hd2 (mul_nonneg (by norm_num) (sq_nonneg n)) (sq_nonneg r)



end QMAPerfectCompleteness.Main.VerifierAnalysis

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

lemma blockDiagonal_quadratic (E : C → Matrix ι ι ℂ) (ψ : ι × C → ℂ) :
    (star ψ ⬝ᵥ (Matrix.blockDiagonal E *ᵥ ψ)).re =
      ∑ c, (star (fun i => ψ (i, c)) ⬝ᵥ (E c *ᵥ fun i => ψ (i, c))).re := by
  simp only [dotProduct, Fintype.sum_prod_type, blockDiagonal_mulVec,
    star_apply, Complex.re_sum]
  exact Finset.sum_comm

lemma euclidNorm_prod_sq (ψ : ι × C → ℂ) :
    euclidNorm ψ ^ 2 = ∑ c, euclidNorm (fun i => ψ (i, c)) ^ 2 := by
  simp only [euclidNorm_sq, Fintype.sum_prod_type]
  exact Finset.sum_comm

lemma blockDiagonal_hermitian (E : C → Matrix ι ι ℂ) (hE : ∀ c, (E c).IsHermitian) :
    (Matrix.blockDiagonal E).IsHermitian := by
  ext ⟨i, c⟩ ⟨j, d⟩
  by_cases h : c = d
  · subst d
    simpa [Matrix.conjTranspose_apply] using congrFun (congrFun (hE c) i) j
  · simp [Matrix.conjTranspose_apply, Matrix.blockDiagonal_apply, h, Ne.symm h]

/-- Keeping a certificate register coherently gives the same bound as averaging its measured
outcomes, including when the certificate and history start entangled. -/
theorem mixed_certificate_bound (E : C → Matrix ι ι ℂ) (q : ℝ)
    (hE : ∀ c, (E c).IsHermitian)
    (hq : ∀ c (v : ι → ℂ), q * euclidNorm v ^ 2 ≤ (star v ⬝ᵥ (E c *ᵥ v)).re)
    (ρ : Matrix (ι × C) (ι × C) ℂ) (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1) :
    q ≤ (Matrix.blockDiagonal E * ρ).trace.re := by
  apply mixed_bound_of_quadratic _ q (blockDiagonal_hermitian E hE) _ ρ hρ htrace
  intro ψ
  rw [euclidNorm_prod_sq, blockDiagonal_quadratic, Finset.mul_sum]
  exact Finset.sum_le_sum fun c _ => hq c _





lemma claimRejection_hermitian (V : Verifier gatesG2) (c : Claim V) :
    (claimRejection V c).IsHermitian := by
  classical
  unfold claimRejection
  split_ifs
  · exact Matrix.isHermitian_conjTranspose_mul_self _
  · exact Matrix.isHermitian_one

lemma claim_quadratic_bound (V : Verifier gatesG2)
    (hno : V.AcceptsAllProofsAtMost (1 / 3)) (c : Claim V) (ψ : History V → ℂ) :
    (1 : ℝ) / 576 * euclidNorm ψ ^ 2 ≤ (star ψ ⬝ᵥ (claimRejection V c *ᵥ ψ)).re := by
  classical
  unfold claimRejection
  split_ifs with hv
  · rw [gram_expectation]
    simpa [rejectionProbability, ← Complex.ofReal_pow] using
      dishonest_rejection_homogeneous V hno c.1 c.2.1 c.2.2 hv ψ
  · rw [Matrix.one_mulVec]
    have hs : star ψ ⬝ᵥ ψ = ((euclidNorm ψ ^ 2 : ℝ) : ℂ) := by
      rw [dotProduct_comm]
      simpa [pureDensity, Matrix.trace_vecMulVec] using pureDensity_trace ψ
    rw [hs, Complex.ofReal_re]
    nlinarith [sq_nonneg (euclidNorm ψ)]

/-- The full certificate/history register has rejection at least 1/576 on NO inputs, even for
an arbitrary entangled proof and including all invalid certificate outcomes. -/
theorem full_mixed_rejection_bound (V : Verifier gatesG2)
    (hno : V.AcceptsAllProofsAtMost (1 / 3))
    (ρ : Matrix (History V × Claim V) (History V × Claim V) ℂ)
    (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1) :
    (1 : ℝ) / 576 ≤ (Matrix.blockDiagonal (claimRejection V) * ρ).trace.re := by
  classical
  exact mixed_certificate_bound _ _ (claimRejection_hermitian V)
    (claim_quadratic_bound V hno) ρ hρ htrace









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



/-- The effect equality implies soundness for every complex mixed proof, including arbitrary
entanglement between the certificate and history. -/
theorem acceptsAll_of_effect {G : GateSet} (V : Verifier gatesG2) (W : Verifier G)
    (e : W.Proof ≃ ProofReg V)
    (hE : W.acceptanceOperator =
      (1 - Matrix.blockDiagonal (claimRejection V)).submatrix e e)
    (hno : V.AcceptsAllProofsAtMost (1/3)) : W.AcceptsAllProofsAtMost (1-1/576) := by
  intro ρ hρ
  let σ := ρ.submatrix e.symm e.symm
  have hσ : σ.PosSemidef := hρ.1.submatrix _
  have ht : σ.trace = 1 := (trace_reindex e.symm ρ).trans hρ.2
  have hb := full_mixed_rejection_bound V hno σ hσ ht
  have hi : σ.submatrix e e = ρ := by simp [σ,Matrix.submatrix_submatrix]
  change (W.acceptanceOperator * ρ).trace.re ≤ 1-1/576
  rw [← hi,hE,trace_product_reindex,Matrix.sub_mul,Matrix.one_mul,Matrix.trace_sub,ht]
  simp only [Complex.sub_re,Complex.one_re]
  linarith

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
































/-- Every mixed or entangled certificate/history proof is accepted with probability ≤575/576. -/
theorem solution (V : Verifier gatesG2) (hno : V.AcceptsAllProofsAtMost (1/3)) :
    (compileVerifier V).AcceptsAllProofsAtMost (1-1/576) :=
  acceptsAll_of_effect V (compileVerifier V) (proofEquiv V) (acceptanceOperator V) hno
