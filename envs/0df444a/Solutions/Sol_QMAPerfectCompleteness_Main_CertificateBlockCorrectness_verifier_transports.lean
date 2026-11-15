-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.CertificateBlockCorrectness.verifier_transports
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T16:45:49.79584+00:00
-- url     : https://prove2.me/submissions/824c2d8e-f4f1-40b9-b1f5-41ac101e03d7

/- Generated from Solutions.CertificateQuantumTransports by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
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
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateBlockCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateHadamardCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateLogicalSelect
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterHistory
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMixture
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateQuantumTransports
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateRangeCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateReadout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateValidity
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateValidityCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateVerifierCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateVerifierLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentCertificate
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_Dyadic
import Definitions.Def_QMAPerfectCompleteness_Proof_DynamicBlockCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_DynamicRangeLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_IndexHadamards
import Definitions.Def_QMAPerfectCompleteness_Proof_PointwiseSetup
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableComparison
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableHistoryEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierAnalysis
import Theorems.Thm_QMAPerfectCompleteness_Main_BlockVerifierCoordinates_spectator_mask

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.BlockComposition
end QMAPerfectCompleteness.Main.BlockComposition
namespace QMAPerfectCompleteness.Main.BlockTransport
end QMAPerfectCompleteness.Main.BlockTransport
namespace QMAPerfectCompleteness.Main.Certificate
end QMAPerfectCompleteness.Main.Certificate
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof
namespace QMAPerfectCompleteness.Main.CoordinateFibers
end QMAPerfectCompleteness.Main.CoordinateFibers
namespace QMAPerfectCompleteness.Main.BlockHistoryCoordinates
end QMAPerfectCompleteness.Main.BlockHistoryCoordinates
namespace QMAPerfectCompleteness.Main.BlockHadamardCoordinates
end QMAPerfectCompleteness.Main.BlockHadamardCoordinates

/- Inline helpers retained from Solutions.BlockVerifierCoordinates. -/
section


/-! The two literal verifier calls in logical block coordinates, with arbitrary workspace. -/
open Matrix
open scoped Kronecker
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.BlockVerifierCoordinates
open BlockCircuit BlockCoordinates ReversibleGadgets





lemma spectator_coordinates (V : Verifier gatesG2) (w : ℕ)
    (y x : Basis (bodyWires V+w)) :
    (∀ j, (∀ a, verifierEmbedding (V := V) w a ≠ j) → y j = x j) ↔
      (coordinates V w y).1.1 = (coordinates V w x).1.1 ∧
      (coordinates V w y).1.2.1 = (coordinates V w x).1.2.1 ∧
      (coordinates V w y).1.2.2.2 = (coordinates V w x).1.2.2.2 ∧
      (coordinates V w y).2 = (coordinates V w x).2 := by
  rw [spectator_mask]
  change _ ↔ IndexHadamards.bitsEquiv _ (y ∘ indexWire) = IndexHadamards.bitsEquiv _ (x ∘ indexWire) ∧
    clockEquiv V (y ∘ clockWire) = clockEquiv V (x ∘ clockWire) ∧
    y flagWire = x flagWire ∧ (y ∘ workspaceWire = x ∘ workspaceWire)
  simp only [Equiv.apply_eq_iff_eq]

/-- A verifier operator has identity action on index, clock, flag and every workspace bit. -/
theorem placeVerifier_coordinates (V : Verifier gatesG2) (w : ℕ)
    (M : Matrix V.Wire V.Wire ℂ) :
    placeMatrix (verifierEmbedding w) M =
      (logicalVerifier V M ⊗ₖ (1 : Matrix (Basis w) (Basis w) ℂ)).submatrix
        (coordinates V w) (coordinates V w) := by
  ext y x
  rw [placeMatrix_apply]
  simp only [spectator_coordinates,Matrix.submatrix_apply,logicalVerifier,Verifier.onWires,
    Matrix.kroneckerMap_apply,Matrix.one_apply]
  change (if _ then M _ _ else 0) = _
  split_ifs <;> simp_all <;> rfl







end QMAPerfectCompleteness.Main.BlockVerifierCoordinates

end

/- Inline helpers retained from Solutions.BlockImplements. -/
section


/-! Exact realization of the literal paper compiler on the published wire layout. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.BlockImplements
open BlockCompiler BlockCoordinates BlockClockCoordinates ReversibleGadgets







lemma mul_basisEmbedding {α β : Type*} [Fintype α] [Fintype β] (e : α → β)
    (C : Matrix β β ℂ) (y : β) (x : α) : (C*basisEmbedding e) y x = C y (e x) := by
  classical
  simp [Matrix.mul_apply,basisEmbedding,mul_ite]







variable (V : Verifier gatesG2)






































end QMAPerfectCompleteness.Main.BlockImplements

end

/- Inline helpers retained from Solutions.CoordinateFibers. -/
section


/-! Matrix transport on a workspace fiber determined by conserved classical coordinates. -/
open Matrix
namespace QMAPerfectCompleteness.Main.CoordinateFibers

variable {P A K W : Type*} [Fintype A] [DecidableEq P] [DecidableEq W]

/-- Workspace computed from a conserved key may remain present during a quantum operation.
The conclusion is the exact matrix-column intertwining equation used in coherent circuits. -/
theorem column (coords : P ≃ A × W) (key : A → K)
    (U : Matrix A A ℂ) (C : Matrix P P ℂ)
    (hC : ∀ y x, C y x = U (coords y).1 (coords x).1 *
      (if (coords y).2 = (coords x).2 then 1 else 0))
    (hu : ∀ a b, key a ≠ key b → U a b = 0)
    (e : A → P) (s : K → W) (he : ∀ a, coords (e a) = (a,s (key a)))
    (y : P) (a : A) :
    C y (e a) = ∑ b, (if y=e b then (1 : ℂ) else 0) * U b a := by
  classical
  have hd (b : A) : (coords (e b)).1 = b := congrArg Prod.fst (he b)
  have hsum : (∑ b, (if y=e b then (1 : ℂ) else 0)*U b a) =
      if y=e (coords y).1 then U (coords y).1 a else 0 := by
    rw [Finset.sum_eq_single (coords y).1]
    · split_ifs <;> simp
    · intro b _ hb
      have hy : y ≠ e b := by intro hy; exact hb ((congrArg (fun z => (coords z).1) hy).trans (hd b)).symm
      simp [hy]
    · simp
  rw [hsum,hC,he]
  have hy : y=e (coords y).1 ↔ (coords y).2=s (key (coords y).1) := by
    rw [← coords.apply_eq_iff_eq,he,Prod.ext_iff]
    simp
  simp only [hy]
  by_cases hk : key (coords y).1 = key a
  · simp only [hk]
    split_ifs <;> simp
  · rw [hu _ _ hk]
    simp

end QMAPerfectCompleteness.Main.CoordinateFibers

end

/- Inline helpers retained from Solutions.CertificateVerifierCoordinates. -/
section


/-! Lift the two quantum calls through retained certificate and workspace coordinates. -/
open Matrix
open scoped Kronecker
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.CertificateVerifierCoordinates
open BlockCircuit BlockCoordinates CertificateCoordinates BlockVerifierCoordinates ReversibleGadgets



lemma prefix_mask (n q : ℕ) (y x : Basis (n+q)) :
    (∀ j, (∀ a, prefixEmbedding n q a ≠ j) → y j=x j) ↔
      (splitBasis n q y).2 = (splitBasis n q x).2 := by
  constructor
  · intro h
    funext j
    apply h
    intro a ha
    have hv := congrArg Fin.val ha
    have ha' := a.isLt
    change a.val=n+j.val at hv
    omega
  · intro h j
    refine Fin.addCases (m := n) (n := q) (fun a => ?_) (fun a => ?_) j
    · intro hj; exact (hj a rfl).elim
    · intro _; exact congrFun h a

lemma placePrefix (n q : ℕ) (A : Matrix (Basis n) (Basis n) ℂ) :
    placeMatrix (prefixEmbedding n q) A =
      (A ⊗ₖ (1 : Matrix (Basis q) (Basis q) ℂ)).submatrix (splitBasis n q) (splitBasis n q) := by
  ext y x
  rw [placeMatrix_apply]
  simp only [prefix_mask]
  simp only [Matrix.submatrix_apply,Matrix.kroneckerMap_apply,Matrix.one_apply]
  split_ifs <;> simp <;> rfl

/-- Reordering (body,work),certificate to (body,certificate),work preserves the tensor operator. -/
lemma prefix_coordinates (V : Verifier gatesG2) (w : ℕ)
    (A : Matrix (V.BlockReg (indexQubits V)) (V.BlockReg (indexQubits V)) ℂ) :
    placeMatrix (prefixEmbedding (bodyWires V+w) (claimQubits V))
      ((A ⊗ₖ (1 : Matrix (Basis w) (Basis w) ℂ)).submatrix (coordinates V w) (coordinates V w)) =
      (((A ⊗ₖ (1 : Matrix (CertificateMixture.Claim V) (CertificateMixture.Claim V) ℂ)) ⊗ₖ
        (1 : Matrix (Basis w) (Basis w) ℂ))).submatrix
        (computationEquiv V w) (computationEquiv V w) := by
  rw [placePrefix]
  ext y x
  simp only [Matrix.submatrix_apply,Matrix.kroneckerMap_apply,Matrix.one_apply]
  change (A (coordinates V w (splitBasis _ _ y).1).1 (coordinates V w (splitBasis _ _ x).1).1 *
    (if (coordinates V w (splitBasis _ _ y).1).2 = (coordinates V w (splitBasis _ _ x).1).2 then 1 else 0)) *
      (if (splitBasis _ _ y).2 = (splitBasis _ _ x).2 then 1 else 0) =
    (A (coordinates V w (splitBasis _ _ y).1).1 (coordinates V w (splitBasis _ _ x).1).1 *
      (if claimEquiv V (splitBasis _ _ y).2 = claimEquiv V (splitBasis _ _ x).2 then 1 else 0)) *
        (if (coordinates V w (splitBasis _ _ y).1).2 = (coordinates V w (splitBasis _ _ x).1).2 then 1 else 0)
  simp only [Equiv.apply_eq_iff_eq]
  ring





theorem physicalCall_coordinates (V : Verifier gatesG2) (w : ℕ) (M : Matrix V.Wire V.Wire ℂ) :
    physicalCall V w M =
      (logicalCall V M ⊗ₖ (1 : Matrix (Basis w) (Basis w) ℂ)).submatrix
        (computationEquiv V w) (computationEquiv V w) := by
  rw [physicalCall,placeVerifier_coordinates,prefix_coordinates]
  rfl



lemma logicalCall_key (V : Verifier gatesG2) (M : Matrix V.Wire V.Wire ℂ)
    (p q : CoherentCertificate.ComputationReg V) (h : key V p ≠ key V q) : logicalCall V M p q = 0 := by
  by_cases hc : p.2=q.2
  · have hi : p.1.1 ≠ q.1.1 := fun hi => h (Prod.ext hi hc)
    simp [logicalCall,logicalVerifier,Verifier.onWires,Matrix.kroneckerMap_apply,Matrix.one_apply,hi]
  · simp [logicalCall,Matrix.kroneckerMap_apply,Matrix.one_apply,hc]

/-- Quantum simulation on an arbitrary index/certificate-dependent arithmetic workspace fiber. -/
theorem verifier_fiber (V : Verifier gatesG2) (w : ℕ) (M : Matrix V.Wire V.Wire ℂ)
    (e : CoherentCertificate.ComputationReg V → Basis ((bodyWires V+w)+claimQubits V))
    (s : (Fin (2^indexQubits V) × CertificateMixture.Claim V) → Basis w)
    (he : ∀ p, computationEquiv V w (e p) = (p,s (key V p)))
    (y : Basis ((bodyWires V+w)+claimQubits V)) (p : CoherentCertificate.ComputationReg V) :
    physicalCall V w M y (e p) =
      ∑ q, (if y=e q then (1 : ℂ) else 0) * logicalCall V M q p := by
  apply CoordinateFibers.column (computationEquiv V w) (key V) (logicalCall V M) (physicalCall V w M)
  · intro y x
    rw [physicalCall_coordinates]
    rfl
  · exact logicalCall_key V M
  · exact he








end QMAPerfectCompleteness.Main.CertificateVerifierCoordinates

end

/- Inline helpers retained from Solutions.CertificateBlockCorrectness. -/
section


/-! Exact coherent block SELECT on the master certificate register layout. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.CertificateBlockCorrectness
open CertificateMasterLayout CertificateCoordinates BlockCoordinates BlockCompiler
open ReversibleGadgets BlockImplements
variable (V : Verifier gatesG2)










@[simp] lemma coords_embed (s : Key V → Basis (work V)) (p : Logical V) :
    coords V (embed V s p) = (p,s (key V p)) := (coords V).apply_symm_apply _



















































end QMAPerfectCompleteness.Main.CertificateBlockCorrectness

end



/-! Quantum calls and both H banks on the prepared arithmetic workspace fibers. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix
namespace QMAPerfectCompleteness.Main.CertificateBlockCorrectness
end QMAPerfectCompleteness.Main.CertificateBlockCorrectness
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.CertificateBlockCorrectness
open CertificateMasterLayout BlockImplements
variable (V : Verifier gatesG2)

theorem solution (s : Key V → Basis (work V)) (M : Matrix V.Wire V.Wire ℂ) :
    Transports (embed V s) (embed V s)
      (CertificateVerifierCoordinates.physicalCall V (work V) M)
      (CertificateVerifierCoordinates.logicalCall V M) := by
  ext y p
  rw [mul_basisEmbedding,Matrix.mul_apply,
    CertificateVerifierCoordinates.verifier_fiber V (work V) M (embed V s) s (coords_embed V s) y p]
  apply Finset.sum_congr rfl
  intro q _
  by_cases he : y=embed V s q <;> simp [basisEmbedding,he]
