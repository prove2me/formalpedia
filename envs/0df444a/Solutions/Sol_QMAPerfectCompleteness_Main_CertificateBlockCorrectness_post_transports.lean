-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.CertificateBlockCorrectness.post_transports
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T16:52:48.293743+00:00
-- url     : https://prove2.me/submissions/cd615b22-a9ff-4242-9de6-400e26f84551

/- Generated from Solutions.CertificatePostCorrectness by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateClosingActions
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateClosingCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateHadamardCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateHistoryCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateHistoryPrograms
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateLogicalSelect
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterHistory
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMixture
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateOldPrograms
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificatePostCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateRangeCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateReadout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateStageActions
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
import Theorems.Thm_QMAPerfectCompleteness_Main_CertificateBlockCorrectness_increment_transports

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

/- Inline helpers retained from Solutions.ReversibleGadgets. -/
section


/-! Explicit G₂ circuit gadgets used by the block-encoding compiler. -/

open Matrix
open scoped Kronecker

namespace QMAPerfectCompleteness.Main.ReversibleGadgets



































/-- A paired Hadamard on its entire local two-wire register. -/
theorem hhAt_id_matrix :
    (hhAt (Function.Embedding.refl (Fin 2))).matrix = hadamardTwoMatrix := by
  ext y x
  change (if (∀ w : Fin 2, (∀ a : Fin 2, a ≠ w) → y w = x w) then
    hadamardTwoMatrix y x else 0) = hadamardTwoMatrix y x
  have h : ∀ w : Fin 2, (∀ a : Fin 2, a ≠ w) → y w = x w := by
    intro w hw
    exact (hw w rfl).elim
  rw [if_pos h]

private theorem sum_basis_two (f : Basis 2 → ℂ) :
    ∑ x, f x = f ![false,false] + f ![false,true] +
      f ![true,false] + f ![true,true] := by
  have huniv : (Finset.univ : Finset (Basis 2)) =
      {![false,false], ![false,true], ![true,false], ![true,true]} := by decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_pair (by decide)]
  ring

/-- The three-gate exact sign gadget is Z tensor I; its dummy wire is restored for every input,
not only when initially zero. -/
theorem phaseZ_matrix : circuitMatrix phaseZ =
    Matrix.diagonal (fun x : Basis 2 => if x 0 then (-1 : ℂ) else 1) := by
  classical
  simp only [phaseZ, circuitMatrix, Matrix.one_mul, hhAt_id_matrix, xAt_matrix]
  ext y x
  obtain ⟨a,b,rfl⟩ : ∃ a b, y = ![a,b] := ⟨y 0, y 1, by funext i; fin_cases i <;> rfl⟩
  obtain ⟨c,d,rfl⟩ : ∃ c d, x = ![c,d] := ⟨x 0, x 1, by funext i; fin_cases i <;> rfl⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [Matrix.mul_apply, sum_basis_two, hadamardTwoMatrix, classicalMatrix,
      xAction, funext_iff, Fin.forall_fin_two]

















/-- It applies (-1) on a true predicate wire and otherwise acts identically on the full register. -/
theorem phaseZAt_matrix {n : ℕ} (e : Fin 2 ↪ Fin n) :
    circuitMatrix (phaseZAt e) =
      placeMatrix e (Matrix.diagonal fun x : Basis 2 => if x 0 then (-1 : ℂ) else 1) := by
  rw [phaseZAt, circuitMatrix_mapWires, phaseZ_matrix]





/-- Diagonal phases lift to diagonal phases on the selected bits of the full register. -/
theorem placeMatrix_diagonal {r n : ℕ} (e : Fin r ↪ Fin n) (f : Basis r → ℂ) :
    placeMatrix e (Matrix.diagonal f) = Matrix.diagonal (fun x : Basis n => f (x ∘ e)) := by
  classical
  ext y x
  rw [placeMatrix_apply]
  change (if (∀ w, (∀ a, e a ≠ w) → y w = x w) then
      if y ∘ e = x ∘ e then f (y ∘ e) else 0 else 0) =
    if y = x then f (y ∘ e) else 0
  have hiff : (∀ w, (∀ a, e a ≠ w) → y w = x w) ∧ y ∘ e = x ∘ e ↔ y = x := by
    constructor
    · rintro ⟨hu, he⟩
      apply (CircuitProof.splitTargets e).injective
      exact Prod.ext he ((CircuitProof.unaffected_iff e x y).mp hu)
    · intro h
      subst y
      simp
  simp only [← ite_and, hiff]

/-- Full-register semantics: the first selected wire supplies the sign; every wire is preserved. -/
theorem phaseZAt_matrix_diagonal {n : ℕ} (e : Fin 2 ↪ Fin n) :
    circuitMatrix (phaseZAt e) =
      Matrix.diagonal (fun x : Basis n => if x (e 0) then (-1 : ℂ) else 1) := by
  rw [phaseZAt_matrix, placeMatrix_diagonal]
  rfl























end QMAPerfectCompleteness.Main.ReversibleGadgets

end

/- Inline helpers retained from Solutions.BlockCompiler. -/
section


/-! Concrete paper block-compiler scaffolds. Circuit data depend only on layout and certificate. -/

open Matrix
namespace QMAPerfectCompleteness.Main.BlockCompiler
open ReversibleGadgets ControlCircuits EqualityCircuits ComparisonCircuits ClockCircuits





namespace CleanProgram





end CleanProgram

namespace Layout

































































































































































lemma clock_ne_flag (D : Layout) (i : Fin D.clock) : D.clockWire i ≠ D.flagWire := by
  intro h
  have hv := congrArg Fin.val h
  change D.index+(i : ℕ) = D.index+D.clock+(D.proof+D.ancilla) at hv
  have := i.isLt
  omega























































































end Layout











end QMAPerfectCompleteness.Main.BlockCompiler

end

/- Inline helpers retained from Solutions.BlockCoordinates. -/
section


/-! Exact basis coordinates for the published block register, including clean workspace. -/
open Matrix
namespace QMAPerfectCompleteness.Main.BlockCoordinates
open BlockCircuit IndexHadamards































theorem coordinates_fst (V : Verifier gatesG2) (w : ℕ) (x : Basis (bodyWires V+w)) :
    (coordinates V w x).1 = decode x := by
  apply Prod.ext
  · apply Fin.ext
    change ComparisonCircuits.littleValue (x ∘ indexWire) =
      ComparisonCircuits.littleValue (x ∘ indexWire) % 2^indexQubits V
    exact (Nat.mod_eq_of_lt (ComparisonCircuits.littleValue_lt_two_pow _)).symm
  · apply Prod.ext
    · apply Fin.ext
      change ComparisonCircuits.littleValue (x ∘ clockWire) =
        bitsValue x clockWire % (ell V.proofQubits+1)
      rw [clock_card]
      exact (Nat.mod_eq_of_lt (ComparisonCircuits.littleValue_lt_two_pow (x ∘ clockWire))).symm
    · rfl



















end QMAPerfectCompleteness.Main.BlockCoordinates

end

/- Inline helpers retained from Solutions.CertificateCoordinates. -/
section


/-! Concrete qubit coordinates for a coherent binary certificate and its history proof. -/
namespace QMAPerfectCompleteness.Main.CertificateCoordinates
open BlockCircuit BlockCoordinates IndexHadamards CertificateMixture














@[simp] theorem computationEquiv_body (V : Verifier gatesG2) (w : ℕ)
    (x : Basis ((bodyWires V+w)+claimQubits V)) :
    (computationEquiv V w x).1.1 = decode (fun i => x (Fin.castAdd (claimQubits V) i)) :=
  coordinates_fst V w _

@[simp] theorem computationEquiv_claim (V : Verifier gatesG2) (w : ℕ)
    (x : Basis ((bodyWires V+w)+claimQubits V)) :
    (computationEquiv V w x).1.2 = claimEquiv V (fun i => x (Fin.natAdd (bodyWires V+w) i)) := rfl



end QMAPerfectCompleteness.Main.CertificateCoordinates

end

/- Inline helpers retained from Solutions.BlockStateCoordinates. -/
section


/-! Pure basis-state identities for the concrete block compiler's register layout. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Matrix
namespace QMAPerfectCompleteness.Main.BlockStateCoordinates
open BlockCompiler BlockCoordinates
variable (V : Verifier gatesG2)







lemma index_ne_flag (i : Fin (D V).index) : (D V).indexWire i ≠ (D V).flagWire := by
  intro h
  have hv := congrArg Fin.val h
  change i.val = (D V).index+(D V).clock+((D V).proof+(D V).ancilla) at hv
  have := i.isLt
  omega

lemma verifier_ne_flag (i : Fin ((D V).proof+(D V).ancilla)) :
    (D V).verifierWire i ≠ (D V).flagWire := by
  intro h
  have hv := congrArg Fin.val h
  change (D V).index+(D V).clock+i.val = (D V).index+(D V).clock+((D V).proof+(D V).ancilla) at hv
  have := i.isLt
  omega



lemma decode_update_flag (x : Physical V) (b : Bool) :
    BlockCircuit.decode (Function.update x (D V).flagWire b) =
      ((BlockCircuit.decode x).1,(BlockCircuit.decode x).2.1,(BlockCircuit.decode x).2.2.1,b) := by
  apply Prod.ext
  · change Fin.ofNat _ (BlockCircuit.bitsValue (Function.update x (D V).flagWire b) (D V).indexWire) = _
    congr 1
    unfold BlockCircuit.bitsValue
    simp_rw [Function.update_of_ne (index_ne_flag V _)]
    rfl
  · apply Prod.ext
    · change Fin.ofNat _ (BlockCircuit.bitsValue (Function.update x (D V).flagWire b) (D V).clockWire) = _
      congr 1
      unfold BlockCircuit.bitsValue
      simp_rw [Function.update_of_ne ((D V).clock_ne_flag _)]
      rfl
    · apply Prod.ext
      · funext i
        exact Function.update_of_ne (verifier_ne_flag V i) b x
      · exact Function.update_self _ _ _



end QMAPerfectCompleteness.Main.BlockStateCoordinates

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





theorem transports_mul {α β : Type*} [Fintype α] [Fintype β]
    (e f g : α → β) (C D : Matrix β β ℂ) (U W : Matrix α α ℂ)
    (hC : Transports f g C U) (hD : Transports e f D W) :
    Transports e g (C*D) (U*W) := by
  unfold Transports at *
  rw [Matrix.mul_assoc,hD,← Matrix.mul_assoc,hC,Matrix.mul_assoc]

lemma mul_basisEmbedding {α β : Type*} [Fintype α] [Fintype β] (e : α → β)
    (C : Matrix β β ℂ) (y : β) (x : α) : (C*basisEmbedding e) y x = C y (e x) := by
  classical
  simp [Matrix.mul_apply,basisEmbedding,mul_ite]



lemma basisEmbedding_mul_classical {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (e : α → β) (f : α → α) (y : β) (x : α) :
    (basisEmbedding e * basisMap f) y x = if y = e (f x) then 1 else 0 := by
  classical
  simp [Matrix.mul_apply,basisEmbedding,basisMap,ite_mul,mul_ite]

lemma transports_classical {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (e f : α → β) (C : Matrix β β ℂ) (g : α → α)
    (hc : ∀ y x, C y (e x) = if y = f (g x) then 1 else 0) :
    Transports e f C (basisMap g) := by
  ext y x
  rw [mul_basisEmbedding,basisEmbedding_mul_classical]
  exact hc y x

variable (V : Verifier gatesG2)






































end QMAPerfectCompleteness.Main.BlockImplements

end

/- Inline helpers retained from Solutions.BlockHistoryCoordinates. -/
section


/-! The physical closing equality test in the published logical clock/proof coordinates. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace QMAPerfectCompleteness.Main.BlockHistoryCoordinates
open BlockCompiler BlockCoordinates BlockStateCoordinates ComparisonCircuits ClockCircuits
variable (V : Verifier gatesG2)

lemma littleValue_true (r : ℕ) : littleValue (fun _ : Fin r => true) = 2^r-1 := by
  unfold littleValue
  simp only [Bool.true_eq,ite_true]
  rw [Fin.sum_univ_eq_sum_range]
  simpa using Nat.geomSum_eq (by omega : 2 ≤ 2) r

lemma clockValue_decode (x : Physical V) :
    (D V).clockValue x = (BlockCircuit.decode x).2.1.val := by
  change (D V).clockValue x = (D V).clockValue x % (ell V.proofQubits+1)
  rw [clock_card]
  exact (Nat.mod_eq_of_lt (littleValue_lt_two_pow (x ∘ (D V).clockWire))).symm

lemma clock_all_true_iff (x : Physical V) :
    (∀ i : Fin (D V).clock, x ((D V).clockWire i) = true) ↔
      (BlockCircuit.decode x).2.1.val = ell V.proofQubits := by
  rw [← clockValue_decode]
  have ht : littleValue (fun _ : Fin (D V).clock => true) = ell V.proofQubits := by
    exact littleValue_true _
  constructor
  · intro h
    change littleValue (x ∘ (D V).clockWire) = _
    rw [show x ∘ (D V).clockWire = (fun _ => true) from funext h,ht]
  · intro h
    have he : x ∘ (D V).clockWire = (fun _ => true) :=
      littleValue_injective (h.trans ht.symm)
    exact congrFun he







end QMAPerfectCompleteness.Main.BlockHistoryCoordinates

end

/- Inline helpers retained from Solutions.BlockLogicalActions. -/
section


/-! Deterministic logical matrix entries for flag and clock operations. -/
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.BlockImplements



lemma basisEmbedding_mul_signed {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (e : α → β) (f : α → α) (s : α → ℂ) (y : β) (x : α) :
    (basisEmbedding e * signedMap f s) y x = if y = e (f x) then s x else 0 := by
  classical
  simp [Matrix.mul_apply,basisEmbedding,signedMap,ite_mul,mul_ite]

lemma transports_signed {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (e f : α → β) (C : Matrix β β ℂ) (g : α → α) (s : α → ℂ)
    (hc : ∀ y x, C y (e x) = if y = f (g x) then s x else 0) :
    Transports e f C (signedMap g s) := by
  ext y x
  rw [mul_basisEmbedding,basisEmbedding_mul_signed]
  exact hc y x



variable (V : Verifier gatesG2)







end QMAPerfectCompleteness.Main.BlockImplements

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







lemma old_decode (x : Physical V) : BlockCircuit.decode (old V x) = (coords V x).1.1 := by
  rw [computationEquiv_body]
  rfl

@[simp] lemma embed_decode (s : Key V → Basis (work V)) (p : Logical V) :
    BlockCircuit.decode (old V (embed V s p)) = p.1 := by rw [old_decode,coords_embed]

lemma coords_work (x : Physical V) : (coords V x).2 = x ∘ workWire V := rfl

lemma embed_work (s : Key V → Basis (work V)) (p : Logical V) (i : Fin (work V)) :
    embed V s p (workWire V i) = s (key V p) i :=
  congrFun (congrArg Prod.snd (coords_embed V s p)) i

lemma old_tag_work (i : Fin 11) :
    oldEmbedding V ((layoutOf V).tagWire i) =
      workWire V ⟨i.val,by have := i.isLt; dsimp only [work,oldWork,Layout.work]; omega⟩ := by
  apply Fin.ext
  rfl

lemma old_scratch_work (i : Fin ((layoutOf V).scale+4)) :
    oldEmbedding V ((layoutOf V).scratchWire i) =
      workWire V ⟨11+i.val,by have := i.isLt; dsimp only [work,oldWork,Layout.work]; omega⟩ := by
  apply Fin.ext
  rfl

lemma old_update_flag (x : Physical V) (f : Bool) :
    old V (Function.update x (oldEmbedding V (layoutOf V).flagWire) f) =
      Function.update (old V x) (layoutOf V).flagWire f := by
  funext i
  simp only [old,Function.comp_apply,Function.update_apply,(oldEmbedding V).injective.eq_iff]

lemma flag_ne_work (i : Fin (work V)) :
    oldEmbedding V (layoutOf V).flagWire ≠ workWire V i := by
  intro h
  have hv := congrArg Fin.val h
  change indexQubits V+BlockCircuit.clockWires V+(V.proofQubits+V.ancillaQubits) =
    BlockCircuit.bodyWires V+i.val at hv
  dsimp only [BlockCircuit.bodyWires] at hv
  omega

lemma flag_ne_claim (i : Fin (claimQubits V)) :
    oldEmbedding V (layoutOf V).flagWire ≠ Fin.natAdd (BlockCircuit.bodyWires V+work V) i := by
  intro h
  have hv := congrArg Fin.val h
  change indexQubits V+BlockCircuit.clockWires V+(V.proofQubits+V.ancillaQubits) =
    BlockCircuit.bodyWires V+work V+i.val at hv
  dsimp only [BlockCircuit.bodyWires] at hv
  omega

lemma coords_update_flag (x : Physical V) (f : Bool) :
    coords V (Function.update x (oldEmbedding V (layoutOf V).flagWire) f) =
      ((((coords V x).1.1.1,(coords V x).1.1.2.1,(coords V x).1.1.2.2.1,f),
        (coords V x).1.2),(coords V x).2) := by
  apply Prod.ext
  · apply Prod.ext
    · rw [← old_decode,old_update_flag,BlockStateCoordinates.decode_update_flag,old_decode]
    · rw [computationEquiv_claim,computationEquiv_claim]
      congr 1
      funext i
      exact Function.update_of_ne (flag_ne_claim V i).symm f x
  · rw [coords_work,coords_work]
    funext i
    exact Function.update_of_ne (flag_ne_work V i).symm f x

lemma embed_update_flag (s : Key V → Basis (work V)) (p : Logical V) (f : Bool) :
    Function.update (embed V s p) (oldEmbedding V (layoutOf V).flagWire) f =
      embed V s (((p.1.1,p.1.2.1,p.1.2.2.1,f)),p.2) := by
  apply (coords V).injective
  rw [coords_update_flag,coords_embed,coords_embed]
  rfl



lemma embed_old_flag (s : Key V → Basis (work V)) (p : Logical V) :
    embed V s p (oldEmbedding V (layoutOf V).flagWire) = p.1.2.2.2 :=
  congrArg (fun q : V.BlockReg (indexQubits V) => q.2.2.2) (embed_decode V s p)



















end QMAPerfectCompleteness.Main.CertificateBlockCorrectness

end

/- Inline helpers retained from Solutions.CertificateOldPrograms. -/
section


/-! Literal old block gadgets lifted into the master coherent-certificate register. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix
namespace QMAPerfectCompleteness.Main.CertificateOldPrograms
open CertificateMasterLayout BlockCompiler ReversibleGadgets
variable (V : Verifier gatesG2)





lemma place_update_of_action {r n : ℕ} (e : Fin r ↪ Fin n) (f : Basis r → Basis r)
    (x : Basis n) (w : Fin r) (b : Bool) (h : f (x ∘ e) = Function.update (x ∘ e) w b) :
    placePermutation e f x = Function.update x (e w) b := by
  calc
    placePermutation e f x = placePermutation e (fun u => Function.update u w b) x := by
      unfold placePermutation
      rw [h]
    _ = _ := place_update e w (fun _ => b) x







lemma identityFlag_action (x : Physical V) :
    (identityFlagProgram V).action x = Function.update x (flag V)
      (xor (x (flag V)) (x (oldTags V 0))) := by
  apply place_update_of_action
  rfl







lemma phase_matrix : circuitMatrix (phaseGates V) =
    Matrix.diagonal (fun x : Physical V => if x (oldTags V 5) then (-1 : ℂ) else 1) := by
  rw [phaseGates,circuitMatrix_mapWires,phaseZAt_matrix_diagonal,placeMatrix_diagonal]
  rfl

end QMAPerfectCompleteness.Main.CertificateOldPrograms

end

/- Inline helpers retained from Solutions.CertificateHistoryPrograms. -/
section


/-! Clean compute/use/uncompute of the variable certificate history predicate. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix
namespace QMAPerfectCompleteness.Main.CertificateHistoryPrograms
open BlockCompiler ReversibleGadgets VariableHistoryEquality

namespace Layout
variable {m c n : ℕ} (L : VariableHistoryEquality.Layout m c n)










end Layout



namespace ClosingLayout
variable {m c n : ℕ} (L : ClosingLayout m c n)









lemma predicate_update_flag (x : Basis n) (b : Bool) :
    Layout.predicate L.history (Function.update x L.flag b) = Layout.predicate L.history x := by
  have hl : (Function.update x L.flag b) ∘ VariableComparison.leftWire L.history.equality =
      x ∘ VariableComparison.leftWire L.history.equality := by
    funext j; exact Function.update_of_ne (L.flag_eq _).symm _ _
  have hr : (Function.update x L.flag b) ∘ VariableComparison.rightWire L.history.equality =
      x ∘ VariableComparison.rightWire L.history.equality := by
    funext j; exact Function.update_of_ne (L.flag_eq _).symm _ _
  have hp : L.history.proofMatches (Function.update x L.flag b) ↔ L.history.proofMatches x := by
    unfold VariableHistoryEquality.Layout.proofMatches
    rw [hl,hr]
  have hc : L.history.clockMatches (Function.update x L.flag b) ↔ L.history.clockMatches x := by
    simp only [VariableHistoryEquality.Layout.clockMatches,Function.update_of_ne (L.flag_clock _).symm]
  simp only [Layout.predicate,hp,hc]

lemma historyAction_update_flag (x : Basis n) (b : Bool) :
    Layout.action L.history (Function.update x L.flag b) =
      Function.update (Layout.action L.history x) L.flag b := by
  simp only [Layout.action,L.predicate_update_flag,Function.update_of_ne (L.flag_tags 2).symm]
  exact Function.update_comm (L.flag_tags 2) _ _ _








lemma action_eq (x : Basis n) (h2 : x (L.history.tags 2)=false) :
    L.action x = Function.update x L.flag
      (xor (x L.flag) (x L.range && Layout.predicate L.history x)) := by
  change Layout.action L.history (Function.update (Layout.action L.history x) L.flag
    (xor (Layout.action L.history x L.flag)
      (Layout.action L.history x L.range && Layout.action L.history x (L.history.tags 2)))) = _
  rw [L.historyAction_update_flag,Layout.action_involutive]
  simp [Layout.action,L.flag_tags,L.range_history,h2]

theorem gates_matrix (y x : Basis n) (hx : Layout.Clean L.history x)
    (h2 : x (L.history.tags 2)=false) : circuitMatrix L.gates y x =
      if y=Function.update x L.flag (xor (x L.flag) (x L.range && Layout.predicate L.history x))
      then 1 else 0 := by
  rw [gates,L.program.sound y x hx]
  change (if y=L.action x then (1 : ℂ) else 0) = _
  rw [L.action_eq x h2]



end ClosingLayout
end QMAPerfectCompleteness.Main.CertificateHistoryPrograms

end

/- Inline helpers retained from Solutions.CertificateStageActions. -/
section


/-! Actual deterministic master-register stages on the coherent indexed workspace fiber. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Matrix
namespace QMAPerfectCompleteness.Main.CertificateBlockCorrectness
open CertificateMasterLayout BlockCompiler BlockCoordinates BlockImplements
variable (V : Verifier gatesG2)

lemma tagged_core (s : Key V → Basis (work V)) (p : Logical V) (i : Fin 11) (hi : i.val<6) :
    embed V (taggedSpace V s) p (oldTags V i) =
      Layout.rangeTruth p.2.2.1.val p.2.2.2.val p.1.1.val ⟨i.val,hi⟩ := by
  change embed V (taggedSpace V s) p (oldEmbedding V ((layoutOf V).tagWire i)) = _
  rw [old_tag_work,embed_work]
  exact dif_pos hi

lemma tagged_aux (s : Key V → Basis (work V)) (hs : Prepared V s)
    (p : Logical V) (i : Fin 11) (hi : (6 : ℕ) ≤ i.val) :
    embed V (taggedSpace V s) p (oldTags V i) = false := by
  change embed V (taggedSpace V s) p (oldEmbedding V ((layoutOf V).tagWire i)) = _
  rw [old_tag_work,embed_work]
  change (if h : i.val<6 then _ else s (key V p) _) = false
  rw [dif_neg (by omega)]
  have h := hs.old_clean p ⟨i.val,by have := i.isLt; dsimp only [Layout.work]; omega⟩
  change embed V s p (oldEmbedding V ((layoutOf V).tagWire i)) = false at h
  rw [old_tag_work,embed_work] at h
  exact h

lemma tagged_scratch (s : Key V → Basis (work V)) (hs : Prepared V s) (p : Logical V) :
    (layoutOf V).ScratchClean (old V (embed V (taggedSpace V s) p)) := by
  intro i
  change embed V (taggedSpace V s) p (oldEmbedding V ((layoutOf V).scratchWire i)) = false
  rw [old_scratch_work,embed_work]
  change (if h : 11+i.val<6 then _ else s (key V p) _) = false
  rw [dif_neg (by omega)]
  have h := hs.old_clean p ⟨11+i.val,by have := i.isLt; dsimp only [Layout.work]; omega⟩
  change embed V s p (oldEmbedding V ((layoutOf V).scratchWire i)) = false at h
  rw [old_scratch_work,embed_work] at h
  exact h









lemma identityFlag_action (s : Key V → Basis (work V)) (p : Logical V) :
    (CertificateOldPrograms.identityFlagProgram V).action (embed V (taggedSpace V s) p) =
      embed V (taggedSpace V s)
        ((p.1.1,p.1.2.1,p.1.2.2.1,xor p.1.2.2.2 (Layout.rangeTruth p.2.2.1.val p.2.2.2.val p.1.1.val 0)),p.2) := by
  rw [CertificateOldPrograms.identityFlag_action]
  simp only [CertificateOldPrograms.flag]
  change Function.update (embed V (taggedSpace V s) p) (oldEmbedding V (layoutOf V).flagWire) _ = _
  rw [embed_old_flag,tagged_core V s p 0 (by decide),embed_update_flag]
  rfl

end QMAPerfectCompleteness.Main.CertificateBlockCorrectness

end

/- Inline helpers retained from Solutions.CertificateHistoryCoordinates. -/
section


/-! Master variable-history test in logical body/certificate coordinates. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace QMAPerfectCompleteness.Main.CertificateHistoryCoordinates
open CertificateMasterLayout CertificateCoordinates BlockCompiler CertificateOldPrograms
open VariableComparison
variable (V : Verifier gatesG2)




lemma proof_left (j : Fin V.proofQubits) :
    leftWire (historyEquality V) j = oldEmbedding V
      ((layoutOf V).verifierWire (Fin.castAdd V.ancillaQubits j)) := by
  apply Fin.ext
  change (if j.val<V.proofQubits then indexQubits V+BlockCircuit.clockWires V+j.val else _) = _
  rw [if_pos j.isLt]
  rfl

lemma proof_right (j : Fin V.proofQubits) : rightWire (historyEquality V) j = certZ V j := by
  apply Fin.ext
  change (if V.proofQubits+j.val<V.proofQubits then _ else
    if V.proofQubits+j.val<2*V.proofQubits then
      BlockCircuit.bodyWires V+work V+(V.proofQubits+j.val-V.proofQubits) else _) = _
  have hj := j.isLt
  rw [if_neg (by omega),if_pos (by omega)]
  change BlockCircuit.bodyWires V+work V+(V.proofQubits+j.val-V.proofQubits) = BlockCircuit.bodyWires V+work V+j.val
  omega

lemma equality_carry (j : Fin (V.proofQubits+1)) :
    carryWire (historyEquality V) j = oldEmbedding V ((layoutOf V).scratchWire
      ⟨j.val,by have := j.isLt; dsimp only [Layout.scale,layoutOf]; omega⟩) := by
  apply Fin.ext
  change (if 2*V.proofQubits+j.val<V.proofQubits then _ else
    if 2*V.proofQubits+j.val<2*V.proofQubits then _ else
    if 2*V.proofQubits+j.val<3*V.proofQubits+1 then
      BlockCircuit.bodyWires V+11+(2*V.proofQubits+j.val-2*V.proofQubits) else _) = _
  have hj := j.isLt
  rw [if_neg (by omega),if_neg (by omega),if_pos (by omega)]
  change BlockCircuit.bodyWires V+11+(2*V.proofQubits+j.val-2*V.proofQubits) = BlockCircuit.bodyWires V+(11+j.val)
  omega

lemma equality_temp : tempWire (historyEquality V) = oldTags V 10 := by
  apply Fin.ext
  change (if 3*V.proofQubits+1<V.proofQubits then _ else
    if 3*V.proofQubits+1<2*V.proofQubits then _ else
    if 3*V.proofQubits+1<3*V.proofQubits+1 then _ else _) = _
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  rfl

lemma clock_control (j : Fin (BlockCircuit.clockWires V)) :
    (historyLayout V).clock.controls j = oldEmbedding V ((layoutOf V).clockWire j) := rfl

lemma clock_flag (j : Fin (BlockCircuit.clockWires V+1)) :
    (historyLayout V).clock.flags j = oldEmbedding V ((layoutOf V).scratchWire
      ⟨j.val,by have := j.isLt; dsimp only [Layout.scale,layoutOf,Layout.clock,BlockCircuit.clockWires] at *; omega⟩) := rfl

lemma clean_of_old (x : Physical V) (hx : (layoutOf V).ScratchClean (oldState V x))
    (h10 : x (oldTags V 10)=false) : (historyLayout V).Clean x := by
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro j
    change x (carryWire (historyEquality V) j) = false
    rw [equality_carry]
    exact hx _
  · change x (tempWire (historyEquality V)) = false
    rw [equality_temp]
    exact h10
  · intro j
    rw [clock_flag]
    exact hx _

lemma proofMatches_iff (x : Physical V) :
    (historyLayout V).proofMatches x ↔
      V.proofPart (BlockCircuit.decode (oldState V x)).2.2.1 = (claim V x).1 := by
  have hl : (x ∘ leftWire (historyLayout V).equality) =
      V.proofPart (BlockCircuit.decode (oldState V x)).2.2.1 := by
    funext j
    change x (leftWire (historyEquality V) j) = _
    rw [proof_left]
    rfl
  have hr : (x ∘ rightWire (historyLayout V).equality) = (claim V x).1 := by
    funext j
    change x (rightWire (historyEquality V) j) = _
    rw [proof_right]
    rfl
  unfold VariableHistoryEquality.Layout.proofMatches
  rw [hl,hr]

lemma clockMatches_iff (x : Physical V) : (historyLayout V).clockMatches x ↔
    (BlockCircuit.decode (oldState V x)).2.1.val = ell V.proofQubits := by
  change (∀ j, x ((historyLayout V).clock.controls j) = true) ↔ _
  simp only [clock_control]
  exact BlockHistoryCoordinates.clock_all_true_iff V (oldState V x)

lemma predicate_eq (x : Physical V) :
    CertificateHistoryPrograms.Layout.predicate (historyLayout V) x =
      (decide ((BlockCircuit.decode (oldState V x)).2.1.val = ell V.proofQubits) &&
        decide (V.proofPart (BlockCircuit.decode (oldState V x)).2.2.1 = (claim V x).1)) := by
  simp only [CertificateHistoryPrograms.Layout.predicate,proofMatches_iff,clockMatches_iff,Bool.and_comm]

end QMAPerfectCompleteness.Main.CertificateHistoryCoordinates

end

/- Inline helpers retained from Solutions.CertificateClosingActions. -/
section


/-! Exact variable-certificate closing and identity stages on the prepared workspace fiber. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Matrix
namespace QMAPerfectCompleteness.Main.CertificateBlockCorrectness
open CertificateMasterLayout BlockCompiler BlockCoordinates BlockImplements
variable (V : Verifier gatesG2)

lemma embed_claim (s : Key V → Basis (work V)) (p : Logical V) :
    CertificateHistoryCoordinates.claim V (embed V s p) = p.2 :=
  congrArg (fun q : Logical V × Basis (work V) => q.1.2) (coords_embed V s p)

lemma tagged_historyClean (s : Key V → Basis (work V)) (hs : Prepared V s) (p : Logical V) :
    CertificateHistoryPrograms.Layout.Clean (historyLayout V) (embed V (taggedSpace V s) p) :=
  ⟨CertificateHistoryCoordinates.clean_of_old V _ (tagged_scratch V s hs p)
      (tagged_aux V s hs p 10 (by decide)),
    tagged_aux V s hs p 8 (by decide),tagged_aux V s hs p 6 (by decide)⟩



lemma closing_action (s : Key V → Basis (work V)) (hs : Prepared V s) (p : Logical V) :
    (CertificateClosingCircuit.layout V).action (embed V (taggedSpace V s) p) =
      embed V (taggedSpace V s) (closingLogical V p) := by
  have h7 : embed V (taggedSpace V s) p ((historyLayout V).tags 2)=false :=
    tagged_aux V s hs p 7 (by decide)
  rw [(CertificateClosingCircuit.layout V).action_eq _ h7]
  have hp := CertificateHistoryCoordinates.predicate_eq V (embed V (taggedSpace V s) p)
  have hd : BlockCircuit.decode (CertificateOldPrograms.oldState V (embed V (taggedSpace V s) p)) = p.1 :=
    embed_decode V (taggedSpace V s) p
  simp only [hd,embed_claim] at hp
  change Function.update (embed V (taggedSpace V s) p) (oldEmbedding V (layoutOf V).flagWire)
    (xor (embed V (taggedSpace V s) p (oldEmbedding V (layoutOf V).flagWire))
      (embed V (taggedSpace V s) p (oldTags V 4) &&
        CertificateHistoryPrograms.Layout.predicate (historyLayout V) (embed V (taggedSpace V s) p))) = _
  rw [hp]
  rw [embed_old_flag,tagged_core V s p 4 (by decide),embed_update_flag]
  rfl

lemma closing_transports (s : Key V → Basis (work V)) (hs : Prepared V s) :
    Transports (embed V (taggedSpace V s)) (embed V (taggedSpace V s))
      (circuitMatrix (CertificateClosingCircuit.gates V)) (basisMap (closingLogical V)) := by
  apply transports_classical
  intro y p
  have h7 : embed V (taggedSpace V s) p ((historyLayout V).tags 2)=false :=
    tagged_aux V s hs p 7 (by decide)
  have ha := closing_action V s hs p
  rw [(CertificateClosingCircuit.layout V).action_eq _ h7] at ha
  have hm := (CertificateClosingCircuit.layout V).gates_matrix y _ (tagged_historyClean V s hs p) h7
  have hh := congrArg (fun z : Physical V => if y=z then (1 : ℂ) else 0) ha
  exact hm.trans hh



lemma identity_transports (s : Key V → Basis (work V)) (hs : Prepared V s) :
    Transports (embed V (taggedSpace V s)) (embed V (taggedSpace V s))
      (circuitMatrix (CertificateOldPrograms.identityFlagProgram V).gates) (basisMap (identityLogical V)) := by
  apply transports_classical
  intro y p
  rw [(CertificateOldPrograms.identityFlagProgram V).sound y _ (tagged_scratch V s hs p),identityFlag_action]
  rfl

lemma phase_transports (s : Key V → Basis (work V)) :
    Transports (embed V (taggedSpace V s)) (embed V (taggedSpace V s))
      (circuitMatrix (CertificateOldPrograms.phaseGates V))
      (signedMap id (CertificateLogicalSelect.sign V)) := by
  apply transports_signed
  intro y p
  rw [CertificateOldPrograms.phase_matrix,Matrix.diagonal_apply]
  by_cases hy : y=embed V (taggedSpace V s) p
  · subst y
    rw [if_pos rfl,tagged_core V s p 5 (by decide)]
    simp only [Function.id_def,if_pos rfl]
    rfl
  · simp only [hy,if_false,Function.id_def]

end QMAPerfectCompleteness.Main.CertificateBlockCorrectness

end



/-! Actual coherent post-call SELECT: flag tests, clock shift, and active minus phase. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Matrix
namespace QMAPerfectCompleteness.Main.CertificateBlockCorrectness
end QMAPerfectCompleteness.Main.CertificateBlockCorrectness
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.CertificateBlockCorrectness
open CertificateMasterLayout BlockCompiler BlockImplements
variable (V : Verifier gatesG2)







lemma QMAPerfectCompleteness.Main.CertificateBlockCorrectness.signedMap_mul_basisMap {α : Type*} [Fintype α]
    (f g : α → α) (s : α → ℂ) :
    signedMap f s * basisMap g = signedMap (f ∘ g) (s ∘ g) := by
  classical
  ext y x
  simp [signedMap,basisMap,basisEmbedding,Matrix.mul_apply,Function.comp_apply,mul_ite]

lemma QMAPerfectCompleteness.Main.CertificateBlockCorrectness.post_logical_assembly :
    signedMap id (CertificateLogicalSelect.sign V) * basisMap (incrementLogical V) *
      basisMap (closingLogical V) * basisMap (identityLogical V) =
      signedMap (CertificateLogicalSelect.post V) (CertificateLogicalSelect.sign V) := by
  rw [signedMap_mul_basisMap,signedMap_mul_basisMap,signedMap_mul_basisMap]
  congr 1 <;> funext p <;> rfl



theorem solution (s : Key V → Basis (work V)) (hs : Prepared V s) :
    Transports (embed V (taggedSpace V s)) (embed V (taggedSpace V s))
      (circuitMatrix (postGates V))
      (signedMap (CertificateLogicalSelect.post V) (CertificateLogicalSelect.sign V)) := by
  let e := embed V (taggedSpace V s)
  have h1 := transports_mul e e e _ _ _ _ (closing_transports V s hs) (identity_transports V s hs)
  have h2 := transports_mul e e e _ _ _ _ (increment_transports V s hs) h1
  have h3 := transports_mul e e e _ _ _ _ (phase_transports V s) h2
  have h : Transports e e (circuitMatrix (postGates V))
      (signedMap id (CertificateLogicalSelect.sign V) * basisMap (incrementLogical V) *
        basisMap (closingLogical V) * basisMap (identityLogical V)) := by
    simpa only [postGates,BlockProof.circuitMatrix_append,Matrix.mul_assoc] using h3
  rw [post_logical_assembly] at h
  exact h
