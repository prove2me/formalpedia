-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.CertificateBlockCorrectness.increment_transports
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T16:45:48.144455+00:00
-- url     : https://prove2.me/submissions/b810fae7-d968-4f4c-9356-ce43f613c06b

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

/- Inline helpers retained from Solutions.ClockCircuits. -/
section


/-! Controlled cyclic increment of a little-endian binary clock, using reusable clean flags. -/

open Matrix
namespace QMAPerfectCompleteness.Main.ClockCircuits
open ReversibleGadgets ControlCircuits ComparisonCircuits

variable {r n : ℕ} (L : AndLayout (r+1) n)



/-- Updating a control beyond a prefix does not change that prefix's conjunction. -/
theorem prefixAnd_update_late {k : ℕ} (A : AndLayout k n) (x : Basis n)
    (u : ℕ) (hu : u ≤ k) (j : Fin k) (huj : u ≤ (j : ℕ)) (b : Bool) :
    prefixAnd A (Function.update x (A.controls j) b) u hu = prefixAnd A x u hu := by
  induction u with
  | zero => rfl
  | succ u ih =>
    rw [prefixAnd, prefixAnd, ih (by omega) (by omega)]
    have hne : A.controls (⟨u, by omega⟩ : Fin k) ≠ A.controls j := by
      apply A.controls.injective.ne
      intro h
      have := congrArg Fin.val h
      change u = j.val at this
      omega
    rw [Function.update_of_ne hne]

















/-- Exact carry formula for every control, with the enable wire (index zero) left untouched. -/
theorem incrementPrefix_control (t : ℕ) (ht : t ≤ r) (x : Basis n) (i : Fin (r+1)) :
    incrementPrefixAction L t ht x (L.controls i) =
      if 0 < (i : ℕ) ∧ (i : ℕ) ≤ t then
        xor (x (L.controls i)) (prefixAnd L x i (Nat.le_of_lt i.isLt))
      else x (L.controls i) := by
  induction t generalizing x i with
  | zero =>
    change x (L.controls i) = if 0 < i.val ∧ i.val ≤ 0 then _ else x (L.controls i)
    rw [if_neg (by omega)]
  | succ t ih =>
    let j : Fin (r+1) := ⟨t+1, by omega⟩
    rw [incrementPrefixAction, ih (by omega)]
    by_cases hij : i = j
    · subst i
      simp [j, prefixAnd_update_late]
    · have hne : L.controls i ≠ L.controls j := L.controls.injective.ne hij
      rw [Function.update_of_ne hne]
      by_cases hit : 0 < (i : ℕ) ∧ (i : ℕ) ≤ t
      · rw [if_pos hit, prefixAnd_update_late L x i (Nat.le_of_lt i.isLt) j (by dsimp [j]; omega),
          if_pos (by omega : 0 < (i : ℕ) ∧ (i : ℕ) ≤ t+1)]
      · have hfalse : ¬ (0 < (i : ℕ) ∧ (i : ℕ) ≤ t+1) := by
          have hidx : (i : ℕ) ≠ t+1 := by intro h; apply hij; exact Fin.ext h
          omega
        rw [if_neg hit, if_neg hfalse]











/-- Each clock bit is XORed with enable AND the conjunction of all lower original bits. -/
theorem controlledIncrementAction_bit (x : Basis n) (j : Fin r) :
    controlledIncrementAction L x (L.controls j.succ) =
      xor (x (L.controls j.succ)) (prefixAnd L x (j+1) (by have := j.isLt; omega)) := by
  rw [controlledIncrementAction, incrementPrefix_control]
  simp [j.isLt]

@[simp] theorem controlledIncrementAction_enable (x : Basis n) :
    controlledIncrementAction L x (L.controls 0) = x (L.controls 0) := by
  rw [controlledIncrementAction, incrementPrefix_control]
  simp









theorem clockWord_bit (x : Basis n) (j : Fin r) :
    (clockWord L x).getLsbD j = x (L.controls j.succ) := by
  simp only [clockWord, BitVec.getLsbD_ofNatLT]
  exact littleValue_decode _ j

/-- The clean conjunction ladder computes exactly the standard binary adder's carry. -/
theorem prefixAnd_eq_carry (x : Basis n) (j : ℕ) (hj : j ≤ r) :
    prefixAnd L x (j+1) (by omega) =
      BitVec.carry j (clockWord L x) (0 : BitVec r) (x (L.controls 0)) := by
  induction j with
  | zero => simp [prefixAnd]
  | succ j ih =>
    rw [prefixAnd, ih (by omega), BitVec.carry_succ]
    have hbit : (clockWord L x).getLsbD j = x (L.controls (⟨j+1, by omega⟩ : Fin (r+1))) :=
      clockWord_bit L x ⟨j, by omega⟩
    have hzero : (0 : BitVec r).getLsbD j = false := BitVec.getLsbD_zero
    rw [hzero, Bool.atLeastTwo_false_mid, hbit]
    exact Bool.and_comm _ _

theorem controlledIncrementAction_bit_add (x : Basis n) (j : Fin r) :
    controlledIncrementAction L x (L.controls j.succ) =
      (clockWord L x + (0 : BitVec r) + (BitVec.ofBool (x (L.controls 0))).setWidth r).getLsbD j := by
  rw [controlledIncrementAction_bit, prefixAnd_eq_carry L x j (Nat.le_of_lt j.isLt)]
  have h := BitVec.getLsbD_add_add_bool j.isLt (clockWord L x) (0 : BitVec r) (x (L.controls 0))
  have hzero : (0 : BitVec r).getLsbD j = false := BitVec.getLsbD_zero
  rw [hzero, Bool.false_xor, clockWord_bit] at h
  exact h.symm

theorem littleValue_getLsbD {k : ℕ} (v : BitVec k) :
    littleValue (fun j : Fin k => v.getLsbD j) = v.toNat := by
  change littleValue (fun j : Fin k => v.toNat.testBit j) = v.toNat
  rw [littleValue_testBit, Nat.mod_eq_of_lt v.isLt]

/-- Exact cyclic increment in the same little-endian numeric convention as the block compiler. -/
theorem controlledIncrementAction_bitsValue (x : Basis n) :
    BlockCircuit.bitsValue (controlledIncrementAction L x) (fun j : Fin r => L.controls j.succ) =
      (BlockCircuit.bitsValue x (fun j : Fin r => L.controls j.succ) +
        (x (L.controls 0)).toNat) % 2 ^ r := by
  change littleValue (fun j : Fin r => controlledIncrementAction L x (L.controls j.succ)) = _
  simp_rw [controlledIncrementAction_bit_add]
  rw [littleValue_getLsbD]
  simp [clockWord, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofBool,
    Nat.add_mod_mod, Nat.mod_add_mod]
  rfl







end QMAPerfectCompleteness.Main.ClockCircuits

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

/- Inline helpers retained from Solutions.BlockClockCoordinates. -/
section


/-! Physical controlled increment in the published logical clock coordinates. -/
set_option backward.isDefEq.respectTransparency false
open Matrix
namespace QMAPerfectCompleteness.Main.BlockClockCoordinates
open BlockCompiler ClockCircuits BlockCoordinates



/-- Only clock targets change; even the persistent enable tag is preserved. -/
theorem increment_outside_clock (D : Layout) (x : Basis D.total) (w : Fin D.total)
    (hw : ∀ j, w ≠ D.clockWire j) : increment D x w = x w := by
  by_cases he : w = D.tagWire 5
  · subst w
    exact controlledIncrementAction_enable D.incrementLayout x
  · apply controlledIncrementAction_outside D.incrementLayout x w
    intro i
    refine Fin.cases he (fun j => hw j) i

@[simp] theorem increment_index (D : Layout) (x : Basis D.total) (i : Fin D.index) :
    increment D x (D.indexWire i) = x (D.indexWire i) := by
  apply increment_outside_clock
  intro j h
  have hv := congrArg Fin.val h
  change i.val = D.index+j.val at hv
  have := i.isLt
  omega

@[simp] theorem increment_verifier (D : Layout) (x : Basis D.total)
    (i : Fin (D.proof+D.ancilla)) :
    increment D x (D.verifierWire i) = x (D.verifierWire i) := by
  apply increment_outside_clock
  intro j h
  have hv := congrArg Fin.val h
  change D.index+D.clock+i.val = D.index+j.val at hv
  have := j.isLt
  omega

@[simp] theorem increment_flag (D : Layout) (x : Basis D.total) :
    increment D x D.flagWire = x D.flagWire := by
  apply increment_outside_clock
  intro j h
  have hv := congrArg Fin.val h
  change D.index+D.clock+(D.proof+D.ancilla) = D.index+j.val at hv
  have := j.isLt
  omega









/-- Numeric form of the physical clock update, for both enabled and disabled branches. -/
theorem increment_clockValue (D : Layout) (x : Basis D.total) :
    D.clockValue (increment D x) = (D.clockValue x+(x (D.tagWire 5)).toNat) % 2^D.clock :=
  controlledIncrementAction_bitsValue D.incrementLayout x




/-- Decoding the physical step gives modular addition on the clock and no other body change. -/
theorem decode_increment (V : Verifier gatesG2)
    (x : Basis (BlockCircuit.bodyWires V+(layoutOf V).work)) :
    BlockCircuit.decode (increment (layoutOf V) x) =
      ((BlockCircuit.decode x).1,
        (BlockCircuit.decode x).2.1 +
          (Fin.ofNat (ell V.proofQubits+1) (x ((layoutOf V).tagWire 5)).toNat),
        (BlockCircuit.decode x).2.2) := by
  apply Prod.ext
  · change Fin.ofNat _ ((layoutOf V).indexValue (increment (layoutOf V) x)) =
      Fin.ofNat _ ((layoutOf V).indexValue x)
    congr 1
    unfold Layout.indexValue BlockCircuit.bitsValue
    simp_rw [increment_index]
  · apply Prod.ext
    · apply Fin.ext
      change (layoutOf V).clockValue (increment (layoutOf V) x) % (ell V.proofQubits+1) =
        ((layoutOf V).clockValue x % (ell V.proofQubits+1) +
          (x ((layoutOf V).tagWire 5)).toNat % (ell V.proofQubits+1)) % (ell V.proofQubits+1)
      rw [increment_clockValue,clock_card]
      simp [Nat.mod_add_mod]
    · apply Prod.ext
      · funext i
        exact increment_verifier (layoutOf V) x i
      · exact increment_flag (layoutOf V) x





end QMAPerfectCompleteness.Main.BlockClockCoordinates

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















lemma increment_selected (x : Physical V) :
    ((incrementProgram V).action x) ∘ oldEmbedding V =
      BlockClockCoordinates.increment (layoutOf V) (oldState V x) :=
  CleanProgram.placePermutation_selected _ _ _

lemma place_outside {r n : ℕ} (e : Fin r ↪ Fin n) (f : Basis r → Basis r)
    (x : Basis n) (w : Fin n) (hw : ∀ j, e j ≠ w) :
    placePermutation e f x w = x w := by
  have h := congrArg Prod.snd ((CircuitProof.splitTargets e).apply_symm_apply
    (f (x ∘ e),(CircuitProof.splitTargets e x).2))
  have hw' : w ∉ Set.range e := by simpa only [Set.mem_range,not_exists] using hw
  exact congrFun h ⟨w,hw'⟩





end QMAPerfectCompleteness.Main.CertificateOldPrograms

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











end QMAPerfectCompleteness.Main.CertificateBlockCorrectness

end

/- Inline helpers retained from Solutions.CertificateClockCoordinates. -/
section


/-! The lifted SELECT clock step on the complete coherent-certificate register. -/
set_option backward.isDefEq.respectTransparency false
open Matrix
namespace QMAPerfectCompleteness.Main.CertificateBlockCorrectness
open CertificateMasterLayout CertificateCoordinates BlockCoordinates BlockCompiler ReversibleGadgets
variable (V : Verifier gatesG2)

lemma increment_old (x : Physical V) :
    old V ((CertificateOldPrograms.incrementProgram V).action x) =
      BlockClockCoordinates.increment (layoutOf V) (old V x) :=
  CertificateOldPrograms.increment_selected V x

/-- The lifted program changes only its old-layout clock targets, wherever spectators are stored. -/
lemma increment_outside_clock (x : Physical V) (w : Fin (total V))
    (hw : ∀ j, w ≠ oldEmbedding V ((layoutOf V).clockWire j)) :
    (CertificateOldPrograms.incrementProgram V).action x w = x w := by
  classical
  by_cases he : w ∈ Set.range (oldEmbedding V)
  · obtain ⟨i,rfl⟩ := he
    have hs := congrFun (CertificateOldPrograms.increment_selected V x) i
    rw [Function.comp_apply] at hs
    rw [hs]
    apply BlockClockCoordinates.increment_outside_clock
    intro j hij
    exact hw j (congrArg (oldEmbedding V) hij)
  · apply CertificateOldPrograms.place_outside
    intro i hi
    exact he ⟨i,hi⟩

lemma increment_work (x : Physical V) (i : Fin (work V)) :
    (CertificateOldPrograms.incrementProgram V).action x (workWire V i) = x (workWire V i) := by
  apply increment_outside_clock
  intro j h
  have hv := congrArg Fin.val h
  change BlockCircuit.bodyWires V+i.val = indexQubits V+j.val at hv
  have hj : j.val < BlockCircuit.clockWires V := j.isLt
  dsimp only [BlockCircuit.bodyWires] at hv
  omega

lemma increment_claim (x : Physical V) (i : Fin (claimQubits V)) :
    (CertificateOldPrograms.incrementProgram V).action x
      (Fin.natAdd (BlockCircuit.bodyWires V+work V) i) =
      x (Fin.natAdd (BlockCircuit.bodyWires V+work V) i) := by
  apply increment_outside_clock
  intro j h
  have hv := congrArg Fin.val h
  change BlockCircuit.bodyWires V+work V+i.val = indexQubits V+j.val at hv
  have hj : j.val < BlockCircuit.clockWires V := j.isLt
  dsimp only [BlockCircuit.bodyWires] at hv
  omega

lemma coords_increment (x : Physical V) :
    coords V ((CertificateOldPrograms.incrementProgram V).action x) =
      ((((coords V x).1.1.1,(coords V x).1.1.2.1+
        Fin.ofNat (ell V.proofQubits+1) (x (oldTags V 5)).toNat,
        (coords V x).1.1.2.2),(coords V x).1.2),(coords V x).2) := by
  apply Prod.ext
  · apply Prod.ext
    · rw [← old_decode,increment_old,BlockClockCoordinates.decode_increment,old_decode]
      rfl
    · rw [computationEquiv_claim,computationEquiv_claim]
      congr 1
      funext i
      exact increment_claim V x i
  · rw [coords_work,coords_work]
    funext i
    exact increment_work V x i

/-- The full master increment preserves the indexed certificate workspace fiber and advances
only the decoded clock by the old persistent D tag. -/
lemma increment_action_embed (s : Key V → Basis (work V)) (p : Logical V) :
    (CertificateOldPrograms.incrementProgram V).action (embed V s p) =
      embed V s
        ((p.1.1,p.1.2.1+Fin.ofNat (ell V.proofQubits+1)
          (embed V s p (oldTags V 5)).toNat,p.1.2.2),p.2) := by
  apply (coords V).injective
  rw [coords_increment,coords_embed,coords_embed]
  rfl

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



lemma QMAPerfectCompleteness.Main.CertificateBlockCorrectness.increment_action (s : Key V → Basis (work V)) (p : Logical V) :
    (CertificateOldPrograms.incrementProgram V).action (embed V (taggedSpace V s) p) =
      embed V (taggedSpace V s) (incrementLogical V p) := by
  rw [increment_action_embed,tagged_core V s p 5 (by decide)]
  rfl

theorem solution (s : Key V → Basis (work V)) (hs : Prepared V s) :
    Transports (embed V (taggedSpace V s)) (embed V (taggedSpace V s))
      (circuitMatrix (CertificateOldPrograms.incrementProgram V).gates) (basisMap (incrementLogical V)) := by
  apply transports_classical
  intro y p
  rw [(CertificateOldPrograms.incrementProgram V).sound y _ (tagged_scratch V s hs p),increment_action]
