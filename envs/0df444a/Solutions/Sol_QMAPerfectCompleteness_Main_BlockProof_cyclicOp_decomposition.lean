-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.BlockProof.cyclicOp_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:50:58.326731+00:00
-- url     : https://prove2.me/submissions/2ecf68ac-65dd-482a-affb-780eea1953f3

/- Generated from Solutions.BlockEncoding by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates

/- Inline helpers retained from Solutions.Cyclic. -/
section


open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.CyclicProof

variable {G : GateSet}









theorem single_kronecker_mulVec {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (a b t : α) (p : β) (A : Matrix β β ℂ)
    (v : α × β → ℂ) :
    (((Matrix.single a b (1 : ℂ)) ⊗ₖ A) *ᵥ v) (t,p) =
      if t = a then (A *ᵥ fun q => v (b,q)) p else 0 := by
  classical
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kronecker_apply,
    Matrix.single_apply]
  by_cases h : t = a
  · subst t
    simp
  · simp [h, Ne.symm h]

theorem cyclic_mulVec_zero (V : Verifier G) (z : V.Proof) (Γ : ℝ)
    (v : History V → ℂ) (p : V.Proof) :
    (V.cyclicOp z Γ *ᵥ v) (0,p) =
      if p = z then (Γ⁻¹ : ℂ) * v (Fin.last (ell V.proofQubits),z) else 0 := by
  classical
  simp only [Verifier.cyclicOp, Matrix.add_mulVec, Matrix.sum_mulVec, Pi.add_apply,
    Finset.sum_apply, single_kronecker_mulVec]
  simp [Matrix.single_mulVec_eq, Fin.succ_ne_zero, Pi.single_apply, eq_comm]

theorem cyclic_mulVec_succ (V : Verifier G) (z : V.Proof) (Γ : ℝ)
    (v : History V → ℂ) (t : Fin (ell V.proofQubits)) (p : V.Proof) :
    (V.cyclicOp z Γ *ᵥ v) (t.succ,p) =
      (V.doubled *ᵥ fun q => v (t.castSucc,q)) p := by
  classical
  simp only [Verifier.cyclicOp, Matrix.add_mulVec, Matrix.sum_mulVec, Pi.add_apply,
    Finset.sum_apply, single_kronecker_mulVec]
  simp [Fin.succ_ne_zero]





theorem cyclicOp_apply_zero (V : Verifier G) (z : V.Proof) (Γ : ℝ)
    (s : Clock V.proofQubits) (p q : V.Proof) :
    V.cyclicOp z Γ (0,p) (s,q) =
      if p = z ∧ s = Fin.last (ell V.proofQubits) ∧ q = z then ((Γ⁻¹ : ℝ) : ℂ) else 0 := by
  classical
  have h := cyclic_mulVec_zero V z Γ (Pi.single (s,q) 1) p
  simp only [Matrix.mulVec_single_one] at h
  by_cases hp : p = z <;> by_cases hs : s = Fin.last (ell V.proofQubits) <;>
    by_cases hq : q = z <;>
    simp_all [Pi.single_apply, Prod.mk.injEq]

theorem cyclicOp_apply_succ (V : Verifier G) (z : V.Proof) (Γ : ℝ)
    (t : Fin (ell V.proofQubits)) (s : Clock V.proofQubits) (p q : V.Proof) :
    V.cyclicOp z Γ (t.succ,p) (s,q) =
      if s = t.castSucc then V.doubled p q else 0 := by
  classical
  have h := cyclic_mulVec_succ V z Γ (Pi.single (s,q) 1) t p
  simp only [Matrix.mulVec_single_one] at h
  by_cases hs : s = t.castSucc
  · subst s
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Prod.mk.injEq, eq_comm] using h
  · simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Prod.mk.injEq, hs, Ne.symm hs] using h

open VerifierAnalysis











open scoped ComplexOrder





open scoped Matrix.Norms.L2Operator







end QMAPerfectCompleteness.Main.CyclicProof

end



/-! Algebraic ingredients of Lemma 3.6. All results in this file are proved from definitions;
no import of the open `exact_block_encoding` statement is used. -/

open Matrix
open scoped Kronecker

namespace QMAPerfectCompleteness.Main.BlockProof
end QMAPerfectCompleteness.Main.BlockProof
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.BlockProof

variable {G : GateSet} (V : Verifier G)

@[simp] theorem QMAPerfectCompleteness.Main.BlockProof.proofPart_initialState (p : V.Proof) : V.proofPart (V.initialState p) = p := by
  funext i
  simp [Verifier.proofPart, Verifier.initialState]

theorem QMAPerfectCompleteness.Main.BlockProof.initialState_injective : Function.Injective V.initialState := by
  intro p q hpq
  have := congrArg V.proofPart hpq
  simpa using this





/-- A flag controlled on P has block P between input flag one and output flag zero. -/
theorem QMAPerfectCompleteness.Main.BlockProof.flipIf_false_true (P : Clock V.proofQubits → V.Wire → Bool)
    (t' t : Clock V.proofQubits) (w' w : V.Wire) :
    V.flipIf P (t', w', false) (t, w, true) =
      if t' = t ∧ w' = w ∧ P t w = true then 1 else 0 := by
  simp only [Verifier.flipIf, Matrix.of_apply]
  cases h : P t w <;> simp [h]













/-- Right multiplication by an operation on verifier wires preserves clock and flag. -/
theorem QMAPerfectCompleteness.Main.BlockProof.mul_onWires_apply (M : Matrix V.Body V.Body ℂ)
    (N : Matrix V.Wire V.Wire ℂ) (y : V.Body) (t : Clock V.proofQubits)
    (w : V.Wire) (f : Bool) :
    (M * V.onWires N) y (t, w, f) =
      ∑ q : V.Wire, M y (t, q, f) * N q w := by
  classical
  simp [Matrix.mul_apply, Verifier.onWires, Matrix.kronecker_apply,
    Fintype.sum_prod_type, Matrix.one_apply, mul_ite, ite_mul]

/-- Left multiplication by an operation on verifier wires preserves clock and flag. -/
theorem QMAPerfectCompleteness.Main.BlockProof.onWires_mul_apply (M : Matrix V.Wire V.Wire ℂ)
    (N : Matrix V.Body V.Body ℂ) (t : Clock V.proofQubits)
    (w : V.Wire) (f : Bool) (x : V.Body) :
    (V.onWires M * N) (t, w, f) x =
      ∑ q : V.Wire, M w q * N (t, q, f) x := by
  classical
  simp [Matrix.mul_apply, Verifier.onWires, Matrix.kronecker_apply,
    Fintype.sum_prod_type, Matrix.one_apply, mul_ite, ite_mul]







/-- The flag block between two arbitrary operations on verifier wires is their projector
sandwich; this is the algebraic observation used in the forward-transition gadget. -/
theorem QMAPerfectCompleteness.Main.BlockProof.controlled_flag_block (M N : Matrix V.Wire V.Wire ℂ)
    (P : Clock V.proofQubits → V.Wire → Bool)
    (t' t : Clock V.proofQubits) (w' w : V.Wire) :
    (V.onWires M * V.flipIf P * V.onWires N) (t', w', false) (t, w, true) =
      if t' = t then ∑ q : V.Wire, M w' q * (if P t q then N q w else 0) else 0 := by
  classical
  rw [mul_onWires_apply]
  simp_rw [onWires_mul_apply, flipIf_false_true]
  by_cases ht : t' = t
  · subst t'
    simp [ite_and, mul_ite, ite_mul]
  · simp [ht]

/-- The shift acts only on the clock coordinate. -/
theorem QMAPerfectCompleteness.Main.BlockProof.shift_mul_apply (M : Matrix V.Body V.Body ℂ) (y x : V.Body) :
    (V.shift * M) y x = ∑ t : Clock V.proofQubits,
      if y.1 = t + 1 then M (t, y.2.1, y.2.2) x else 0 := by
  classical
  simp [Verifier.shift, Matrix.mul_apply, Matrix.kronecker_apply,
    Fintype.sum_prod_type, Matrix.one_apply, ite_mul, mul_ite]

/-- Acceptance-operator entries after inserting the zero ancillas. -/
theorem QMAPerfectCompleteness.Main.BlockProof.acceptanceOperator_apply (p q : V.Proof) :
    V.acceptanceOperator p q =
      ∑ w : V.Wire, V.unitaryᴴ (V.initialState p) w *
        (if w V.output then V.unitary w (V.initialState q) else 0) := by
  classical
  simp [Verifier.acceptanceOperator, Verifier.ancillaZero, Verifier.acceptProjector,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply, ite_mul, mul_ite]

/-- The forward gadget's designated flag block before inserting proof-register ancillas. -/
theorem QMAPerfectCompleteness.Main.BlockProof.gadgetT_false_true (t' t : Clock V.proofQubits) (w' w : V.Wire) :
    V.gadgetT (t', w', false) (t, w, true) =
      if t' = t + 1 ∧ (t : ℕ) < ell V.proofQubits then
        ∑ q : V.Wire, V.unitaryᴴ w' q * (if q V.output then V.unitary q w else 0)
      else 0 := by
  classical
  have hform : V.gadgetT = V.shift *
      (V.onWires V.unitaryᴴ *
        V.flipIf (fun t w => decide ((t : ℕ) < ell V.proofQubits) && w V.output) *
          V.onWires V.unitary) := by
    simp only [Verifier.gadgetT, Matrix.mul_assoc]
  rw [hform, shift_mul_apply]
  simp_rw [controlled_flag_block]
  rw [Finset.sum_eq_single t]
  · simp [ite_and, mul_ite]
  · intro u _ hut
    simp [hut]
  · simp





/-- The closing gadget's flag block. -/
theorem QMAPerfectCompleteness.Main.BlockProof.gadgetR_false_true (z : V.Proof) (t' t : Clock V.proofQubits) (w' w : V.Wire) :
    V.gadgetR z (t', w', false) (t, w, true) =
      if t' = t + 1 ∧ w' = w ∧ (t : ℕ) = ell V.proofQubits ∧ V.proofPart w = z
      then 1 else 0 := by
  classical
  rw [Verifier.gadgetR, shift_mul_apply]
  simp_rw [flipIf_false_true]
  rw [Finset.sum_eq_single t]
  · simp [ite_and]
  · intro u _ hut
    simp [hut]
  · simp







/-- The forward block is the acceptance operator on each nonclosing clock transition. -/
theorem QMAPerfectCompleteness.Main.BlockProof.forwardBlock_apply (t' t : Clock V.proofQubits) (p q : V.Proof) :
    forwardBlock V (t', p) (t, q) =
      if t' = t + 1 ∧ (t : ℕ) < ell V.proofQubits then V.acceptanceOperator p q else 0 := by
  simp only [forwardBlock, bodyInitial, gadgetT_false_true, ← acceptanceOperator_apply]

/-- The closing block tests the basis proof z and the final clock, then advances the clock. -/
theorem QMAPerfectCompleteness.Main.BlockProof.closingBlock_apply (z : V.Proof) (t' t : Clock V.proofQubits) (p q : V.Proof) :
    closingBlock V z (t', p) (t, q) =
      if t' = t + 1 ∧ p = q ∧ (t : ℕ) = ell V.proofQubits ∧ q = z then 1 else 0 := by
  simp only [closingBlock, bodyInitial, gadgetR_false_true, proofPart_initialState,
    (initialState_injective V).eq_iff]

/-- The two gadget blocks are exactly the forward and closing summands of Eq. (3). -/
theorem solution (z : V.Proof) (Γ : ℝ) :
    V.cyclicOp z Γ = (2 : ℂ) • forwardBlock V + ((Γ⁻¹ : ℝ) : ℂ) • closingBlock V z := by
  classical
  ext ⟨r,p⟩ ⟨s,q⟩
  refine Fin.cases ?_ (fun t => ?_) r
  · rw [CyclicProof.cyclicOp_apply_zero]
    refine Fin.lastCases ?_ (fun u => ?_) s
    · by_cases hp : p = z <;> by_cases hq : q = z <;>
        simp_all [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
          forwardBlock_apply, closingBlock_apply]
    · simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        forwardBlock_apply, closingBlock_apply, Fin.coeSucc_eq_succ, u.isLt,
        Fin.castSucc_ne_last, Fin.succ_ne_zero, Ne.symm (Fin.succ_ne_zero u)]
  · rw [CyclicProof.cyclicOp_apply_succ]
    refine Fin.lastCases ?_ (fun u => ?_) s
    · simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        forwardBlock_apply, closingBlock_apply, Fin.succ_ne_zero,
        Ne.symm (Fin.castSucc_ne_last t)]
    · by_cases h : t = u
      · subst u
        simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, forwardBlock_apply,
          closingBlock_apply, Fin.coeSucc_eq_succ, t.isLt, Nat.ne_of_lt t.isLt, Verifier.doubled]
      · simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, forwardBlock_apply,
          closingBlock_apply, Fin.coeSucc_eq_succ, u.isLt, h, Ne.symm h]
