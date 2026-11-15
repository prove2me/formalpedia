-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.Repetition.CircuitProof.acceptanceOperator_pi
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T16:59:45.185141+00:00
-- url     : https://prove2.me/submissions/a420bdae-b59a-435e-9c50-0bcdab86ad2a

/- Generated from Solutions.RepetitionCircuit by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_Repetition
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof

/- Inline helpers retained from Solutions.ReversibleGadgets. -/
section


/-! Explicit G₂ circuit gadgets used by the block-encoding compiler. -/

open Matrix
open scoped Kronecker

namespace QMAPerfectCompleteness.Main.ReversibleGadgets













































































/-- Phase kickback through a reversible classical computation preserves every input wire. -/
theorem classical_phase_conjugation {n : ℕ} (f : Basis n → Basis n)
    (hf : Function.Injective f) (s : Basis n → ℂ) :
    (classicalMatrix f)ᴴ * Matrix.diagonal s * classicalMatrix f =
      Matrix.diagonal (s ∘ f) := by
  classical
  ext y x
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    classicalMatrix, Matrix.of_apply]
  by_cases hxy : y = x
  · subst y
    simp [ite_mul, mul_ite, hf.eq_iff]
  · simp [ite_mul, mul_ite, hf.eq_iff, hxy, Ne.symm hxy]











end QMAPerfectCompleteness.Main.ReversibleGadgets

end

/- Inline helpers retained from Solutions.ControlCircuits. -/
section


/-! Concrete prefix-AND and many-control circuits for the block compiler. -/

open Matrix
namespace QMAPerfectCompleteness.Main.ControlCircuits
open ReversibleGadgets



variable {r n : ℕ} (L : AndLayout r n)























































/-- The recursive prefix list agrees with the canonical increasing finRange order. -/
theorem prefixGates_eq_map (t : ℕ) (ht : t ≤ r) :
    prefixGates L t ht = (List.finRange t).map
      (fun j : Fin t => andStep L ⟨j, Nat.lt_of_lt_of_le j.isLt ht⟩) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [prefixGates, List.finRange_succ_last, List.map_append, List.map_map,
      List.map_singleton]
    rw [ih (by omega)]
    rfl

theorem prefixGates_full_eq_map :
    prefixGates L r le_rfl = (List.finRange r).map (andStep L) := by
  rw [prefixGates_eq_map]

theorem andGates_eq_map :
    andGates L = [xAt (L.flags 0)] ++ (List.finRange r).map (andStep L) := by
  rw [andGates, prefixGates_full_eq_map]

theorem andAction_injective : Function.Injective (andAction L) :=
  classicalCircuit_injective (andGates L) (andAction L) (andGates_matrix L)

end QMAPerfectCompleteness.Main.ControlCircuits


end



open Matrix
open scoped Kronecker ComplexOrder

set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.Repetition.CircuitProof
end QMAPerfectCompleteness.Main.Repetition.CircuitProof
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.Repetition QMAPerfectCompleteness.Main.Repetition.CircuitProof
open Circuit ReversibleGadgets VerifierAnalysis




































lemma QMAPerfectCompleteness.Main.Repetition.CircuitProof.copyEmbedding_disjoint (V : Verifier gatesG2) (n : ℕ) (j k : Fin n) (hjk : j ≠ k)
    (w v : Fin (V.proofQubits+V.ancillaQubits)) :
    copyEmbedding V n j w ≠ copyEmbedding V n k v := by
  intro h
  have hh := congrArg (decodeWire V n) h
  simp only [decodeWire_copy, Sum.inl.injEq, Prod.mk.injEq] at hh
  exact hjk hh.1

lemma QMAPerfectCompleteness.Main.Repetition.CircuitProof.copy_mask_iff (V : Verifier gatesG2) (n : ℕ) (j : Fin n)
    (x y : Basis (wireCount V n)) :
    (∀ w, (∀ a, copyEmbedding V n j a ≠ w) → y w = x w) ↔
      (basisEquiv V n y).2 = (basisEquiv V n x).2 ∧
      ∀ k, k ≠ j → (basisEquiv V n y).1 k = (basisEquiv V n x).1 k := by
  constructor
  · intro h
    constructor
    · funext k
      exact h _ (fun a => (flagWire_ne_copy V n k j a).symm)
    · intro k hkj
      funext w
      exact h _ (fun a => copyEmbedding_disjoint V n j k hkj.symm a w)
  · rintro ⟨hflags,hcopies⟩ w hw
    have he := encode_decode_wire V n w
    cases hd : decodeWire V n w with
    | inl kv =>
      obtain ⟨k,v⟩ := kv
      have hk : k ≠ j := by
        intro hk
        subst k
        have hencode : copyEmbedding V n j v = w := by simpa [hd, encodeWire] using he
        exact hw v hencode
      have hencode : copyEmbedding V n k v = w := by simpa [hd, encodeWire] using he
      rw [← hencode]
      exact congrFun (hcopies k hk) v
    | inr k =>
      have hencode : flagWire V n k = w := by simpa [hd, encodeWire] using he
      rw [← hencode]
      exact congrFun hflags k

/-! Generic finite tensor matrices on function-indexed copy registers. -/



lemma QMAPerfectCompleteness.Main.Repetition.CircuitProof.piMatrix_one {J α : Type*} [Fintype J] [DecidableEq J] [Fintype α] [DecidableEq α] :
    piMatrix (fun _ : J => (1 : Matrix α α ℂ)) = 1 := by
  classical
  ext y x
  by_cases hxy : y = x
  · subst y
    simp [piMatrix]
  · have hne : ∃ j, y j ≠ x j := by simpa only [funext_iff, not_forall] using hxy
    obtain ⟨j,hj⟩ := hne
    simp only [Matrix.one_apply, if_neg hxy]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [Matrix.one_apply, hj]

lemma QMAPerfectCompleteness.Main.Repetition.CircuitProof.piMatrix_mul {J α : Type*} [Fintype J] [DecidableEq J] [Fintype α]
    (M N : J → Matrix α α ℂ) :
    piMatrix (fun j => M j * N j) = piMatrix M * piMatrix N := by
  classical
  ext y x
  simp only [piMatrix, Matrix.mul_apply]
  simpa only [← Finset.prod_mul_distrib] using
    (Fintype.prod_sum (fun j k => M j (y j) k * N j k (x j)))

lemma QMAPerfectCompleteness.Main.Repetition.CircuitProof.piMatrix_single {J α : Type*} [Fintype J] [DecidableEq J] [Fintype α] [DecidableEq α]
    (j : J) (U : Matrix α α ℂ) (y x : J → α) :
    piMatrix (fun k => if k = j then U else 1) y x =
      if (∀ k, k ≠ j → y k = x k) then U (y j) (x j) else 0 := by
  classical
  by_cases hm : ∀ k, k ≠ j → y k = x k
  · rw [if_pos hm]
    unfold piMatrix
    rw [Finset.prod_eq_single j]
    · simp
    · intro k _ hkj
      simp [hkj, Matrix.one_apply, hm k hkj]
    · simp
  · rw [if_neg hm]
    push Not at hm
    obtain ⟨k,hkj,hxy⟩ := hm
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    simp [hkj, Matrix.one_apply, hxy]



lemma QMAPerfectCompleteness.Main.Repetition.CircuitProof.place_copy (V : Verifier gatesG2) (n : ℕ) (j : Fin n)
    (U : Matrix V.Wire V.Wire ℂ) :
    placeMatrix (copyEmbedding V n j) U = liftCopies V n (fun k => if k = j then U else 1) := by
  classical
  ext y x
  rw [placeMatrix_apply]
  simp only [liftCopies, Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    piMatrix_single]
  simp only [copy_mask_iff]
  by_cases hf : (basisEquiv V n y).2 = (basisEquiv V n x).2 <;>
    by_cases hc : ∀ k, k ≠ j → (basisEquiv V n y).1 k = (basisEquiv V n x).1 k <;>
    simp only [hf, hc, and_self, and_true, and_false, true_and, false_and, if_true, if_false,
      mul_one, mul_zero]
  all_goals first | rfl | (congr 1)

lemma QMAPerfectCompleteness.Main.Repetition.CircuitProof.liftCopies_one (V : Verifier gatesG2) (n : ℕ) :
    liftCopies V n (fun _ => 1) = 1 := by
  classical
  simp [liftCopies, piMatrix_one, Matrix.one_kronecker_one]

lemma QMAPerfectCompleteness.Main.Repetition.CircuitProof.liftCopies_mul (V : Verifier gatesG2) (n : ℕ)
    (M N : Fin n → Matrix V.Wire V.Wire ℂ) :
    liftCopies V n (fun k => M k * N k) = liftCopies V n M * liftCopies V n N := by
  classical
  simp only [liftCopies]
  rw [Matrix.submatrix_mul_equiv _ _ (basisEquiv V n) (basisEquiv V n) (basisEquiv V n),
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, piMatrix_mul]



/-- A list of relocated verifier copies acts as the product of its independent copy factors. -/
lemma QMAPerfectCompleteness.Main.Repetition.CircuitProof.parallelList_matrix (V : Verifier gatesG2) (n : ℕ) (js : List (Fin n)) :
    circuitMatrix (js.flatMap fun j => V.gates.map (Instr.mapWires (copyEmbedding V n j))) =
      liftCopies V n (copyProduct V js) := by
  classical
  induction js with
  | nil =>
    change 1 = liftCopies V n (fun _ => 1)
    exact (liftCopies_one V n).symm
  | cons j js ih =>
    rw [List.flatMap_cons, BlockProof.circuitMatrix_append, ih,
      circuitMatrix_mapWires, place_copy, ← liftCopies_mul]
    congr 1
    funext k
    simp [copyProduct, Verifier.unitary]

/-- Each copy index occurs exactly once in finRange, so every factor is the original V. -/
lemma QMAPerfectCompleteness.Main.Repetition.CircuitProof.copyProduct_finRange (V : Verifier gatesG2) (n : ℕ) :
    copyProduct V (List.finRange n) = fun _ => V.unitary := by
  classical
  funext k
  unfold copyProduct
  rw [List.prod_map_eq_pow_single k (fun j => if k = j then V.unitary else 1)
    (fun j hj _ => by simp [Ne.symm hj])]
  simp

/-- Exact full-register parallel-copy matrix, including identity on the AND flags. -/
theorem QMAPerfectCompleteness.Main.Repetition.CircuitProof.parallelGates_matrix (V : Verifier gatesG2) (n : ℕ) :
    circuitMatrix (parallelGates V n) = liftCopies V n (fun _ => V.unitary) := by
  rw [parallelGates, parallelList_matrix, copyProduct_finRange]



lemma QMAPerfectCompleteness.Main.Repetition.CircuitProof.basisEquiv_initial (V : Verifier gatesG2) (n : ℕ) (p : (Circuit.verifier V n).Proof) :
    basisEquiv V n ((Circuit.verifier V n).initialState p) =
      ((fun j => V.initialState (proofEquiv V n p j)), (fun _ => false)) := by
  apply Prod.ext
  · funext j w
    refine Fin.addCases (fun k => ?_) (fun a => ?_) w
    · simp [basisEquiv, Verifier.initialState, copyEmbedding_proof, Circuit.verifier, proofEquiv]
      all_goals exact Fin.append_left _ _ _
    · simp [basisEquiv, Verifier.initialState, copyEmbedding_ancilla, Circuit.verifier]
      all_goals exact Fin.append_right _ _ _
  · funext k
    simp [basisEquiv, Verifier.initialState, flagWire, Circuit.verifier]
    all_goals exact Fin.append_right _ _ _

lemma QMAPerfectCompleteness.Main.Repetition.CircuitProof.parallel_initial (V : Verifier gatesG2) (n : ℕ) (y : Basis (wireCount V n))
    (p : (Circuit.verifier V n).Proof) :
    circuitMatrix (parallelGates V n) y ((Circuit.verifier V n).initialState p) =
      piMatrix (fun _ : Fin n => V.unitary) (basisEquiv V n y).1
          (fun j => V.initialState (proofEquiv V n p j)) *
        (if (basisEquiv V n y).2 = (fun _ => false) then 1 else 0) := by
  classical
  rw [parallelGates_matrix]
  change piMatrix (fun _ : Fin n => V.unitary) (basisEquiv V n y).1
      (basisEquiv V n ((Circuit.verifier V n).initialState p)).1 *
      (if (basisEquiv V n y).2 = (basisEquiv V n ((Circuit.verifier V n).initialState p)).2 then 1 else 0) = _
  rw [basisEquiv_initial]

lemma QMAPerfectCompleteness.Main.Repetition.CircuitProof.mul_ancillaZero_apply {G : GateSet} (V : Verifier G) {α : Type*}
    (M : Matrix α V.Wire ℂ) (y : α) (p : V.Proof) :
    (M * V.ancillaZero) y p = M y (V.initialState p) := by
  classical
  simp [Matrix.mul_apply, Verifier.ancillaZero, mul_ite]

lemma QMAPerfectCompleteness.Main.Repetition.CircuitProof.gram_diagonal_apply {α β : Type*} [Fintype α] [DecidableEq α]
    (B : Matrix α β ℂ) (d : α → ℂ) (p q : β) :
    (Bᴴ * Matrix.diagonal d * B) p q = ∑ x, star (B x p) * d x * B x q := by
  classical
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply, ite_mul, mul_ite]

/-- Acceptance as a sum over output basis outcomes. -/
lemma QMAPerfectCompleteness.Main.Repetition.CircuitProof.acceptanceOperator_apply {G : GateSet} (V : Verifier G) (p q : V.Proof) :
    V.acceptanceOperator p q =
      ∑ w : V.Wire, star (V.unitary w (V.initialState p)) *
        (if w V.output then 1 else 0) * V.unitary w (V.initialState q) := by
  have heq : V.acceptanceOperator =
      (V.unitary * V.ancillaZero)ᴴ * V.acceptProjector * (V.unitary * V.ancillaZero) := by
    simp only [Verifier.acceptanceOperator, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [heq, Verifier.acceptProjector, gram_diagonal_apply]
  simp only [mul_ancillaZero_apply]



/-- Summing the accepted product amplitudes factors into the product of acceptance effects. -/
lemma QMAPerfectCompleteness.Main.Repetition.CircuitProof.factorized_acceptance_pairing (V : Verifier gatesG2) (n : ℕ) (p q : Fin n → V.Proof) :
    (∑ y : Fin n → V.Wire,
      star (piMatrix (fun _ : Fin n => V.unitary) y (fun j => V.initialState (p j))) *
        (if ∀ j, y j V.output = true then 1 else 0) *
      piMatrix (fun _ : Fin n => V.unitary) y (fun j => V.initialState (q j))) =
        piMatrix (fun _ : Fin n => V.acceptanceOperator) p q := by
  classical
  calc
    _ = ∑ y : Fin n → V.Wire, ∏ j, star (V.unitary (y j) (V.initialState (p j))) *
        (if y j V.output then 1 else 0) * V.unitary (y j) (V.initialState (q j)) := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases ha : ∀ j, y j V.output = true
      · simp only [if_pos ha, piMatrix, star_prod, mul_one, ha, if_true,
          Finset.prod_mul_distrib, forall_const, forall_true_iff]
      · simp only [if_neg ha, mul_zero, zero_mul]
        push Not at ha
        obtain ⟨j,hj⟩ := ha
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ j)
        simp [hj]
    _ = ∏ j : Fin n, ∑ w : V.Wire, star (V.unitary w (V.initialState (p j))) *
        (if w V.output then 1 else 0) * V.unitary w (V.initialState (q j)) :=
      (Fintype.prod_sum (fun (j : Fin n) (w : V.Wire) =>
        star (V.unitary w (V.initialState (p j))) * (if w V.output then (1 : ℂ) else 0) *
          V.unitary w (V.initialState (q j)))).symm
    _ = _ := by
      unfold piMatrix
      congr 1
      funext j
      exact (acceptanceOperator_apply V (p j) (q j)).symm





lemma QMAPerfectCompleteness.Main.Repetition.CircuitProof.andSuffix_eq (V : Verifier gatesG2) (n : ℕ) :
    andSuffix V n = ControlCircuits.andGates (andLayout V n) := by
  rw [ControlCircuits.andGates_eq_map]
  rfl

lemma QMAPerfectCompleteness.Main.Repetition.CircuitProof.andSuffix_matrix (V : Verifier gatesG2) (n : ℕ) :
    circuitMatrix (andSuffix V n) = classicalMatrix (ControlCircuits.andAction (andLayout V n)) := by
  rw [andSuffix_eq, ControlCircuits.andGates_matrix]

lemma QMAPerfectCompleteness.Main.Repetition.CircuitProof.and_accept_iff_clean (V : Verifier gatesG2) (n : ℕ) (x : Basis (wireCount V n))
    (hclean : ∀ k, x (flagWire V n k) = false) :
    ControlCircuits.andAction (andLayout V n) x (flagWire V n (Fin.last n)) = true ↔
      ∀ j : Fin n, x (copyEmbedding V n j V.output) = true := by
  change ControlCircuits.andAction (andLayout V n) x ((andLayout V n).flags (Fin.last n)) = true ↔ _
  rw [ControlCircuits.andAction_last _ x hclean, ControlCircuits.prefixAnd_eq_true]
  constructor
  · intro h j
    exact h j j.isLt
  · intro h j _
    exact h j

lemma QMAPerfectCompleteness.Main.Repetition.CircuitProof.verifier_unitary_decomposition (V : Verifier gatesG2) (n : ℕ) :
    (Circuit.verifier V n).unitary =
      classicalMatrix (ControlCircuits.andAction (andLayout V n)) * circuitMatrix (parallelGates V n) := by
  have heq : (Circuit.verifier V n).gates = parallelGates V n ++ andSuffix V n := by
    simp only [Circuit.verifier, andSuffix, List.append_assoc]
  rw [Verifier.unitary, heq, BlockProof.circuitMatrix_append, andSuffix_matrix]



lemma QMAPerfectCompleteness.Main.Repetition.CircuitProof.parallelInput_apply (V : Verifier gatesG2) (n : ℕ) (y : Basis (wireCount V n))
    (p : (Circuit.verifier V n).Proof) :
    parallelInput V n y p =
      piMatrix (fun _ : Fin n => V.unitary) (basisEquiv V n y).1
          (fun j => V.initialState (proofEquiv V n p j)) *
        (if (basisEquiv V n y).2 = (fun _ => false) then 1 else 0) := by
  rw [parallelInput, mul_ancillaZero_apply, parallel_initial]

/-- The AND chain can be moved into a diagonal predicate on the parallel-copy outputs. -/
lemma QMAPerfectCompleteness.Main.Repetition.CircuitProof.acceptance_as_parallel_gram (V : Verifier gatesG2) (n : ℕ) :
    (Circuit.verifier V n).acceptanceOperator =
      (parallelInput V n)ᴴ * Matrix.diagonal
        (fun x : (Circuit.verifier V n).Wire => if ControlCircuits.andAction (andLayout V n) x (flagWire V n (Fin.last n))
          then (1 : ℂ) else 0) * parallelInput V n := by
  let Q : Matrix (Circuit.verifier V n).Wire (Circuit.verifier V n).Wire ℂ :=
    classicalMatrix (ControlCircuits.andAction (andLayout V n))
  let W := circuitMatrix (parallelGates V n)
  have hdiag : Qᴴ * (Circuit.verifier V n).acceptProjector * Q =
      Matrix.diagonal (fun x : (Circuit.verifier V n).Wire => if ControlCircuits.andAction (andLayout V n) x
        (flagWire V n (Fin.last n)) then (1 : ℂ) else 0) := by
    change (classicalMatrix (ControlCircuits.andAction (andLayout V n)))ᴴ *
        Matrix.diagonal (fun x : Basis (wireCount V n) => if x (flagWire V n (Fin.last n)) then (1 : ℂ) else 0) *
        classicalMatrix (ControlCircuits.andAction (andLayout V n)) = _
    exact classical_phase_conjugation (ControlCircuits.andAction (andLayout V n))
      (ControlCircuits.andAction_injective (andLayout V n))
      (fun x : Basis (wireCount V n) => if x (flagWire V n (Fin.last n)) then (1 : ℂ) else 0)

  calc
    _ = (parallelInput V n)ᴴ * (Qᴴ * (Circuit.verifier V n).acceptProjector * Q) *
        parallelInput V n := by
      simp only [Verifier.acceptanceOperator, verifier_unitary_decomposition, parallelInput,
        Matrix.conjTranspose_mul, Matrix.mul_assoc, Q]
    _ = _ := by rw [hdiag]

lemma QMAPerfectCompleteness.Main.Repetition.CircuitProof.sum_basis_group (V : Verifier gatesG2) (n : ℕ)
    (f : Basis (wireCount V n) → ℂ) :
    (∑ x, f x) = ∑ y : (Fin n → V.Wire) × Basis (n+1), f ((basisEquiv V n).symm y) :=
  ((basisEquiv V n).symm.sum_comp f).symm

lemma QMAPerfectCompleteness.Main.Repetition.CircuitProof.grouped_input_apply (V : Verifier gatesG2) (n : ℕ) (c : Fin n → V.Wire)
    (f : Basis (n+1)) (p : (Circuit.verifier V n).Proof) :
    parallelInput V n ((basisEquiv V n).symm (c,f)) p =
      piMatrix (fun _ : Fin n => V.unitary) c
          (fun j => V.initialState (proofEquiv V n p j)) *
        (if f = (fun _ => false) then 1 else 0) := by
  rw [parallelInput_apply, Equiv.apply_symm_apply]

lemma QMAPerfectCompleteness.Main.Repetition.CircuitProof.grouped_and_predicate (V : Verifier gatesG2) (n : ℕ) (c : Fin n → V.Wire) :
    (if ControlCircuits.andAction (andLayout V n) ((basisEquiv V n).symm (c,fun _ => false))
      (flagWire V n (Fin.last n)) then (1 : ℂ) else 0) =
      if ∀ j, c j V.output = true then 1 else 0 := by
  have hclean : ∀ k, ((basisEquiv V n).symm (c,fun _ => false)) (flagWire V n k) = false := by
    intro k
    change (basisEquiv V n ((basisEquiv V n).symm (c,fun _ => false))).2 k = false
    rw [Equiv.apply_symm_apply]
  have hcopy (j : Fin n) : ((basisEquiv V n).symm (c,fun _ => false))
      (copyEmbedding V n j V.output) = c j V.output := by
    change (basisEquiv V n ((basisEquiv V n).symm (c,fun _ => false))).1 j V.output = _
    rw [Equiv.apply_symm_apply]
  have hiff := and_accept_iff_clean V n ((basisEquiv V n).symm (c,fun _ => false)) hclean
  simp only [hcopy] at hiff
  by_cases hc : ∀ j, c j V.output = true
  · simp [hc, hiff.mpr hc]
  · have hfalse := mt hiff.mp hc
    simp [hc, hfalse]

/-- The physical repeated verifier has exactly the tensor acceptance effect after regrouping
its proof register. This equality includes the initialized AND flags and all copy ancillas. -/
theorem solution (V : Verifier gatesG2) (n : ℕ) :
    (Circuit.verifier V n).acceptanceOperator =
      (piMatrix (fun _ : Fin n => V.acceptanceOperator)).submatrix (proofEquiv V n) (proofEquiv V n) := by
  classical
  ext p q
  rw [acceptance_as_parallel_gram, gram_diagonal_apply]
  change (∑ x : Basis (wireCount V n), star (parallelInput V n x p) *
      (if ControlCircuits.andAction (andLayout V n) x (flagWire V n (Fin.last n)) then (1 : ℂ) else 0) *
      parallelInput V n x q) = _
  rw [sum_basis_group V n]
  simp only [Fintype.sum_prod_type, Matrix.submatrix_apply]
  calc
    _ = ∑ c : Fin n → V.Wire,
        star (piMatrix (fun _ : Fin n => V.unitary) c (fun j => V.initialState (proofEquiv V n p j))) *
          (if ∀ j, c j V.output = true then 1 else 0) *
        piMatrix (fun _ : Fin n => V.unitary) c (fun j => V.initialState (proofEquiv V n q j)) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_eq_single (fun _ => false)]
      · rw [grouped_input_apply, grouped_input_apply]
        simp only [if_pos rfl, if_true, mul_one]
        rw [grouped_and_predicate]
      · intro f _ hf
        simp only [grouped_input_apply, if_neg hf, mul_zero, star_zero, zero_mul]
      · simp
    _ = _ := factorized_acceptance_pairing V n (proofEquiv V n p) (proofEquiv V n q)
