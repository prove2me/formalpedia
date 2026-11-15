-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.HTCompiler.compileVerifier_acceptanceOperator
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T17:08:17.962437+00:00
-- url     : https://prove2.me/submissions/08e04f78-68c8-4bb3-bc15-c3702de64618

/- Generated from Solutions.HTPreservation by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Gates
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_GateCompilation
import Definitions.Def_QMAPerfectCompleteness_Proof_HTCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_HTPreservation
import Definitions.Def_QMAPerfectCompleteness_Proof_HadamardToffoli
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_RealSimulation
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

/- Inline helpers retained from Solutions.CircuitUnitary. -/
section


open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.CircuitProof





















theorem initialState_injective {G : GateSet} (V : Verifier G) :
    Function.Injective V.initialState := by
  intro p q hpq
  funext j
  have h := congrFun hpq (Fin.castAdd V.ancillaQubits j)
  simpa [Verifier.initialState] using h

/-- Initialization of the ancillas in zero is an isometry. -/
theorem ancillaZero_isometry {G : GateSet} (V : Verifier G) :
    V.ancillaZeroᴴ * V.ancillaZero = 1 := by
  classical
  ext p q
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Verifier.ancillaZero, Matrix.of_apply,
    apply_ite, star_one, star_zero, Matrix.one_apply]
  rw [Finset.sum_eq_single (V.initialState p)]
  · simp [initialState_injective V |>.eq_iff, eq_comm]
  · intro w _ hw
    simp [hw]
  · simp

open scoped ComplexOrder



end QMAPerfectCompleteness.Main.CircuitProof

end

/- Inline helpers retained from Solutions.GateCompilation. -/
section


open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.GateCompilation



@[simp] theorem pairedH_matrix : pairedH.matrix = hadamardTwoMatrix := by
  ext y x
  have hu : (∀ w : Fin 2, (∀ a : Fin 2, a ≠ w) → y w = x w) := by
    intro w h
    exact False.elim (h w rfl)
  change (if ∀ w : Fin 2, (∀ a : Fin 2, a ≠ w) → y w = x w then
      hadamardTwoMatrix y x else 0) = hadamardTwoMatrix y x
  exact if_pos hu

@[simp] theorem pairedH_circuit : circuitMatrix [pairedH] = hadamardTwoMatrix := by
  simp [circuitMatrix]



/-- Actual gate-list semantics of replacing H by H⊗H. The ignored wire evolves by H as well. -/
theorem pairedH_semantics : circuitMatrix [pairedH] =
    (hadamardMatrix ⊗ₖ hadamardMatrix).submatrix splitTwo splitTwo := by
  rw [pairedH_circuit]
  have hs : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  ext y x
  change (if xor (y 0 && x 0) (y 1 && x 1) then -(1 / 2 : ℂ) else 1 / 2) =
    (if y 0 && x 0 then -((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) *
    (if y 1 && x 1 then -((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else ((Real.sqrt 2 : ℝ) : ℂ)⁻¹)
  cases y 0 <;> cases x 0 <;> cases y 1 <;> cases x 1 <;> simp [hs]





















theorem simulationHH_matrix : simulationHH.matrix = simulationHHQ.map (Rat.cast : ℚ → ℂ) := by
  ext y x
  have hwire : (∀ w : Fin 4, (∀ a : Fin 2, (![0,3] : Fin 2 → Fin 4) a ≠ w) → y w = x w) ↔
      y 1 = x 1 ∧ y 2 = x 2 := by
    simp [Fin.forall_fin_succ]
  change (if ∀ w : Fin 4, (∀ a : Fin 2, (![0,3] : Fin 2 → Fin 4) a ≠ w) → y w = x w then
    (if xor (y 0 && x 0) (y 3 && x 3) then -(1 / 2 : ℂ) else 1 / 2) else 0) =
    ((simulationHHQ y x : ℚ) : ℂ)
  simp only [hwire]
  simp only [simulationHHQ]
  split_ifs <;> norm_num

theorem simulationToffoli_matrix :
    simulationToffoli.matrix = simulationToffoliQ.map (Rat.cast : ℚ → ℂ) := by
  ext y x
  have hwire : (∀ w : Fin 4, (∀ a : Fin 3, (![1,2,0] : Fin 3 → Fin 4) a ≠ w) → y w = x w) ↔
      y 3 = x 3 := by
    simp [Fin.forall_fin_succ]
  change (if ∀ w : Fin 4, (∀ a : Fin 3, (![1,2,0] : Fin 3 → Fin 4) a ≠ w) → y w = x w then
    (if (y ∘ (![1,2,0] : Fin 3 → Fin 4)) =
      ![x 1, x 2, xor (x 0) (x 1 && x 2)] then (1 : ℂ) else 0) else 0) =
    ((simulationToffoliQ y x : ℚ) : ℂ)
  simp only [hwire]
  simp only [simulationToffoliQ, funext_iff, Fin.forall_fin_succ]
  by_cases h0 : y 0 = xor (x 0) (x 1 && x 2) <;>
    by_cases h1 : y 1 = x 1 <;> by_cases h2 : y 2 = x 2 <;> by_cases h3 : y 3 = x 3 <;>
    simp_all

private theorem sum_basis_four (f : Basis 4 → ℚ) :
    ∑ z, f z = f ![false, false, false, false] + f ![false, false, false, true] + f ![false, false, true, false] + f ![false, false, true, true] + f ![false, true, false, false] + f ![false, true, false, true] + f ![false, true, true, false] + f ![false, true, true, true] + f ![true, false, false, false] + f ![true, false, false, true] + f ![true, false, true, false] + f ![true, false, true, true] + f ![true, true, false, false] + f ![true, true, false, true] + f ![true, true, true, false] + f ![true, true, true, true] := by
  have hu : (Finset.univ : Finset (Basis 4)) = {![false, false, false, false], ![false, false, false, true], ![false, false, true, false], ![false, false, true, true], ![false, true, false, false], ![false, true, false, true], ![false, true, true, false], ![false, true, true, true], ![true, false, false, false], ![true, false, false, true], ![true, false, true, false], ![true, false, true, true], ![true, true, false, false], ![true, true, false, true], ![true, true, true, false], ![true, true, true, true]} := by decide
  rw [hu, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring



lemma flipCC_involutive : Function.Involutive flipCC := by
  intro x
  funext i
  fin_cases i <;> simp [flipCC]

lemma simulationToffoliQ_eq (y x : Basis 4) :
    simulationToffoliQ y x = if y = flipCC x then 1 else 0 := by
  simp [simulationToffoliQ, flipCC, funext_iff, Fin.forall_fin_succ]

lemma simulationToffoliQ_mul (M : Matrix (Basis 4) (Basis 4) ℚ) (y x : Basis 4) :
    (simulationToffoliQ * M) y x = M (flipCC y) x := by
  simp only [Matrix.mul_apply, simulationToffoliQ_eq]
  rw [Finset.sum_eq_single (flipCC y)]
  · simp [flipCC_involutive y]
  · intro z _ hz
    have hyz : y ≠ flipCC z := fun h => hz (by rw [h, flipCC_involutive z])
    simp [hyz]
  · simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The exact rational identity behind the clean four-gate realization. -/
theorem simulation_identity_Q :
    simulationToffoliQ * simulationHHQ * simulationToffoliQ * simulationHHQ =
      controlledQuarterTurnQ := by
  have ha : simulationToffoliQ * simulationHHQ * simulationToffoliQ * simulationHHQ =
      simulationToffoliQ * (simulationHHQ * (simulationToffoliQ * simulationHHQ)) := by
    simp only [Matrix.mul_assoc]
  rw [ha]
  ext y x
  rw [simulationToffoliQ_mul]
  change (∑ z : Basis 4, simulationHHQ (flipCC y) z *
    (simulationToffoliQ * simulationHHQ) z x) = controlledQuarterTurnQ y x
  simp_rw [simulationToffoliQ_mul]
  have hy : y = ![y 0, y 1, y 2, y 3] := by funext i; fin_cases i <;> rfl
  have hx : x = ![x 0, x 1, x 2, x 3] := by funext i; fin_cases i <;> rfl
  rw [hy, hx]
  cases y 0 <;> cases y 1 <;> cases y 2 <;> cases y 3 <;>
    cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;>
    norm_num [sum_basis_four, simulationHHQ, controlledQuarterTurnQ, flipCC,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]









theorem realControlledPhaseCircuit_matrix :
    circuitMatrix realControlledPhaseCircuit = controlledQuarterTurnQ.map (Rat.cast : ℚ → ℂ) := by
  have h := congrArg (fun M : Matrix (Basis 4) (Basis 4) ℚ => M.map (Rat.cast : ℚ → ℂ))
    simulation_identity_Q
  simpa only [realControlledPhaseCircuit, circuitMatrix, Matrix.one_mul,
    simulationHH_matrix, simulationToffoli_matrix, Matrix.map_mul_ratCast] using h











end QMAPerfectCompleteness.Main.GateCompilation

end

/- Inline helpers retained from Solutions.ReversibleGadgets. -/
section


/-! Explicit G₂ circuit gadgets used by the block-encoding compiler. -/

open Matrix
open scoped Kronecker

namespace QMAPerfectCompleteness.Main.ReversibleGadgets































































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

























end QMAPerfectCompleteness.Main.ReversibleGadgets

end

/- Inline helpers retained from Solutions.HadamardToffoli. -/
section


/-! Concrete exact G₂-to-Hadamard/Toffoli gadgets. The CZ construction is the controlled
quarter-turn squared, equivalently Takeuchi 2024 Fig.3(a), Appendix B:
https://arxiv.org/html/2312.16433v2 . No general synthesis theorem is used. -/
open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.HadamardToffoli
open GateCompilation ReversibleGadgets





lemma hAt_zero : (hAt (0 : Fin 2)).matrix =
    (hadamardMatrix ⊗ₖ (1 : Matrix (Basis 1) (Basis 1) ℂ)).submatrix splitTwo splitTwo := by
  ext y x
  have hkeep : (∀ w : Fin 2, (∀ a : Fin 1, (0 : Fin 2) ≠ w) → y w = x w) ↔ y 1 = x 1 := by
    simp [Fin.forall_fin_succ]
  change (if ∀ w : Fin 2, (∀ a : Fin 1, (0 : Fin 2) ≠ w) → y w = x w then
    hadamardMatrix (fun _ => y 0) (fun _ => x 0) else 0) = _
  simp only [hkeep, Matrix.submatrix_apply, Matrix.kronecker_apply, splitTwo,
    Matrix.one_apply, Matrix.kroneckerMap_apply]
  by_cases h : y 1 = x 1
  · have hf : (fun _ : Fin 1 => y 1) = (fun _ => x 1) := by simp [h]
    simp [h, hf]
  · have hf : (fun _ : Fin 1 => y 1) ≠ (fun _ => x 1) := by intro he; exact h (congrFun he 0)
    simp [h, hf]

lemma hAt_one : (hAt (1 : Fin 2)).matrix =
    ((1 : Matrix (Basis 1) (Basis 1) ℂ) ⊗ₖ hadamardMatrix).submatrix splitTwo splitTwo := by
  ext y x
  have hkeep : (∀ w : Fin 2, (∀ a : Fin 1, (1 : Fin 2) ≠ w) → y w = x w) ↔ y 0 = x 0 := by
    simp [Fin.forall_fin_succ]
  change (if ∀ w : Fin 2, (∀ a : Fin 1, (1 : Fin 2) ≠ w) → y w = x w then
    hadamardMatrix (fun _ => y 1) (fun _ => x 1) else 0) = _
  simp only [hkeep, Matrix.submatrix_apply, Matrix.kronecker_apply, splitTwo,
    Matrix.one_apply, Matrix.kroneckerMap_apply]
  by_cases h : y 0 = x 0
  · have hf : (fun _ : Fin 1 => y 0) = (fun _ => x 0) := by simp [h]
    simp [h, hf]
  · have hf : (fun _ : Fin 1 => y 0) ≠ (fun _ => x 0) := by intro he; exact h (congrFun he 0)
    simp [h, hf]

/-- Two literal HT Hadamards implement one G₂ paired Hadamard. -/
theorem paired_hadamard : circuitMatrix [hAt (0 : Fin 2), hAt 1] = hadamardTwoMatrix := by
  simp only [circuitMatrix, Matrix.one_mul, hAt_zero, hAt_one]
  rw [Matrix.submatrix_mul_equiv _ _ splitTwo splitTwo splitTwo,
    ← Matrix.mul_kronecker_mul]
  simpa using pairedH_semantics.symm



theorem hhAt_matrix {n : ℕ} (e : Fin 2 ↪ Fin n) :
    circuitMatrix (hhAt e) = placeMatrix e hadamardTwoMatrix := by
  rw [hhAt, circuitMatrix_mapWires, paired_hadamard]






lemma hh_simulation : circuitMatrix (hhAt simulationWires) = simulationHH.matrix := by
  rw [hhAt_matrix]
  have hi : Instr.mapWires simulationWires pairedH = simulationHH := by rfl
  rw [← hi, instr_mapWires_matrix, pairedH_matrix]

lemma t_simulation : (tAt toffoliWires).matrix = simulationToffoli.matrix := by
  rfl

theorem quarterTurn_matrix : circuitMatrix quarterTurn = controlledQuarterTurnQ.map (Rat.cast : ℚ → ℂ) := by
  rw [quarterTurn]
  simp only [BlockProof.circuitMatrix_append, circuitMatrix, Matrix.one_mul,
    hh_simulation, t_simulation]
  simpa [realControlledPhaseCircuit, circuitMatrix, Matrix.mul_assoc] using realControlledPhaseCircuit_matrix

lemma quarterTurnQ_apply (y x : Basis 4) :
    controlledQuarterTurnQ y x = if y = flipCC x then
      (if x 0 && x 1 && x 2 then -1 else 1) else 0 := by
  simp [controlledQuarterTurnQ, flipCC, funext_iff, Fin.forall_fin_succ]



lemma quarterTurnQ_sq : controlledQuarterTurnQ * controlledQuarterTurnQ = czQ := by
  ext y x
  simp only [Matrix.mul_apply, quarterTurnQ_apply]
  rw [Finset.sum_eq_single (flipCC y)]
  · by_cases h : y = x
    · subst x
      simp only [flipCC_involutive y, if_true, czQ, Matrix.diagonal_apply_eq]
      cases h0 : y 0 <;> cases h1 : y 1 <;> cases h2 : y 2 <;>
        norm_num [flipCC, h0, h1, h2, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    · have hf : flipCC y ≠ flipCC x := fun he => h (flipCC_involutive.injective he)
      simp [flipCC_involutive y, hf, czQ, Matrix.diagonal_apply, h]
  · intro z _ hz
    have hy : y ≠ flipCC z := fun h => hz (by rw [h, flipCC_involutive z])
    simp [hy]
  · simp



theorem controlledZ_matrix : circuitMatrix controlledZ = czQ.map (Rat.cast : ℚ → ℂ) := by
  rw [controlledZ, BlockProof.circuitMatrix_append, quarterTurn_matrix]
  have h := congrArg (fun M : Matrix (Basis 4) (Basis 4) ℚ => M.map (Rat.cast : ℚ → ℂ)) quarterTurnQ_sq
  simpa only [Matrix.map_mul_ratCast] using h



lemma hAt_two_apply (y x : Basis 4) : (hAt (2 : Fin 4)).matrix y x =
    if y 0 = x 0 ∧ y 1 = x 1 ∧ y 3 = x 3 then
      (if y 2 && x 2 then -((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else ((Real.sqrt 2 : ℝ) : ℂ)⁻¹)
    else 0 := by
  have hk : (∀ w : Fin 4, (∀ a : Fin 1, (2 : Fin 4) ≠ w) → y w = x w) ↔
      y 0 = x 0 ∧ y 1 = x 1 ∧ y 3 = x 3 := by simp [Fin.forall_fin_succ]
  change (if ∀ w : Fin 4, (∀ a : Fin 1, (2 : Fin 4) ≠ w) → y w = x w then
    (if y 2 && x 2 then -((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) else 0) = _
  simp only [hk]

lemma controlledZ_diagonal : circuitMatrix controlledZ =
    Matrix.diagonal (fun x : Basis 4 => if x 1 && x 2 then (-1 : ℂ) else 1) := by
  rw [controlledZ_matrix]
  ext y x
  simp only [czQ, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> norm_num



lemma controlledNot_matrix_expression : circuitMatrix controlledNot =
    ((hAt (2 : Fin 4)).matrix *
      Matrix.diagonal (fun x : Basis 4 => if x 1 && x 2 then (-1 : ℂ) else 1)) *
      (hAt (2 : Fin 4)).matrix := by
  simp [controlledNot, BlockProof.circuitMatrix_append, circuitMatrix, controlledZ_diagonal,
    Matrix.mul_assoc]



private theorem sum_basis_four (f : Basis 4 → ℂ) :
    ∑ z, f z = ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, ∑ d : Bool, f ![a,b,c,d] := by
  let e : Basis 4 ≃ Bool × Bool × Bool × Bool :=
    { toFun := fun z => (z 0,z 1,z 2,z 3)
      invFun := fun z => ![z.1,z.2.1,z.2.2.1,z.2.2.2]
      left_inv := by intro z; funext i; fin_cases i <;> rfl
      right_inv := by rintro ⟨a,b,c,d⟩; rfl }
  simpa [e, Fintype.sum_prod_type] using (Equiv.sum_comp e.symm f).symm

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem controlledNot_matrix (y x : Basis 4) :
    circuitMatrix controlledNot y x = if y = cnotAction x then 1 else 0 := by
  rw [controlledNot_matrix_expression]
  change (∑ z : Basis 4, ((hAt (2 : Fin 4)).matrix *
    Matrix.diagonal (fun z : Basis 4 => if z 1 && z 2 then (-1 : ℂ) else 1)) y z *
      (hAt (2 : Fin 4)).matrix z x) = _
  simp_rw [Matrix.mul_diagonal, hAt_two_apply]
  rw [sum_basis_four]
  have hs : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have hy : y = ![y 0,y 1,y 2,y 3] := by funext i; fin_cases i <;> rfl
  have hx : x = ![x 0,x 1,x 2,x 3] := by funext i; fin_cases i <;> rfl
  rw [hy,hx]
  cases h0 : y 0 <;> cases h1 : y 1 <;> cases h2 : y 2 <;> cases h3 : y 3 <;>
    cases h4 : x 0 <;> cases h5 : x 1 <;> cases h6 : x 2 <;> cases h7 : x 3 <;>
    norm_num [cnotAction, Fintype.sum_bool, h0,h1,h2,h3,h4,h5,h6,h7,hs,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, mul_assoc,
      funext_iff, Fin.forall_fin_succ]



lemma cnotAction_involutive : Function.Involutive cnotAction := by
  intro x
  funext i
  fin_cases i <;> simp [cnotAction, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]

lemma controlledNot_classical : circuitMatrix controlledNot = classicalMatrix cnotAction := by
  ext y x
  exact controlledNot_matrix y x

lemma classical_left {n : ℕ} (f : Basis n → Basis n) (hf : Function.Involutive f)
    (M : Matrix (Basis n) (Basis n) ℂ) (y x : Basis n) :
    (classicalMatrix f * M) y x = M (f y) x := by
  simp only [Matrix.mul_apply, classicalMatrix, Matrix.of_apply]
  rw [Finset.sum_eq_single (f y)]
  · simp [hf y]
  · intro z _ hz
    have hy : y ≠ f z := fun h => hz (by rw [h, hf z])
    simp [hy]
  · simp

lemma classical_diagonal_conjugate {n : ℕ} (f : Basis n → Basis n)
    (hf : Function.Involutive f) (d : Basis n → ℂ) :
    classicalMatrix f * Matrix.diagonal d * classicalMatrix f = Matrix.diagonal (d ∘ f) := by
  rw [Matrix.mul_assoc]
  ext y x
  rw [classical_left f hf, Matrix.diagonal_mul]
  simp [classicalMatrix, Matrix.diagonal_apply, hf.injective.eq_iff, Function.comp_apply]

lemma hAt_one_apply_four (y x : Basis 4) : (hAt (1 : Fin 4)).matrix y x =
    if y 0 = x 0 ∧ y 2 = x 2 ∧ y 3 = x 3 then
      (if y 1 && x 1 then -((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else ((Real.sqrt 2 : ℝ) : ℂ)⁻¹)
    else 0 := by
  have hk : (∀ w : Fin 4, (∀ a : Fin 1, (1 : Fin 4) ≠ w) → y w = x w) ↔
      y 0 = x 0 ∧ y 2 = x 2 ∧ y 3 = x 3 := by simp [Fin.forall_fin_succ]
  change (if ∀ w : Fin 4, (∀ a : Fin 1, (1 : Fin 4) ≠ w) → y w = x w then
    (if y 1 && x 1 then -((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) else 0) = _
  simp only [hk]





lemma bitFlipClean_matrix_expression : circuitMatrix bitFlipClean =
    ((hAt (1 : Fin 4)).matrix *
      Matrix.diagonal (fun x : Basis 4 => if (cnotAction x) 1 && (cnotAction x) 2 then (-1 : ℂ) else 1)) *
      (hAt (1 : Fin 4)).matrix := by
  simp only [bitFlipClean, BlockProof.circuitMatrix_append, circuitMatrix, Matrix.one_mul,
    controlledNot_classical, controlledZ_diagonal]
  have hconj := classical_diagonal_conjugate cnotAction cnotAction_involutive
    (fun x : Basis 4 => if x 1 && x 2 then (-1 : ℂ) else 1)
  simpa only [Matrix.mul_assoc, Function.comp_def] using
    congrArg (fun M => (hAt (1 : Fin 4)).matrix * M * (hAt (1 : Fin 4)).matrix) hconj

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem bitFlipClean_matrix (y x : Basis 4) :
    circuitMatrix bitFlipClean y x = if y = negativeControlAction x then 1 else 0 := by
  rw [bitFlipClean_matrix_expression]
  change (∑ z : Basis 4, ((hAt (1 : Fin 4)).matrix *
    Matrix.diagonal (fun z : Basis 4 => if (cnotAction z) 1 && (cnotAction z) 2 then (-1 : ℂ) else 1)) y z *
      (hAt (1 : Fin 4)).matrix z x) = _
  simp_rw [Matrix.mul_diagonal, hAt_one_apply_four]
  rw [sum_basis_four]
  have hs : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have hy : y = ![y 0,y 1,y 2,y 3] := by funext i; fin_cases i <;> rfl
  have hx : x = ![x 0,x 1,x 2,x 3] := by funext i; fin_cases i <;> rfl
  rw [hy,hx]
  cases h0 : y 0 <;> cases h1 : y 1 <;> cases h2 : y 2 <;> cases h3 : y 3 <;>
    cases h4 : x 0 <;> cases h5 : x 1 <;> cases h6 : x 2 <;> cases h7 : x 3 <;>
    norm_num [negativeControlAction, cnotAction, Fintype.sum_bool, h0,h1,h2,h3,h4,h5,h6,h7,hs,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, mul_assoc,
      funext_iff, Fin.forall_fin_succ]



/-- Clean-workspace contract for X on wire1; all other wires are restored. -/
theorem bitFlipClean_zero (y x : Basis 4) (hx : x 2 = false) :
    circuitMatrix bitFlipClean y x = if y = Function.update x 1 (!x 1) then 1 else 0 := by
  rw [bitFlipClean_matrix]
  have heq : negativeControlAction x = Function.update x 1 (!x 1) := by
    funext i
    fin_cases i <;> simp [negativeControlAction, hx, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons]
  rw [heq]

end QMAPerfectCompleteness.Main.HadamardToffoli

end



open Matrix
open scoped Kronecker
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.HTCompiler
end QMAPerfectCompleteness.Main.HTCompiler
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.HTCompiler
open HadamardToffoli ReversibleGadgets






@[simp] theorem QMAPerfectCompleteness.Main.HTCompiler.dataPart_basisZero {n : ℕ} (x : Basis n) : dataPart (basisZero x) = x := by
  funext w
  change Fin.append x (fun _ : Fin 3 => false) (Fin.castAdd 3 w) = x w
  exact Fin.append_left _ _ _

@[simp] theorem QMAPerfectCompleteness.Main.HTCompiler.basisZero_clean {n : ℕ} (x : Basis n) : IsClean (basisZero x) := by
  intro j
  exact Fin.append_right _ _ _



theorem QMAPerfectCompleteness.Main.HTCompiler.clean_eq_basisZero {n : ℕ} (y : Basis (n+3)) : IsClean y ↔ y = basisZero (dataPart y) := by
  constructor
  · intro h
    funext w
    refine Fin.addCases (fun a => ?_) (fun j => ?_) w
    · change y (Fin.castAdd 3 a) = (Fin.append (dataPart y) (fun _ => false)) (Fin.castAdd 3 a)
      rw [Fin.append_left]
      rfl
    · change y (Fin.natAdd n j) = (Fin.append (dataPart y) (fun _ => false)) (Fin.natAdd n j)
      rw [Fin.append_right]
      exact h j
  · intro h
    rw [h]
    exact basisZero_clean _

theorem QMAPerfectCompleteness.Main.HTCompiler.basisZero_eq_iff {n : ℕ} (y : Basis (n+3)) (x : Basis n) :
    y = basisZero x ↔ IsClean y ∧ dataPart y = x := by
  constructor
  · intro h
    subst y
    simp
  · rintro ⟨hclean,hdata⟩
    exact (clean_eq_basisZero y).mp hclean |>.trans (congrArg basisZero hdata)



lemma QMAPerfectCompleteness.Main.HTCompiler.mul_cleanEmbedding {n : ℕ} (A : Matrix (Basis (n+3)) (Basis (n+3)) ℂ)
    (y : Basis (n+3)) (x : Basis n) : (A * cleanEmbedding n) y x = A y (basisZero x) := by
  simp [Matrix.mul_apply, cleanEmbedding, mul_ite]

lemma QMAPerfectCompleteness.Main.HTCompiler.cleanEmbedding_mul {n : ℕ} (A : Matrix (Basis n) (Basis n) ℂ)
    (y : Basis (n+3)) (x : Basis n) :
    (cleanEmbedding n * A) y x = if IsClean y then A (dataPart y) x else 0 := by
  simp only [Matrix.mul_apply, cleanEmbedding, Matrix.of_apply]
  by_cases hc : IsClean y
  · have heq (z : Basis n) : y = basisZero z ↔ dataPart y = z := by
      simp only [basisZero_eq_iff, hc, true_and]
    simp only [heq]
    simp [ite_mul,hc,eq_comm]
  · have heq (z : Basis n) : y ≠ basisZero z := by
      intro h
      exact hc ((basisZero_eq_iff y z).mp h).1
    simp [heq,hc]

theorem QMAPerfectCompleteness.Main.HTCompiler.cleanEmbedding_isometry (n : ℕ) : (cleanEmbedding n)ᴴ * cleanEmbedding n = 1 := by
  let V : Verifier gatesG2 := ⟨n,3,[],⟨0,by omega⟩⟩
  exact CircuitProof.ancillaZero_isometry V

lemma QMAPerfectCompleteness.Main.HTCompiler.placeMatrix_basisZero {n : ℕ} (A : Matrix (Basis n) (Basis n) ℂ)
    (y : Basis (n+3)) (x : Basis n) :
    placeMatrix (dataEmbedding n) A y (basisZero x) = if IsClean y then A (dataPart y) x else 0 := by
  have hmask : (∀ w, (∀ a, dataEmbedding n a ≠ w) → y w = basisZero x w) ↔ IsClean y := by
    constructor
    · intro h j
      have hj := h (Fin.natAdd n j) (by
        intro a ha
        have hv := congrArg Fin.val ha
        change a.val = n + j.val at hv
        have := a.isLt
        omega)
      simpa [basisZero] using hj
    · intro h w hw
      revert hw
      refine Fin.addCases (fun a hw => ?_) (fun j hw => ?_) w
      · exact False.elim (hw a rfl)
      · simpa [basisZero] using h j
  rw [placeMatrix_apply]
  change (if ∀ w, (∀ a, dataEmbedding n a ≠ w) → y w = basisZero x w then
    A (dataPart y) (dataPart (basisZero x)) else 0) = _
  simp only [hmask, dataPart_basisZero]

theorem QMAPerfectCompleteness.Main.HTCompiler.placeMatrix_intertwines {n : ℕ} (A : Matrix (Basis n) (Basis n) ℂ) :
    placeMatrix (dataEmbedding n) A * cleanEmbedding n = cleanEmbedding n * A := by
  ext y x
  rw [mul_cleanEmbedding, placeMatrix_basisZero, cleanEmbedding_mul]

/-- Transfer a local deterministic action to arbitrary selected wires, for a fixed allowed
input column. It suffices that the local clean-workspace contract holds on that column. -/
lemma QMAPerfectCompleteness.Main.HTCompiler.placeMatrix_classical_column {r n : ℕ} (e : Fin r ↪ Fin n)
    (A : Matrix (Basis r) (Basis r) ℂ) (σ : Basis r → Basis r) (y x : Basis n)
    (hA : ∀ z, A z (x ∘ e) = if z = σ (x ∘ e) then 1 else 0) :
    placeMatrix e A y x = if y = placePermutation e σ x then 1 else 0 := by
  rw [placeMatrix_apply, hA]
  have hiff : (∀ w, (∀ a, e a ≠ w) → y w = x w) ∧ y ∘ e = σ (x ∘ e) ↔
      y = placePermutation e σ x := by
    rw [← (CircuitProof.splitTargets e).apply_eq_iff_eq]
    simp only [placePermutation, Equiv.apply_symm_apply, Prod.ext_iff, CircuitProof.splitTargets_fst]
    rw [CircuitProof.unaffected_iff e x y]
    exact and_comm
  rw [← ite_and]
  simp only [hiff]

lemma QMAPerfectCompleteness.Main.HTCompiler.compileInstr_X {n : ℕ} (e : Fin 1 ↪ Fin n) :
    compileInstr (⟨⟨0,by decide⟩,e⟩ : Instr gatesG2 n) =
      bitFlipClean.map (Instr.mapWires (xPlacement (e 0))) := by rfl
lemma QMAPerfectCompleteness.Main.HTCompiler.compileInstr_CNOT {n : ℕ} (e : Fin 2 ↪ Fin n) :
    compileInstr (⟨⟨1,by decide⟩,e⟩ : Instr gatesG2 n) =
      controlledNot.map (Instr.mapWires (cnotPlacement e)) := by rfl
lemma QMAPerfectCompleteness.Main.HTCompiler.compileInstr_Toffoli {n : ℕ} (e : Fin 3 ↪ Fin n) :
    compileInstr (⟨⟨2,by decide⟩,e⟩ : Instr gatesG2 n) =
      [tAt (e.trans (dataEmbedding n))] := by rfl
lemma QMAPerfectCompleteness.Main.HTCompiler.compileInstr_HH {n : ℕ} (e : Fin 2 ↪ Fin n) :
    compileInstr (⟨⟨3,by decide⟩,e⟩ : Instr gatesG2 n) =
      [hAt (dataEmbedding n (e 0)), hAt (dataEmbedding n (e 1))] := by rfl

lemma QMAPerfectCompleteness.Main.HTCompiler.instr_X_action {n : ℕ} (e : Fin 1 ↪ Fin n) (y x : Basis n) :
    (⟨⟨0,by decide⟩,e⟩ : Instr gatesG2 n).matrix y x =
      if y = Function.update x (e 0) (!(x (e 0))) then 1 else 0 := by
  let σ : Basis 1 → Basis 1 := fun u => Function.update u 0 (!(u 0))
  have hgate : (gatesG2.get (⟨0,by decide⟩ : Fin gatesG2.length)).matrix = classicalMatrix σ := by
    change classicalMatrix (fun u : Basis 1 => ![!u 0]) = classicalMatrix σ
    congr 1
    funext u i
    fin_cases i
    simp [σ]
  rw [instr_classical (⟨⟨0,by decide⟩,e⟩ : Instr gatesG2 n) σ hgate]
  change (if y = placePermutation e (fun u => Function.update u 0 (!(u 0))) x then 1 else 0) = _
  rw [place_update]
  rfl

lemma QMAPerfectCompleteness.Main.HTCompiler.instr_CNOT_action {n : ℕ} (e : Fin 2 ↪ Fin n) (y x : Basis n) :
    (⟨⟨1,by decide⟩,e⟩ : Instr gatesG2 n).matrix y x =
      if y = Function.update x (e 1) (xor (x (e 1)) (x (e 0))) then 1 else 0 := by
  let σ : Basis 2 → Basis 2 := fun u => Function.update u 1 (xor (u 1) (u 0))
  have hgate : (gatesG2.get (⟨1,by decide⟩ : Fin gatesG2.length)).matrix = classicalMatrix σ := by
    change classicalMatrix (fun u : Basis 2 => ![u 0, xor (u 1) (u 0)]) = classicalMatrix σ
    congr 1
    funext u i
    fin_cases i <;> simp [σ]
  rw [instr_classical (⟨⟨1,by decide⟩,e⟩ : Instr gatesG2 n) σ hgate]
  change (if y = placePermutation e (fun u => Function.update u 1 (xor (u 1) (u 0))) x then 1 else 0) = _
  rw [place_update]
  rfl

lemma QMAPerfectCompleteness.Main.HTCompiler.compileInstr_X_action {n : ℕ} (e : Fin 1 ↪ Fin n) (y x : Basis (n+3)) (hx : IsClean x) :
    circuitMatrix (compileInstr (⟨⟨0,by decide⟩,e⟩ : Instr gatesG2 n)) y x =
      if y = Function.update x (dataEmbedding n (e 0)) (!(x (dataEmbedding n (e 0)))) then 1 else 0 := by
  rw [compileInstr_X, circuitMatrix_mapWires]
  let σ : Basis 4 → Basis 4 := fun u => Function.update u 1 (!(u 1))
  have hx2 : (x ∘ xPlacement (e 0)) 2 = false := by
    exact hx 0
  have hcol : ∀ z, circuitMatrix bitFlipClean z (x ∘ xPlacement (e 0)) =
      if z = σ (x ∘ xPlacement (e 0)) then 1 else 0 :=
    fun z => bitFlipClean_zero z _ hx2
  rw [placeMatrix_classical_column _ _ σ y x hcol, place_update]
  rfl

lemma QMAPerfectCompleteness.Main.HTCompiler.compileInstr_CNOT_action {n : ℕ} (e : Fin 2 ↪ Fin n) (y x : Basis (n+3)) :
    circuitMatrix (compileInstr (⟨⟨1,by decide⟩,e⟩ : Instr gatesG2 n)) y x =
      if y = Function.update x (dataEmbedding n (e 1))
        (xor (x (dataEmbedding n (e 1))) (x (dataEmbedding n (e 0)))) then 1 else 0 := by
  rw [compileInstr_CNOT, circuitMatrix_mapWires]
  let σ : Basis 4 → Basis 4 := fun u => Function.update u 2 (xor (u 2) (u 1))
  have hcnot : cnotAction = σ := by
    funext u i
    fin_cases i <;> simp [cnotAction, σ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  have hcol : ∀ z, circuitMatrix controlledNot z (x ∘ cnotPlacement e) =
      if z = σ (x ∘ cnotPlacement e) then 1 else 0 := by
    intro z
    rw [controlledNot_matrix]
    exact congrArg (fun u => if z = u then (1 : ℂ) else 0) (congrFun hcnot _)
  rw [placeMatrix_classical_column _ _ σ y x hcol, place_update]
  rfl

/-- On the globally clean scratch subspace, every translated instruction agrees with placing
its original G₂ matrix on the data wires. -/
theorem QMAPerfectCompleteness.Main.HTCompiler.compileInstr_lift_clean {n : ℕ} (i : Instr gatesG2 n) (y x : Basis (n+3)) (hx : IsClean x) :
    circuitMatrix (compileInstr i) y x = placeMatrix (dataEmbedding n) i.matrix y x := by
  rcases i with ⟨g,e⟩
  fin_cases g
  · change Fin 1 ↪ Fin n at e
    rw [compileInstr_X_action e y x hx, ← instr_mapWires_matrix]
    change _ = (⟨⟨0,by decide⟩,e.trans (dataEmbedding n)⟩ : Instr gatesG2 (n+3)).matrix y x
    rw [instr_X_action]
    rfl
  · change Fin 2 ↪ Fin n at e
    rw [compileInstr_CNOT_action, ← instr_mapWires_matrix]
    change _ = (⟨⟨1,by decide⟩,e.trans (dataEmbedding n)⟩ : Instr gatesG2 (n+3)).matrix y x
    rw [instr_CNOT_action]
    rfl
  · change Fin 3 ↪ Fin n at e
    rw [compileInstr_Toffoli]
    simp only [circuitMatrix, Matrix.one_mul]
    have heq : (tAt (e.trans (dataEmbedding n))).matrix =
        ((⟨⟨2,by decide⟩,e⟩ : Instr gatesG2 n).mapWires (dataEmbedding n)).matrix := rfl
    rw [heq, instr_mapWires_matrix]
  · change Fin 2 ↪ Fin n at e
    rw [compileInstr_HH]
    change circuitMatrix (hhAt (e.trans (dataEmbedding n))) y x = _
    rw [hhAt_matrix]
    have hlocal := CircuitProof.instr_eq_submatrix
      ((⟨⟨3,by decide⟩,e⟩ : Instr gatesG2 n).mapWires (dataEmbedding n))
    have hplaced := instr_mapWires_matrix (dataEmbedding n) (⟨⟨3,by decide⟩,e⟩ : Instr gatesG2 n)
    exact congrArg (fun M : Matrix (Basis (n+3)) (Basis (n+3)) ℂ => M y x)
      (hlocal.symm.trans hplaced)

theorem QMAPerfectCompleteness.Main.HTCompiler.compileInstr_intertwines {n : ℕ} (i : Instr gatesG2 n) :
    circuitMatrix (compileInstr i) * cleanEmbedding n = cleanEmbedding n * i.matrix := by
  ext y x
  rw [mul_cleanEmbedding, compileInstr_lift_clean i _ _ (basisZero_clean x),
    placeMatrix_basisZero, cleanEmbedding_mul]

/-- Whole-circuit simulation on the clean scratch subspace. It also proves the scratch is
restored after every source instruction, allowing the same three wires to be reused. -/
theorem QMAPerfectCompleteness.Main.HTCompiler.compileGates_intertwines {n : ℕ} (gs : List (Instr gatesG2 n)) :
    circuitMatrix (compileGates gs) * cleanEmbedding n = cleanEmbedding n * circuitMatrix gs := by
  induction gs with
  | nil => simp [compileGates, circuitMatrix]
  | cons i gs ih =>
    change circuitMatrix (compileInstr i ++ compileGates gs) * cleanEmbedding n = _
    rw [BlockProof.circuitMatrix_append, Matrix.mul_assoc, compileInstr_intertwines,
      ← Matrix.mul_assoc, ih, Matrix.mul_assoc]
    rfl





/-- All three globally shared work bits really are initialized to zero by the compiled verifier. -/
theorem QMAPerfectCompleteness.Main.HTCompiler.compiledBasis_initial (V : Verifier gatesG2) (p : V.Proof) :
    compiledBasis V ((compileVerifier V).initialState p) = basisZero (V.initialState p) := by
  funext w
  refine Fin.addCases (fun a => ?_) (fun j => ?_) w
  · simp only [basisZero, Fin.append_left]
    refine Fin.addCases (fun i => ?_) (fun j => ?_) a
    · change (Fin.append p (fun _ : Fin (V.ancillaQubits+3) => false))
        (Fin.castAdd (V.ancillaQubits+3) i) =
        (Fin.append p (fun _ : Fin V.ancillaQubits => false)) (Fin.castAdd V.ancillaQubits i)
      rw [Fin.append_left, Fin.append_left]
    · change (Fin.append p (fun _ : Fin (V.ancillaQubits+3) => false))
        (Fin.natAdd V.proofQubits (Fin.castAdd 3 j)) =
        (Fin.append p (fun _ : Fin V.ancillaQubits => false)) (Fin.natAdd V.proofQubits j)
      rw [Fin.append_right, Fin.append_right]
  · simp only [basisZero, Fin.append_right]
    change (Fin.append p (fun _ : Fin (V.ancillaQubits+3) => false))
      ⟨V.proofQubits + V.ancillaQubits + j.val, by have := j.isLt; omega⟩ = false
    have hi : (⟨V.proofQubits + V.ancillaQubits + j.val, by have := j.isLt; omega⟩ :
        Fin (V.proofQubits + (V.ancillaQubits+3))) =
        Fin.natAdd V.proofQubits (Fin.natAdd V.ancillaQubits j) := by
      apply Fin.ext
      simp [Nat.add_assoc]
    rw [hi, Fin.append_right]

lemma QMAPerfectCompleteness.Main.HTCompiler.mul_ancillaZero {G : GateSet} {ι : Type*} (V : Verifier G) (A : Matrix ι V.Wire ℂ)
    (y : ι) (p : V.Proof) : (A * V.ancillaZero) y p = A y (V.initialState p) := by
  simp [Matrix.mul_apply, Verifier.ancillaZero, mul_ite]

theorem QMAPerfectCompleteness.Main.HTCompiler.compileVerifier_ancillaZero (V : Verifier gatesG2) :
    (compileVerifier V).ancillaZero = (cleanEmbedding (V.proofQubits+V.ancillaQubits) * V.ancillaZero).submatrix
      (compiledBasis V) (Equiv.refl V.Proof) := by
  ext y p
  simp only [Matrix.submatrix_apply, Equiv.coe_refl, id_eq, mul_ancillaZero]
  change (if y = (compileVerifier V).initialState p then (1 : ℂ) else 0) =
    if compiledBasis V y = basisZero (V.initialState p) then 1 else 0
  rw [← compiledBasis_initial]
  simp only [(compiledBasis V).injective.eq_iff]

lemma QMAPerfectCompleteness.Main.HTCompiler.place_equiv_matrix {r n : ℕ} (e : Fin r ≃ Fin n) (A : Matrix (Basis r) (Basis r) ℂ) :
    placeMatrix e.toEmbedding A = A.submatrix (fun x => x ∘ e) (fun x => x ∘ e) := by
  ext y x
  rw [placeMatrix_apply]
  have hmask : ∀ w, (∀ a, e a ≠ w) → y w = x w := by
    intro w h
    exact False.elim (h (e.symm w) (e.apply_symm_apply w))
  change (if ∀ w, (∀ a, e a ≠ w) → y w = x w then A (y ∘ e) (x ∘ e) else 0) = A (y ∘ e) (x ∘ e)
  exact if_pos hmask

theorem QMAPerfectCompleteness.Main.HTCompiler.compileVerifier_unitary (V : Verifier gatesG2) :
    (compileVerifier V).unitary =
      (circuitMatrix (compileGates V.gates)).submatrix (compiledBasis V) (compiledBasis V) := by
  change circuitMatrix ((compileGates V.gates).map (Instr.mapWires (compiledWireEquiv V).toEmbedding)) = _
  rw [circuitMatrix_mapWires, place_equiv_matrix]
  rfl

/-- The compiled computation on initialized registers is the source computation followed by
embedding in the clean scratch subspace. -/
theorem QMAPerfectCompleteness.Main.HTCompiler.compileVerifier_initialized_unitary (V : Verifier gatesG2) :
    (compileVerifier V).unitary * (compileVerifier V).ancillaZero =
      (cleanEmbedding (V.proofQubits+V.ancillaQubits) * (V.unitary * V.ancillaZero)).submatrix
        (compiledBasis V) (Equiv.refl V.Proof) := by
  rw [compileVerifier_unitary, compileVerifier_ancillaZero, Matrix.submatrix_mul_equiv,
    ← Matrix.mul_assoc, compileGates_intertwines, Matrix.mul_assoc]
  rfl

lemma QMAPerfectCompleteness.Main.HTCompiler.placed_acceptProjector (V : Verifier gatesG2) :
    placeMatrix (dataEmbedding (V.proofQubits+V.ancillaQubits)) V.acceptProjector =
      Matrix.diagonal (fun x : Basis (V.proofQubits+V.ancillaQubits+3) =>
        if x (dataEmbedding _ V.output) then (1 : ℂ) else 0) := by
  unfold Verifier.acceptProjector
  rw [placeMatrix_diagonal]
  rfl

theorem QMAPerfectCompleteness.Main.HTCompiler.compileVerifier_acceptProjector (V : Verifier gatesG2) :
    (compileVerifier V).acceptProjector =
      (placeMatrix (dataEmbedding (V.proofQubits+V.ancillaQubits)) V.acceptProjector).submatrix
        (compiledBasis V) (compiledBasis V) := by
  rw [placed_acceptProjector]
  ext y x
  by_cases h : y = x
  · subst x
    simp only [Verifier.acceptProjector, Matrix.diagonal_apply_eq, Matrix.submatrix_apply]
    rfl
  · simp [Verifier.acceptProjector, Matrix.diagonal_apply,h,(compiledBasis V).injective.ne h]

lemma QMAPerfectCompleteness.Main.HTCompiler.acceptance_as_gram {G : GateSet} (V : Verifier G) :
    V.acceptanceOperator = (V.unitary * V.ancillaZero)ᴴ * V.acceptProjector * (V.unitary * V.ancillaZero) := by
  simp only [Verifier.acceptanceOperator, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Exact preservation of the source acceptance operator, including arbitrary mixed proofs. -/
theorem solution (V : Verifier gatesG2) :
    (compileVerifier V).acceptanceOperator = V.acceptanceOperator := by
  let K := cleanEmbedding (V.proofQubits+V.ancillaQubits)
  let P := placeMatrix (dataEmbedding (V.proofQubits+V.ancillaQubits)) V.acceptProjector
  have hcompress : Kᴴ * P * K = V.acceptProjector := by
    change (cleanEmbedding _)ᴴ * placeMatrix (dataEmbedding _) V.acceptProjector * cleanEmbedding _ = _
    rw [Matrix.mul_assoc, placeMatrix_intertwines, ← Matrix.mul_assoc,
      cleanEmbedding_isometry, Matrix.one_mul]
  rw [acceptance_as_gram, compileVerifier_initialized_unitary, compileVerifier_acceptProjector]
  simp only [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    Equiv.coe_refl, Matrix.submatrix_id_id]
  change (K * (V.unitary * V.ancillaZero))ᴴ * P * (K * (V.unitary * V.ancillaZero)) = _
  calc
    _ = (V.unitary * V.ancillaZero)ᴴ * (Kᴴ * P * K) * (V.unitary * V.ancillaZero) := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = V.acceptanceOperator := by rw [hcompress, ← acceptance_as_gram]
