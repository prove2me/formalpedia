-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.DyadicCompiler.compileVerifier_acceptanceOperator
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T16:55:30.268177+00:00
-- url     : https://prove2.me/submissions/22f9b330-4d7b-4680-a26c-427cb0cd55d2

/- Generated from Solutions.DyadicCompiler by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Gates
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_GateCompilation
import Definitions.Def_QMAPerfectCompleteness_Proof_RealSimulation
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

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



















































open scoped Kronecker



end QMAPerfectCompleteness.Main.RealSimulation

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





set_option maxHeartbeats 1000000 in
theorem controlledQuarterTurnQ_semantics :
    controlledQuarterTurnQ.map (Rat.cast : ℚ → ℂ) =
      (realControlledPhase ⊗ₖ (1 : Matrix Bool Bool ℂ)).submatrix splitFour splitFour := by
  ext y x
  have hy : y = ![y 0, y 1, y 2, y 3] := by funext i; fin_cases i <;> rfl
  have hx : x = ![x 0, x 1, x 2, x 3] := by funext i; fin_cases i <;> rfl
  rw [hy, hx]
  cases y 0 <;> cases y 1 <;> cases y 2 <;> cases y 3 <;>
    cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;>
    simp [controlledQuarterTurnQ, splitFour, realControlledPhase, RealSimulation.realRep,
      controlledPhaseMatrix, funext_iff, Fin.forall_fin_succ, Matrix.one_apply,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]

/-- A four-gate exact synthesis, with the workspace untouched on every state. -/
theorem realControlledPhaseCircuit_semantics :
    circuitMatrix realControlledPhaseCircuit =
      (realControlledPhase ⊗ₖ (1 : Matrix Bool Bool ℂ)).submatrix splitFour splitFour := by
  rw [realControlledPhaseCircuit_matrix, controlledQuarterTurnQ_semantics]



end QMAPerfectCompleteness.Main.GateCompilation

end



open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.DyadicCompiler
end QMAPerfectCompleteness.Main.DyadicCompiler
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.DyadicCompiler
open GateCompilation

































/-- The literal H replacement is the one-gate paired-H gadget on data and ignored wires. -/
theorem QMAPerfectCompleteness.Main.DyadicCompiler.compileInstr_H {n : ℕ} (e : Fin 1 ↪ Fin n) :
    compileInstr (⟨⟨0, by decide⟩, e⟩ : Instr gatesHP n) =
      [Instr.mapWires (hadamardPlacement (e 0)) pairedH] := by
  rfl

/-- The literal controlled-phase replacement is the verified four-gate gadget on c,a,b,d. -/
theorem QMAPerfectCompleteness.Main.DyadicCompiler.compileInstr_phase {n : ℕ} (e : Fin 2 ↪ Fin n) :
    compileInstr (⟨⟨1, by decide⟩, e⟩ : Instr gatesHP n) =
      realControlledPhaseCircuit.map (Instr.mapWires (phasePlacement e)) := by
  rfl



/-- Arbitrary-address H replacement, with its complete matrix semantics. -/
theorem QMAPerfectCompleteness.Main.DyadicCompiler.compileInstr_H_matrix {n : ℕ} (e : Fin 1 ↪ Fin n) :
    circuitMatrix (compileInstr (⟨⟨0, by decide⟩, e⟩ : Instr gatesHP n)) =
      ReversibleGadgets.placeMatrix (hadamardPlacement (e 0)) hadamardTwoMatrix := by
  rw [compileInstr_H]
  change circuitMatrix ([pairedH].map (Instr.mapWires (hadamardPlacement (e 0)))) = _
  rw [ReversibleGadgets.circuitMatrix_mapWires, pairedH_circuit]

/-- Arbitrary-address real controlled-phase replacement, with its complete matrix semantics. -/
theorem QMAPerfectCompleteness.Main.DyadicCompiler.compileInstr_phase_matrix {n : ℕ} (e : Fin 2 ↪ Fin n) :
    circuitMatrix (compileInstr (⟨⟨1, by decide⟩, e⟩ : Instr gatesHP n)) =
      ReversibleGadgets.placeMatrix (phasePlacement e)
        ((realControlledPhase ⊗ₖ (1 : Matrix Bool Bool ℂ)).submatrix splitFour splitFour) := by
  rw [compileInstr_phase, ReversibleGadgets.circuitMatrix_mapWires,
    realControlledPhaseCircuit_semantics]









lemma QMAPerfectCompleteness.Main.DyadicCompiler.complexRealRep_mul {ι κ τ : Type*} [Fintype κ]
    (A : Matrix ι κ ℂ) (B : Matrix κ τ ℂ) :
    complexRealRep (A * B) = complexRealRep A * complexRealRep B := by
  unfold complexRealRep
  rw [RealSimulation.realRep_mul]
  exact Matrix.map_mul (f := Complex.ofRealHom)

@[simp] lemma QMAPerfectCompleteness.Main.DyadicCompiler.complexRealRep_one {ι : Type*} [DecidableEq ι] :
    complexRealRep (1 : Matrix ι ι ℂ) = 1 := by
  simp [complexRealRep]



@[simp] theorem QMAPerfectCompleteness.Main.DyadicCompiler.simulationMatrix_one {n : ℕ} :
    simulationMatrix (1 : Matrix (Basis n) (Basis n) ℂ) (1 : Matrix Bool Bool ℂ) = 1 := by
  simp [simulationMatrix]

theorem QMAPerfectCompleteness.Main.DyadicCompiler.simulationMatrix_mul {n : ℕ} (A B : Matrix (Basis n) (Basis n) ℂ)
    (D E : Matrix Bool Bool ℂ) :
    simulationMatrix (A * B) (D * E) = simulationMatrix A D * simulationMatrix B E := by
  unfold simulationMatrix
  rw [Matrix.submatrix_mul_equiv _ _ (splitWires n) (splitWires n) (splitWires n),
    ← Matrix.mul_kronecker_mul, ← complexRealRep_mul]

theorem QMAPerfectCompleteness.Main.DyadicCompiler.dataWire_injective {n : ℕ} : Function.Injective (dataWire : Fin n → Fin (n + 2)) := by
  intro i j hij
  apply Fin.ext
  have := congrArg Fin.val hij
  dsimp [dataWire] at this
  omega

@[simp] theorem QMAPerfectCompleteness.Main.DyadicCompiler.hadamardPlacement_data {n : ℕ} (w : Fin n) :
    hadamardPlacement w 0 = dataWire w := rfl
@[simp] theorem QMAPerfectCompleteness.Main.DyadicCompiler.hadamardPlacement_ignored {n : ℕ} (w : Fin n) :
    hadamardPlacement w 1 = ignoredWire n := rfl
@[simp] theorem QMAPerfectCompleteness.Main.DyadicCompiler.phasePlacement_simulation {n : ℕ} (e : Fin 2 ↪ Fin n) :
    phasePlacement e 0 = simulationWire n := rfl
@[simp] theorem QMAPerfectCompleteness.Main.DyadicCompiler.phasePlacement_first {n : ℕ} (e : Fin 2 ↪ Fin n) :
    phasePlacement e 1 = dataWire (e 0) := rfl
@[simp] theorem QMAPerfectCompleteness.Main.DyadicCompiler.phasePlacement_second {n : ℕ} (e : Fin 2 ↪ Fin n) :
    phasePlacement e 2 = dataWire (e 1) := rfl
@[simp] theorem QMAPerfectCompleteness.Main.DyadicCompiler.phasePlacement_ignored {n : ℕ} (e : Fin 2 ↪ Fin n) :
    phasePlacement e 3 = ignoredWire n := rfl

/-- Every compiled wire is exactly c, one shifted original wire, or d. -/
theorem QMAPerfectCompleteness.Main.DyadicCompiler.wire_cases {n : ℕ} (w : Fin (n + 2)) :
    w = simulationWire n ∨ w = ignoredWire n ∨ ∃ v : Fin n, w = dataWire v := by
  by_cases hc : w.val = 0
  · exact Or.inl (Fin.ext hc)
  by_cases hd : w.val = n + 1
  · exact Or.inr (Or.inl (Fin.ext hd))
  refine Or.inr (Or.inr ⟨⟨w.val - 1, by have := w.isLt; omega⟩, ?_⟩)
  apply Fin.ext
  dsimp [dataWire]
  omega

/-- Untouched-wire conditions for replacing a single H by a pair of H gates. -/
theorem QMAPerfectCompleteness.Main.DyadicCompiler.hadamard_mask {n : ℕ} (w : Fin n) (y x : Basis (n + 2)) :
    (∀ v, (∀ a, hadamardPlacement w a ≠ v) → y v = x v) ↔
      y (simulationWire n) = x (simulationWire n) ∧
      ∀ v : Fin n, w ≠ v → y (dataWire v) = x (dataWire v) := by
  constructor
  · intro h
    constructor
    · apply h
      intro a
      fin_cases a <;> simp [hadamardPlacement, dataWire, ignoredWire, simulationWire, Fin.mk.injEq]
    · intro v hv
      apply h
      intro a
      fin_cases a
      · simpa using (fun heq => hv (dataWire_injective heq) : dataWire w ≠ dataWire v)
      · intro heq
        have hh := congrArg Fin.val heq
        have hvlt := v.isLt
        change n + 1 = v.val + 1 at hh
        omega
  · rintro ⟨hc, hd⟩ v hv
    rcases wire_cases v with rfl | rfl | ⟨a,rfl⟩
    · exact hc
    · exact False.elim (hv 1 (hadamardPlacement_ignored w))
    · apply hd
      intro heq
      exact hv 0 (by simpa [heq])

/-- Untouched-wire conditions for the c,a,b,d controlled-phase gadget. -/
theorem QMAPerfectCompleteness.Main.DyadicCompiler.phase_mask {n : ℕ} (e : Fin 2 ↪ Fin n) (y x : Basis (n + 2)) :
    (∀ v, (∀ a, phasePlacement e a ≠ v) → y v = x v) ↔
      ∀ v : Fin n, (∀ a, e a ≠ v) → y (dataWire v) = x (dataWire v) := by
  constructor
  · intro h v hv
    apply h
    intro a
    fin_cases a
    · intro heq
      have hh := congrArg Fin.val heq
      change (0 : ℕ) = v.val + 1 at hh
      omega
    · simpa using (fun heq => hv 0 (dataWire_injective heq) : dataWire (e 0) ≠ dataWire v)
    · simpa using (fun heq => hv 1 (dataWire_injective heq) : dataWire (e 1) ≠ dataWire v)
    · intro heq
      have hh := congrArg Fin.val heq
      have hvlt := v.isLt
      change n + 1 = v.val + 1 at hh
      omega
  · intro h v hv
    rcases wire_cases v with rfl | rfl | ⟨a,rfl⟩
    · exact False.elim (hv 0 (phasePlacement_simulation e))
    · exact False.elim (hv 3 (phasePlacement_ignored e))
    · apply h
      intro b hb
      fin_cases b
      · change e 0 = a at hb
        exact hv 1 (by rw [phasePlacement_first, hb])
      · change e 1 = a at hb
        exact hv 2 (by rw [phasePlacement_second, hb])



lemma QMAPerfectCompleteness.Main.DyadicCompiler.hh_factor (y x : Basis 2) : hadamardTwoMatrix y x =
    bitHadamard (y 0) (x 0) * bitHadamard (y 1) (x 1) := by
  have h := congrArg (fun M : Matrix (Basis 2) (Basis 2) ℂ => M y x) pairedH_semantics
  rw [pairedH_circuit] at h
  exact h

lemma QMAPerfectCompleteness.Main.DyadicCompiler.sourceH_apply {n : ℕ} (e : Fin 1 ↪ Fin n) (y x : Basis n) :
    (⟨⟨0,by decide⟩,e⟩ : Instr gatesHP n).matrix y x =
      if ∀ v : Fin n, e 0 ≠ v → y v = x v then bitHadamard (y (e 0)) (x (e 0)) else 0 := by
  change (if ∀ w : Fin n, (∀ a : Fin 1, e a ≠ w) → y w = x w then
    hadamardMatrix (y ∘ e) (x ∘ e) else 0) = _
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero, and_true]
  rfl

lemma QMAPerfectCompleteness.Main.DyadicCompiler.sourceH_real {n : ℕ} (e : Fin 1 ↪ Fin n) (y x : Basis n) :
    ((⟨⟨0,by decide⟩,e⟩ : Instr gatesHP n).matrix y x).im = 0 := by
  rw [sourceH_apply]
  simp only [bitHadamard, Matrix.of_apply]
  split_ifs <;> simp

lemma QMAPerfectCompleteness.Main.DyadicCompiler.complexRealRep_real_apply {ι κ : Type*} (A : Matrix ι κ ℂ)
    (hA : ∀ i j, (A i j).im = 0) (c d : Bool) (i : ι) (j : κ) :
    complexRealRep A (c,i) (d,j) = if c = d then A i j else 0 := by
  have hreal : ((A i j).re : ℂ) = A i j := by
    apply Complex.ext
    · rfl
    · simp [hA]
  cases c <;> cases d <;> simp [complexRealRep, RealSimulation.realRep, hA, hreal]

/-- Full-register H replacement is exactly the real-simulated source instruction tensored
with H on the ignored wire. -/
theorem QMAPerfectCompleteness.Main.DyadicCompiler.compileInstr_H_simulation {n : ℕ} (e : Fin 1 ↪ Fin n) :
    circuitMatrix (compileInstr (⟨⟨0,by decide⟩,e⟩ : Instr gatesHP n)) =
      simulationMatrix (⟨⟨0,by decide⟩,e⟩ : Instr gatesHP n).matrix bitHadamard := by
  rw [compileInstr_H_matrix]
  ext y x
  rw [ReversibleGadgets.placeMatrix_apply]
  change (if ∀ v, (∀ a, hadamardPlacement (e 0) a ≠ v) → y v = x v then
      hadamardTwoMatrix (y ∘ hadamardPlacement (e 0)) (x ∘ hadamardPlacement (e 0)) else 0) =
    complexRealRep (⟨⟨0,by decide⟩,e⟩ : Instr gatesHP n).matrix
      (y (simulationWire n), fun v => y (dataWire v))
      (x (simulationWire n), fun v => x (dataWire v)) *
      bitHadamard (y (ignoredWire n)) (x (ignoredWire n))
  rw [complexRealRep_real_apply _ (sourceH_real e), sourceH_apply]
  simp only [hadamard_mask, hh_factor, Function.comp_apply,
    hadamardPlacement_data, hadamardPlacement_ignored]
  split_ifs <;> simp_all

lemma QMAPerfectCompleteness.Main.DyadicCompiler.outside_and_target_eq {r n : ℕ} (e : Fin r ↪ Fin n) (y x : Basis n) :
    ((∀ v, (∀ a, e a ≠ v) → y v = x v) ∧ (∀ a, y (e a) = x (e a))) ↔ y = x := by
  constructor
  · rintro ⟨hout, he⟩
    apply (CircuitProof.splitTargets e).injective
    exact Prod.ext (funext he) ((CircuitProof.unaffected_iff e x y).mp hout)
  · intro h
    subst y
    simp

lemma QMAPerfectCompleteness.Main.DyadicCompiler.sourcePhase_apply {n : ℕ} (e : Fin 2 ↪ Fin n) (y x : Basis n) :
    (⟨⟨1,by decide⟩,e⟩ : Instr gatesHP n).matrix y x =
      if y = x then (if x (e 0) && x (e 1) then Complex.I else 1) else 0 := by
  have heq : (∀ a, y (e a) = x (e a)) ↔ y ∘ e = x ∘ e := by
    exact ⟨fun h => funext h, fun h a => congrFun h a⟩
  have hiff := outside_and_target_eq e y x
  rw [heq] at hiff
  change (if ∀ v, (∀ a, e a ≠ v) → y v = x v then
    (if y ∘ e = x ∘ e then (if x (e 0) && x (e 1) then Complex.I else 1) else 0) else 0) = _
  rw [← ite_and]
  simp only [hiff]

lemma QMAPerfectCompleteness.Main.DyadicCompiler.sourcePhase_diagonal {n : ℕ} (e : Fin 2 ↪ Fin n) :
    (⟨⟨1,by decide⟩,e⟩ : Instr gatesHP n).matrix =
      Matrix.diagonal (fun x : Basis n => if x (e 0) && x (e 1) then Complex.I else 1) := by
  ext y x
  rw [sourcePhase_apply]
  by_cases h : y = x <;> simp [Matrix.diagonal_apply, h]

lemma QMAPerfectCompleteness.Main.DyadicCompiler.complexRealRep_phase_diagonal {ι : Type*} [DecidableEq ι] (p : ι → Bool)
    (c d : Bool) (y x : ι) :
    complexRealRep (Matrix.diagonal (fun x => if p x then Complex.I else 1)) (c,y) (d,x) =
      if y = x ∧ c = xor d (p x) then (if d && p x then -1 else 1) else 0 := by
  by_cases h : y = x
  · subst y
    cases c <;> cases d <;> cases hx : p x <;>
      simp [complexRealRep, RealSimulation.realRep, Matrix.diagonal_apply, hx]
  · cases c <;> cases d <;>
      simp [complexRealRep, RealSimulation.realRep, Matrix.diagonal_apply, h]

lemma QMAPerfectCompleteness.Main.DyadicCompiler.ratCast_ite (P : Prop) [Decidable P] (a b : ℚ) :
    ((if P then a else b : ℚ) : ℂ) = if P then (a : ℂ) else (b : ℂ) := by
  split_ifs <;> rfl

lemma QMAPerfectCompleteness.Main.DyadicCompiler.ite_mul_indicator (P Q : Prop) [Decidable P] [Decidable Q] (a : ℂ) :
    (if P then a else 0) * (if Q then 1 else 0) = if P ∧ Q then a else 0 := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp,hq]

set_option backward.isDefEq.respectTransparency false in
/-- Full-register controlled-phase replacement, with identity on the ignored wire. -/
theorem QMAPerfectCompleteness.Main.DyadicCompiler.compileInstr_phase_simulation {n : ℕ} (e : Fin 2 ↪ Fin n) :
    circuitMatrix (compileInstr (⟨⟨1,by decide⟩,e⟩ : Instr gatesHP n)) =
      simulationMatrix (⟨⟨1,by decide⟩,e⟩ : Instr gatesHP n).matrix 1 := by
  rw [compileInstr_phase_matrix, ← controlledQuarterTurnQ_semantics]
  ext y x
  rw [ReversibleGadgets.placeMatrix_apply]
  change (if ∀ v, (∀ a, phasePlacement e a ≠ v) → y v = x v then
      ((controlledQuarterTurnQ (y ∘ phasePlacement e) (x ∘ phasePlacement e) : ℚ) : ℂ) else 0) =
    complexRealRep (⟨⟨1,by decide⟩,e⟩ : Instr gatesHP n).matrix
      (y (simulationWire n), fun v => y (dataWire v))
      (x (simulationWire n), fun v => x (dataWire v)) *
      (if y (ignoredWire n) = x (ignoredWire n) then 1 else 0)
  rw [sourcePhase_diagonal, complexRealRep_phase_diagonal]
  simp only [controlledQuarterTurnQ, Function.comp_apply, phasePlacement_simulation,
    phasePlacement_first, phasePlacement_second, phasePlacement_ignored, phase_mask]
  simp only [ratCast_ite, Rat.cast_neg, Rat.cast_one, Rat.cast_zero]
  rw [ite_mul_indicator]
  simp only [← ite_and, Bool.and_assoc]
  have hdata := outside_and_target_eq e (fun v => y (dataWire v)) (fun v => x (dataWire v))
  have hlocal : (∀ a : Fin 2, y (dataWire (e a)) = x (dataWire (e a))) ↔
      y (dataWire (e 0)) = x (dataWire (e 0)) ∧ y (dataWire (e 1)) = x (dataWire (e 1)) := by
    simp only [Fin.forall_fin_two]
  rw [hlocal] at hdata
  have hcond :
      ((∀ v : Fin n, (∀ a, e a ≠ v) → y (dataWire v) = x (dataWire v)) ∧
        (y (simulationWire n) = xor (x (simulationWire n)) (x (dataWire (e 0)) && x (dataWire (e 1))) ∧
          y (dataWire (e 0)) = x (dataWire (e 0)) ∧ y (dataWire (e 1)) = x (dataWire (e 1)) ∧
          y (ignoredWire n) = x (ignoredWire n))) ↔
      (((fun v => y (dataWire v)) = (fun v => x (dataWire v)) ∧
        y (simulationWire n) = xor (x (simulationWire n)) (x (dataWire (e 0)) && x (dataWire (e 1)))) ∧
          y (ignoredWire n) = x (ignoredWire n)) := by tauto
  simp only [hcond]

/-- Every source gate is represented exactly; only H rotates the ignored ancillary wire. -/
theorem QMAPerfectCompleteness.Main.DyadicCompiler.compileInstr_simulation {n : ℕ} (i : Instr gatesHP n) :
    circuitMatrix (compileInstr i) = simulationMatrix i.matrix
      (bitHadamard ^ (if i.gate.val = 0 then 1 else 0)) := by
  rcases i with ⟨g,e⟩
  fin_cases g
  · change Fin 1 ↪ Fin n at e
    simpa using compileInstr_H_simulation e
  · change Fin 2 ↪ Fin n at e
    simpa using compileInstr_phase_simulation e

/-- Exact gate-list real simulation, with the ignored wire accumulating one H per source H. -/
theorem QMAPerfectCompleteness.Main.DyadicCompiler.compileGates_simulation {n : ℕ} (gs : List (Instr gatesHP n)) :
    circuitMatrix (compileGates gs) = simulationMatrix (circuitMatrix gs)
      (bitHadamard ^ (gs.countP fun i => i.gate.val == 0)) := by
  induction gs with
  | nil => simp [compileGates, circuitMatrix]
  | cons i gs ih =>
    have hc : (i :: gs).countP (fun i => i.gate.val == 0) =
        gs.countP (fun i => i.gate.val == 0) + (if i.gate.val = 0 then 1 else 0) := by
      by_cases h : i.gate.val = 0 <;> simp [List.countP_cons, h]
    change circuitMatrix (compileInstr i ++ compileGates gs) = _
    rw [BlockProof.circuitMatrix_append, ih, compileInstr_simulation, ← simulationMatrix_mul,
      ← pow_add, hc]
    rfl





lemma QMAPerfectCompleteness.Main.DyadicCompiler.placeMatrix_of_equiv {r n : ℕ} (e : Fin r ≃ Fin n) (A : Matrix (Basis r) (Basis r) ℂ) :
    ReversibleGadgets.placeMatrix e.toEmbedding A = A.submatrix (fun x => x ∘ e) (fun x => x ∘ e) := by
  ext y x
  rw [ReversibleGadgets.placeMatrix_apply]
  have hmask : ∀ w, (∀ a, e a ≠ w) → y w = x w := by
    intro w h
    exact False.elim (h (e.symm w) (e.apply_symm_apply w))
  change (if ∀ w, (∀ a, e a ≠ w) → y w = x w then A (y ∘ e) (x ∘ e) else 0) = A (y ∘ e) (x ∘ e)
  exact if_pos hmask

/-- Complete unitary semantics of the compiled verifier. Register casts only reconcile the
paper's `(m+1)+(a+1)` sizes with the gate compiler's `m+a+2` layout. -/
theorem QMAPerfectCompleteness.Main.DyadicCompiler.compileVerifier_unitary (V : Verifier gatesHP) :
    (compileVerifier V).unitary =
      (simulationMatrix V.unitary (bitHadamard ^ (V.gates.countP fun i => i.gate.val == 0))).submatrix
        (compiledBasis V) (compiledBasis V) := by
  change circuitMatrix ((compileGates V.gates).map
    (Instr.mapWires (compiledWireEquiv V).toEmbedding)) = _
  rw [ReversibleGadgets.circuitMatrix_mapWires, compileGates_simulation, placeMatrix_of_equiv]
  rfl





/-- The compiler's initialized registers have c in the proof and d initialized to zero. -/
theorem QMAPerfectCompleteness.Main.DyadicCompiler.wireLayout_initial (V : Verifier gatesHP) (p : Basis (V.proofQubits + 1)) :
    wireLayout V ((compileVerifier V).initialState p) =
      ((p 0, V.initialState (Fin.tail p)), false) := by
  apply Prod.ext
  · apply Prod.ext
    · change (Fin.append p (fun _ : Fin (V.ancillaQubits + 1) => false))
        (Fin.castAdd (V.ancillaQubits + 1) (0 : Fin (V.proofQubits + 1))) = p 0
      rw [Fin.append_left]
    · funext w
      refine Fin.addCases (fun j => ?_) (fun j => ?_) w
      · change (Fin.append p (fun _ : Fin (V.ancillaQubits + 1) => false))
          (Fin.castAdd (V.ancillaQubits + 1) j.succ) =
          (Fin.append (Fin.tail p) (fun _ : Fin V.ancillaQubits => false))
            (Fin.castAdd V.ancillaQubits j)
        simp [Fin.append_left, Fin.tail]
      · change (Fin.append p (fun _ : Fin (V.ancillaQubits + 1) => false))
          ⟨V.proofQubits + j.val + 1, by have := j.isLt; omega⟩ =
          (Fin.append (Fin.tail p) (fun _ : Fin V.ancillaQubits => false))
            (Fin.natAdd V.proofQubits j)
        have hi : (⟨V.proofQubits + j.val + 1, by have := j.isLt; omega⟩ :
            Fin ((V.proofQubits + 1) + (V.ancillaQubits + 1))) =
            Fin.natAdd (V.proofQubits + 1) j.castSucc := by apply Fin.ext; simp; omega
        rw [hi, Fin.append_right, Fin.append_right]
  · change (Fin.append p (fun _ : Fin (V.ancillaQubits + 1) => false))
      ⟨V.proofQubits + V.ancillaQubits + 1, by omega⟩ = false
    have hi : (⟨V.proofQubits + V.ancillaQubits + 1, by omega⟩ :
        Fin ((V.proofQubits + 1) + (V.ancillaQubits + 1))) =
        Fin.natAdd (V.proofQubits + 1) (Fin.last V.ancillaQubits) := by
      apply Fin.ext
      simp
      omega
    rw [hi, Fin.append_right]



lemma QMAPerfectCompleteness.Main.DyadicCompiler.ancillaZero_real (V : Verifier gatesHP) (y : V.Wire) (p : V.Proof) :
    (V.ancillaZero y p).im = 0 := by
  simp only [Verifier.ancillaZero, Matrix.of_apply]
  split_ifs <;> simp

/-- The compiler's initialization is exactly the real-simulated source initialization tensored
with the ignored zero qubit. -/
theorem QMAPerfectCompleteness.Main.DyadicCompiler.compileVerifier_ancillaZero (V : Verifier gatesHP) :
    (compileVerifier V).ancillaZero =
      (complexRealRep V.ancillaZero ⊗ₖ ignoredZero).submatrix (wireLayout V)
        (proofLayout V.proofQubits) := by
  ext y p
  change Basis (V.proofQubits + 1) at p
  have hiff : y = (compileVerifier V).initialState p ↔
      (wireLayout V y).1.1 = p 0 ∧
      (wireLayout V y).1.2 = V.initialState (Fin.tail p) ∧ (wireLayout V y).2 = false := by
    rw [← (wireLayout V).apply_eq_iff_eq, wireLayout_initial]
    simp only [Prod.ext_iff, and_assoc]
  change (if y = (compileVerifier V).initialState p then (1 : ℂ) else 0) =
    complexRealRep V.ancillaZero ((wireLayout V y).1.1, (wireLayout V y).1.2) (p 0, Fin.tail p) *
      (if (wireLayout V y).2 = false then 1 else 0)
  rw [complexRealRep_real_apply _ (ancillaZero_real V)]
  simp only [Verifier.ancillaZero, Matrix.of_apply]
  by_cases hc : (wireLayout V y).1.1 = p 0 <;>
    by_cases hw : (wireLayout V y).1.2 = V.initialState (Fin.tail p) <;>
    by_cases hd : (wireLayout V y).2 = false <;> simp [hiff,hc,hw,hd]

lemma QMAPerfectCompleteness.Main.DyadicCompiler.complexRealRep_conjTranspose {ι κ : Type*} (A : Matrix ι κ ℂ) :
    complexRealRep Aᴴ = (complexRealRep A)ᴴ := by
  unfold complexRealRep
  rw [RealSimulation.realRep_conjTranspose]
  ext y x
  simp [Matrix.conjTranspose_apply]

lemma QMAPerfectCompleteness.Main.DyadicCompiler.complexRealRep_diagonal_real {ι : Type*} [DecidableEq ι] (f : ι → ℂ)
    (hf : ∀ i, (f i).im = 0) :
    complexRealRep (Matrix.diagonal f) = Matrix.diagonal (fun p : Bool × ι => f p.2) := by
  have hdiag : ∀ i j, ((Matrix.diagonal f) i j).im = 0 := by
    intro i j
    by_cases h : i = j <;> simp [Matrix.diagonal_apply,h,hf]
  ext ⟨c,y⟩ ⟨d,x⟩
  rw [complexRealRep_real_apply _ hdiag]
  by_cases hc : c = d <;> by_cases hx : y = x <;> simp [Matrix.diagonal_apply,hc,hx]

lemma QMAPerfectCompleteness.Main.DyadicCompiler.diagonal_kronecker_identity {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (f : ι → ℂ) :
    Matrix.diagonal f ⊗ₖ (1 : Matrix κ κ ℂ) = Matrix.diagonal (fun p : ι × κ => f p.1) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  by_cases hi : i = j <;> by_cases ha : a = b <;>
    simp [Matrix.kronecker_apply, Matrix.diagonal_apply, Matrix.one_apply, hi,ha]

/-- The output measurement ignores c and d and measures the same original output wire. -/
theorem QMAPerfectCompleteness.Main.DyadicCompiler.compileVerifier_acceptProjector (V : Verifier gatesHP) :
    (compileVerifier V).acceptProjector =
      (complexRealRep V.acceptProjector ⊗ₖ (1 : Matrix Bool Bool ℂ)).submatrix
        (wireLayout V) (wireLayout V) := by
  have hreal : ∀ w : V.Wire, (if w V.output then (1 : ℂ) else 0).im = 0 := by
    intro w; split_ifs <;> simp
  rw [show V.acceptProjector = Matrix.diagonal (fun w : V.Wire => if w V.output then 1 else 0) from rfl,
    complexRealRep_diagonal_real _ hreal, diagonal_kronecker_identity]
  ext y x
  by_cases h : y = x
  · subst x
    simp only [Verifier.acceptProjector, Matrix.diagonal_apply_eq, Matrix.submatrix_apply]
    rfl
  · simp [Verifier.acceptProjector, Matrix.diagonal_apply,h,(wireLayout V).injective.ne h]



theorem QMAPerfectCompleteness.Main.DyadicCompiler.bitHadamard_unitary : bitHadamard ∈ Matrix.unitaryGroup Bool ℂ := by
  have heq : bitHadamard = hadamardMatrix.submatrix singletonBit singletonBit := rfl
  rw [heq]
  exact CircuitProof.submatrix_unitary singletonBit _ hadamardMatrix_mem_unitaryGroup

lemma QMAPerfectCompleteness.Main.DyadicCompiler.ignoredZero_gram : ignoredZeroᴴ * ignoredZero = (1 : Matrix Unit Unit ℂ) := by
  ext i j
  cases i
  cases j
  simp [ignoredZero, Matrix.mul_apply, Matrix.conjTranspose_apply]

lemma QMAPerfectCompleteness.Main.DyadicCompiler.compileVerifier_unitary_layout (V : Verifier gatesHP) :
    (compileVerifier V).unitary =
      (complexRealRep V.unitary ⊗ₖ (bitHadamard ^ (V.gates.countP fun i => i.gate.val == 0))).submatrix
        (wireLayout V) (wireLayout V) := by
  rw [compileVerifier_unitary]
  rfl



/-- The acceptance operator is exactly R(E) on the new proof register. The extra d wire is
initialized to zero and ignored; its accumulated Hadamards cancel from the acceptance effect. -/
theorem solution (V : Verifier gatesHP) :
    (compileVerifier V).acceptanceOperator =
      (complexRealRep V.acceptanceOperator).submatrix (splitProof V.proofQubits) (splitProof V.proofQubits) := by
  let D := bitHadamard ^ (V.gates.countP fun i => i.gate.val == 0)
  have hD : Dᴴ * D = 1 := Matrix.mem_unitaryGroup_iff'.mp
    (pow_mem bitHadamard_unitary _)
  have haux : ignoredZeroᴴ * Dᴴ * (1 : Matrix Bool Bool ℂ) * D * ignoredZero = 1 := by
    rw [Matrix.mul_one]
    calc
      _ = ignoredZeroᴴ * (Dᴴ * D) * ignoredZero := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hD, Matrix.mul_one, ignoredZero_gram]
  have hmain : complexRealRep V.acceptanceOperator =
      (complexRealRep V.ancillaZero)ᴴ * (complexRealRep V.unitary)ᴴ *
        complexRealRep V.acceptProjector * complexRealRep V.unitary * complexRealRep V.ancillaZero := by
    simp only [Verifier.acceptanceOperator, complexRealRep_mul, complexRealRep_conjTranspose]
  have hcompressed : (compileVerifier V).acceptanceOperator =
      (complexRealRep V.acceptanceOperator ⊗ₖ (1 : Matrix Unit Unit ℂ)).submatrix
        (proofLayout V.proofQubits) (proofLayout V.proofQubits) := by
    change (compileVerifier V).ancillaZeroᴴ * (compileVerifier V).unitaryᴴ *
      (compileVerifier V).acceptProjector * (compileVerifier V).unitary *
      (compileVerifier V).ancillaZero = _
    rw [compileVerifier_ancillaZero, compileVerifier_unitary_layout, compileVerifier_acceptProjector]
    change ((complexRealRep V.ancillaZero ⊗ₖ ignoredZero).submatrix
      (wireLayout V) (proofLayout V.proofQubits))ᴴ *
      ((complexRealRep V.unitary ⊗ₖ D).submatrix (wireLayout V) (wireLayout V))ᴴ *
      ((complexRealRep V.acceptProjector ⊗ₖ (1 : Matrix Bool Bool ℂ)).submatrix (wireLayout V) (wireLayout V)) *
      ((complexRealRep V.unitary ⊗ₖ D).submatrix (wireLayout V) (wireLayout V)) *
      ((complexRealRep V.ancillaZero ⊗ₖ ignoredZero).submatrix (wireLayout V) (proofLayout V.proofQubits)) = _
    simp only [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_kronecker,
      Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul]
    rw [← hmain, haux]
  rw [hcompressed]
  ext p q
  simp [Matrix.submatrix_apply, proofLayout, splitProof]
