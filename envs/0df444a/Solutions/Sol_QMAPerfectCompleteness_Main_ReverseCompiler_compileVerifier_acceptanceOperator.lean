-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.ReverseCompiler.compileVerifier_acceptanceOperator
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T17:01:18.861574+00:00
-- url     : https://prove2.me/submissions/efb1a361-ca0d-4d10-9884-b40737131d76

/- Generated from Solutions.ReverseCompiler by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Gates
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_GateCompilation
import Definitions.Def_QMAPerfectCompleteness_Proof_HPToffoli
import Definitions.Def_QMAPerfectCompleteness_Proof_HadamardToffoli
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_RealSimulation
import Definitions.Def_QMAPerfectCompleteness_Proof_ReverseCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

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















end QMAPerfectCompleteness.Main.HadamardToffoli

end

/- Inline helpers retained from Solutions.HPToffoli. -/
section


/-! Exact finite synthesis for the reverse inclusion, using only H and controlled P.
The phase identity i^((a xor b)c-ac-bc)=(-1)^(abc) supplies CCZ. -/
open Matrix
namespace QMAPerfectCompleteness.Main.HPToffoli
open ReversibleGadgets





lemma cpAt_diagonal {n : ℕ} (e : Fin 2 ↪ Fin n) :
    (cpAt e).matrix = Matrix.diagonal (fun x : Basis n => if x (e 0) && x (e 1) then Complex.I else 1) := by
  have hbase : (cpAt (Function.Embedding.refl (Fin 2))).matrix =
      Matrix.diagonal (fun x : Basis 2 => if x 0 && x 1 then Complex.I else 1) := by
    ext y x
    change (if ∀ w : Fin 2, (∀ a : Fin 2, a ≠ w) → y w = x w then
      controlledPhaseMatrix y x else 0) = _
    by_cases h : y = x
    · subst y; simp [controlledPhaseMatrix, Matrix.diagonal_apply]
    · simp [controlledPhaseMatrix, Matrix.diagonal_apply,h]
  have hi : cpAt e = Instr.mapWires e (cpAt (Function.Embedding.refl (Fin 2))) := rfl
  rw [hi, instr_mapWires_matrix, hbase, placeMatrix_diagonal]
  rfl



lemma hAt_one_apply (y x : Basis 2) : (hAt (1 : Fin 2)).matrix y x =
    if y 0 = x 0 then
      (if y 1 && x 1 then -((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else ((Real.sqrt 2 : ℝ) : ℂ)⁻¹)
    else 0 := by
  have hk : (∀ w : Fin 2, (∀ a : Fin 1, (1 : Fin 2) ≠ w) → y w = x w) ↔ y 0 = x 0 := by
    simp [Fin.forall_fin_succ]
  change (if ∀ w : Fin 2, (∀ a : Fin 1, (1 : Fin 2) ≠ w) → y w = x w then
    (if y 1 && x 1 then -((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) else 0) = _
  simp only [hk]

lemma cnot_matrix_expression : circuitMatrix cnot =
    (hAt (1 : Fin 2)).matrix * Matrix.diagonal (fun x : Basis 2 => if x 0 && x 1 then (-1 : ℂ) else 1) *
      (hAt (1 : Fin 2)).matrix := by
  have hs : (cpAt (Function.Embedding.refl (Fin 2))).matrix * (cpAt (Function.Embedding.refl (Fin 2))).matrix =
      Matrix.diagonal (fun x : Basis 2 => if x 0 && x 1 then (-1 : ℂ) else 1) := by
    rw [cpAt_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext x
    cases h : x 0 && x 1 <;> simp [h]
  simp only [cnot, circuitMatrix, Matrix.one_mul]
  simpa only [Matrix.mul_assoc] using congrArg (fun M => (hAt (1 : Fin 2)).matrix * M * (hAt (1 : Fin 2)).matrix) hs

private theorem sum_basis_two (f : Basis 2 → ℂ) :
    ∑ x, f x = ∑ a : Bool, ∑ b : Bool, f ![a,b] := by
  let e : Basis 2 ≃ Bool × Bool :=
    { toFun := fun x => (x 0,x 1)
      invFun := fun x => ![x.1,x.2]
      left_inv := by intro x; funext i; fin_cases i <;> rfl
      right_inv := by rintro ⟨a,b⟩; rfl }
  simpa [e, Fintype.sum_prod_type] using (Equiv.sum_comp e.symm f).symm

set_option maxHeartbeats 1000000 in
theorem cnot_matrix : circuitMatrix cnot = gateCNOT.matrix := by
  rw [cnot_matrix_expression]
  ext y x
  change (∑ z : Basis 2, ((hAt (1 : Fin 2)).matrix *
    Matrix.diagonal (fun z : Basis 2 => if z 0 && z 1 then (-1 : ℂ) else 1)) y z *
      (hAt (1 : Fin 2)).matrix z x) = if y = ![x 0,xor (x 1) (x 0)] then 1 else 0
  simp_rw [Matrix.mul_diagonal, hAt_one_apply]
  rw [sum_basis_two]
  have hs : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have hy : y = ![y 0,y 1] := by funext i; fin_cases i <;> rfl
  have hx : x = ![x 0,x 1] := by funext i; fin_cases i <;> rfl
  rw [hy,hx]
  cases h0 : y 0 <;> cases h1 : y 1 <;> cases h2 : x 0 <;> cases h3 : x 1 <;>
    norm_num [gateCNOT, classicalMatrix, Fintype.sum_bool,h0,h1,h2,h3,hs,mul_assoc,
      funext_iff, Fin.forall_fin_succ]






lemma xor01_involutive : Function.Involutive xor01 := by
  intro x; funext i; fin_cases i <;> simp [xor01, Matrix.cons_val_two]

@[simp] theorem pair_zero (a b : Fin 3) (h : a ≠ b) : pair a b h 0 = a := rfl
@[simp] theorem pair_one (a b : Fin 3) (h : a ≠ b) : pair a b h 1 = b := rfl

lemma cnot01_matrix : circuitMatrix cnot01 = classicalMatrix xor01 := by
  rw [cnot01,circuitMatrix_mapWires,cnot_matrix]
  have hi : placeMatrix (pair 0 1 (by decide)) (gateCNOT.matrix : Matrix (Basis 2) (Basis 2) ℂ) =
      (cnotAt (pair 0 1 (by decide))).matrix := by
    have hb : (cnotAt (Function.Embedding.refl (Fin 2))).matrix = gateCNOT.matrix := by
      ext y x
      change (if ∀ w : Fin 2, (∀ a : Fin 2, a ≠ w) → y w = x w then
        (if y = ![x 0,xor (x 1) (x 0)] then (1 : ℂ) else 0) else 0) = _
      simp
      rfl
    rw [← hb, ← instr_mapWires_matrix]
    rfl
  rw [hi,instr_classical (cnotAt (pair 0 1 (by decide))) _ rfl]
  have hs : (fun u : Basis 2 => ![u 0,xor (u 1) (u 0)]) =
      (fun u : Basis 2 => Function.update u 1 (xor (u 1) (u 0))) := by
    funext u i; fin_cases i <;> simp
  change classicalMatrix (placePermutation (pair 0 1 (by decide))
    (fun u => ![u 0,xor (u 1) (u 0)])) = _
  rw [hs]
  congr 1
  funext x
  rw [place_update]
  funext i
  fin_cases i <;> simp [xor01, Matrix.cons_val_two]



lemma cpAt_cube {n : ℕ} (e : Fin 2 ↪ Fin n) :
    circuitMatrix (List.replicate 3 (cpAt e)) =
      Matrix.diagonal (fun x : Basis n => if x (e 0) && x (e 1) then -Complex.I else 1) := by
  simp only [List.replicate_succ, List.replicate_zero, circuitMatrix, Matrix.one_mul,
    cpAt_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  cases h : x (e 0) && x (e 1) <;> simp [h]

theorem ccZ_matrix : circuitMatrix ccZ =
    Matrix.diagonal (fun x : Basis 3 => if x 0 && x 1 && x 2 then (-1 : ℂ) else 1) := by
  simp only [ccZ,BlockProof.circuitMatrix_append,circuitMatrix,Matrix.one_mul,
    cnot01_matrix, cpAt_diagonal, cpAt_cube]
  have hc := HadamardToffoli.classical_diagonal_conjugate xor01 xor01_involutive
    (fun x : Basis 3 => if x ((pair 1 2 (by decide)) 0) && x ((pair 1 2 (by decide)) 1) then Complex.I else 1)
  simp only [← Matrix.mul_assoc]
  rw [hc]
  simp only [Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    simp [xor01,Function.comp_def,h0,h1,h2,Matrix.cons_val_two]





lemma hAt_two_apply (y x : Basis 3) : (hAt (2 : Fin 3)).matrix y x =
    if y 0 = x 0 ∧ y 1 = x 1 then
      (if y 2 && x 2 then -((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else ((Real.sqrt 2 : ℝ) : ℂ)⁻¹)
    else 0 := by
  have hk : (∀ w : Fin 3, (∀ a : Fin 1, (2 : Fin 3) ≠ w) → y w = x w) ↔
      y 0 = x 0 ∧ y 1 = x 1 := by simp [Fin.forall_fin_succ]
  change (if ∀ w : Fin 3, (∀ a : Fin 1, (2 : Fin 3) ≠ w) → y w = x w then
    (if y 2 && x 2 then -((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) else 0) = _
  simp only [hk]

private theorem sum_basis_three (f : Basis 3 → ℂ) :
    ∑ z, f z = ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, f ![a,b,c] := by
  let e : Basis 3 ≃ Bool × Bool × Bool :=
    { toFun := fun z => (z 0,z 1,z 2)
      invFun := fun z => ![z.1,z.2.1,z.2.2]
      left_inv := by intro z; funext i; fin_cases i <;> rfl
      right_inv := by rintro ⟨a,b,c⟩; rfl }
  simpa [e, Fintype.sum_prod_type] using (Equiv.sum_comp e.symm f).symm

set_option maxHeartbeats 1500000 in
theorem toffoli_matrix : circuitMatrix toffoli = gateToffoli.matrix := by
  have hexpr : circuitMatrix toffoli =
      (hAt (2 : Fin 3)).matrix *
        Matrix.diagonal (fun x : Basis 3 => if x 0 && x 1 && x 2 then (-1 : ℂ) else 1) *
          (hAt (2 : Fin 3)).matrix := by
    simp [toffoli,BlockProof.circuitMatrix_append,circuitMatrix,ccZ_matrix,Matrix.mul_assoc]
  rw [hexpr]
  ext y x
  change (∑ z : Basis 3, ((hAt (2 : Fin 3)).matrix *
    Matrix.diagonal (fun z : Basis 3 => if z 0 && z 1 && z 2 then (-1 : ℂ) else 1)) y z *
      (hAt (2 : Fin 3)).matrix z x) =
        if y = ![x 0,x 1,xor (x 2) (x 0 && x 1)] then 1 else 0
  simp_rw [Matrix.mul_diagonal,hAt_two_apply]
  rw [sum_basis_three]
  have hs : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have hy : y = ![y 0,y 1,y 2] := by funext i; fin_cases i <;> rfl
  have hx : x = ![x 0,x 1,x 2] := by funext i; fin_cases i <;> rfl
  rw [hy,hx]
  cases h0 : y 0 <;> cases h1 : y 1 <;> cases h2 : y 2 <;>
    cases h3 : x 0 <;> cases h4 : x 1 <;> cases h5 : x 2 <;>
    norm_num [Fintype.sum_bool,h0,h1,h2,h3,h4,h5,hs,mul_assoc,
      Matrix.cons_val_two, funext_iff, Fin.forall_fin_succ]

end QMAPerfectCompleteness.Main.HPToffoli

end



/-! Exact HT-to-HP compilation without additional wires. Each Toffoli is replaced by
its literal seventeen-gate H/controlled-P synthesis. -/
open Matrix
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.ReverseCompiler
end QMAPerfectCompleteness.Main.ReverseCompiler
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.ReverseCompiler
open HPToffoli ReversibleGadgets







lemma QMAPerfectCompleteness.Main.ReverseCompiler.compileInstr_H {n : ℕ} (e : Fin 1 ↪ Fin n) :
    compileInstr (⟨⟨0,by decide⟩,e⟩ : Instr gatesHT n) = [hAt (e 0)] := rfl


theorem QMAPerfectCompleteness.Main.ReverseCompiler.compileInstr_matrix {n : ℕ} (i : Instr gatesHT n) :
    circuitMatrix (compileInstr i) = i.matrix := by
  rcases i with ⟨g,e⟩
  fin_cases g
  · change Fin 1 ↪ Fin n at e
    rw [compileInstr_H]
    simp only [circuitMatrix,Matrix.one_mul]
    have he : (⟨fun _ : Fin 1 => e 0,by intro i j _; exact Subsingleton.elim i j⟩ : Fin 1 ↪ Fin n) = e := by
      ext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      rfl
    have he' : (hAt (e 0)).targets = e := he
    rw [CircuitProof.instr_eq_submatrix (hAt (e 0)),he']
    exact (CircuitProof.instr_eq_submatrix (⟨⟨0,by decide⟩,e⟩ : Instr gatesHT n)).symm
  · change Fin 3 ↪ Fin n at e
    rw [compileInstr_Toffoli,circuitMatrix_mapWires,toffoli_matrix]
    exact (CircuitProof.instr_eq_submatrix (⟨⟨1,by decide⟩,e⟩ : Instr gatesHT n)).symm

theorem QMAPerfectCompleteness.Main.ReverseCompiler.compileGates_matrix {n : ℕ} (gs : List (Instr gatesHT n)) :
    circuitMatrix (compileGates gs) = circuitMatrix gs := by
  induction gs with
  | nil => rfl
  | cons i gs ih =>
    change circuitMatrix (compileInstr i ++ compileGates gs) = _
    rw [BlockProof.circuitMatrix_append,ih,compileInstr_matrix]
    rfl

theorem QMAPerfectCompleteness.Main.ReverseCompiler.compileVerifier_unitary (V : Verifier gatesHT) :
    (compileVerifier V).unitary = V.unitary := compileGates_matrix V.gates

theorem solution (V : Verifier gatesHT) :
    (compileVerifier V).acceptanceOperator = V.acceptanceOperator := by
  simp only [Verifier.acceptanceOperator,compileVerifier_unitary]
  rfl
