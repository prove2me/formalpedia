-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P10.localUnitaryInvariant
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T18:40:52.96281+00:00
-- url     : https://prove2.me/submissions/84a9a964-85b4-45dd-b7ed-90a3b8d01586

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P10
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P10_geometricMinimum
namespace QAlgorithms.Papers.Independent.Information100.P10
open scoped ComplexConjugate Matrix

lemma G_kron_mul {M : ℕ} (f g : Fin M → Matrix Bool Bool ℂ) :
    kronAll f * kronAll g = kronAll (fun j => f j * g j) := by
  ext y z
  simp only [kronAll, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.prod_mul_distrib]

lemma G_kron_one {M : ℕ} : kronAll (fun _ : Fin M => (1 : Matrix Bool Bool ℂ)) = 1 := by
  ext y z
  simp only [kronAll, Matrix.of_apply, Matrix.one_apply]
  by_cases h : y = z
  · subst h; simp
  · have : ∃ j, y j ≠ z j := by
      by_contra hc; push_neg at hc; exact h (funext hc)
    obtain ⟨j, hj⟩ := this
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

lemma G_kron_conjT {M : ℕ} (f : Fin M → Matrix Bool Bool ℂ) :
    (kronAll f)ᴴ = kronAll (fun j => (f j)ᴴ) := by
  ext y z
  simp [kronAll, Matrix.conjTranspose_apply]

def LQ {M : ℕ} (q : Fin M) (A : Matrix Bool Bool ℂ) : Matrix (Qubits M) (Qubits M) ℂ :=
  kronAll (fun j => if j = q then A else 1)

lemma LQ_apply {M : ℕ} (q : Fin M) (A : Matrix Bool Bool ℂ) (y z : Qubits M) :
    LQ q A y z = A (y q) (z q) * ∏ j ∈ Finset.univ.erase q, (1 : Matrix Bool Bool ℂ) (y j) (z j) := by
  unfold LQ kronAll
  rw [Matrix.of_apply, ← Finset.mul_prod_erase _ _ (Finset.mem_univ q)]
  simp only [if_true]
  congr 1
  refine Finset.prod_congr rfl (fun j hj => ?_)
  rw [if_neg (Finset.ne_of_mem_erase hj)]

lemma LQ_add {M : ℕ} (q : Fin M) (A B : Matrix Bool Bool ℂ) : LQ q (A + B) = LQ q A + LQ q B := by
  ext y z; simp only [LQ_apply, Matrix.add_apply]; ring
lemma LQ_smul {M : ℕ} (q : Fin M) (c : ℂ) (A : Matrix Bool Bool ℂ) : LQ q (c • A) = c • LQ q A := by
  ext y z; simp only [LQ_apply, Matrix.smul_apply, smul_eq_mul]; ring
lemma LQ_sum {M : ℕ} (q : Fin M) (c : Fin 3 → ℂ) (A : Fin 3 → Matrix Bool Bool ℂ) :
    LQ q (∑ a, c a • A a) = ∑ a, c a • LQ q (A a) := by
  simp only [Fin.sum_univ_three, LQ_add, LQ_smul]
lemma LQ_mul {M : ℕ} (q : Fin M) (A B : Matrix Bool Bool ℂ) : LQ q A * LQ q B = LQ q (A * B) := by
  unfold LQ; rw [G_kron_mul]; congr 1; funext j; split_ifs <;> simp
lemma LQ_one {M : ℕ} (q : Fin M) : LQ q 1 = 1 := by
  unfold LQ; rw [← G_kron_one]; congr 1; funext j; split_ifs <;> rfl
lemma LQ_conjT {M : ℕ} (q : Fin M) (A : Matrix Bool Bool ℂ) : (LQ q A)ᴴ = LQ q Aᴴ := by
  unfold LQ; rw [G_kron_conjT]; congr 1; funext j; split_ifs <;> simp

lemma pauli_herm (a : Fin 3) : (pauli a)ᴴ = pauli a := by
  ext x y
  fin_cases a <;> cases x <;> cases y <;> simp [pauli, pauliX, pauliY, pauliZ, Matrix.conjTranspose_apply]

lemma pauli_sq (v : Fin 3 → ℝ) :
    (∑ a, (v a : ℂ) • pauli a) * (∑ a, (v a : ℂ) • pauli a) = ((∑ a, v a ^ 2 : ℝ) : ℂ) • 1 := by
  ext x y
  simp only [Fin.sum_univ_three, Matrix.mul_apply, Fintype.sum_bool, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.one_apply]
  cases x <;> cases y <;> simp [pauli, pauliX, pauliY, pauliZ] <;> ring_nf <;> simp [Complex.ext_iff] <;> ring


lemma G_act_mul {M : ℕ} (A B : Matrix (Qubits M) (Qubits M) ℂ) (x : Ket M) :
    act (A * B) x = act A (act B x) := by simp [act, Matrix.mulVec_mulVec]

lemma G_inner_act {M : ℕ} (A : Matrix (Qubits M) (Qubits M) ℂ) (x y : Ket M) :
    inner ℂ (act A x) y = inner ℂ x (act Aᴴ y) := by
  simp only [act, PiLp.inner_apply, RCLike.inner_apply, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
    map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  simp only [RCLike.star_def, PiLp.toLp_apply]
  ring

lemma G_dir_eq {M : ℕ} (q : Fin M) (u : Direction) :
    directionalPauli q u = LQ q (∑ a, ((u a : ℝ) : ℂ) • pauli a) := by
  rw [LQ_sum]; rfl

lemma G_dir_herm {M : ℕ} (q : Fin M) (u : Direction) : (directionalPauli q u)ᴴ = directionalPauli q u := by
  rw [G_dir_eq, LQ_conjT]
  congr 1
  simp [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, pauli_herm]

lemma G_real {M : ℕ} (A : Matrix (Qubits M) (Qubits M) ℂ) (hA : Aᴴ = A) (x : Ket M) :
    inner ℂ x (act A x) = ((inner ℂ x (act A x)).re : ℂ) := by
  have h : conj (inner ℂ x (act A x)) = inner ℂ x (act A x) := by
    rw [inner_conj_symm, G_inner_act, hA]
  exact (Complex.conj_eq_iff_re.1 h).symm

lemma G_dir_exp {M : ℕ} (psi : Ket M) (q : Fin M) (u : Direction) :
    inner ℂ psi (act (directionalPauli q u) psi) = ((inner ℝ u (bloch psi q) : ℝ) : ℂ) := by
  rw [G_real _ (G_dir_herm q u)]
  congr 1
  simp only [directionalPauli, bloch, PiLp.inner_apply, real_inner_eq_re_inner, act, Matrix.sum_mulVec,
    Matrix.smul_mulVec, WithLp.toLp_sum, WithLp.toLp_smul, inner_sum, inner_smul_right, Complex.re_sum,
    PiLp.toLp_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp [Complex.mul_re, mul_comm, Finset.mul_sum]

lemma G_dir_sq {M : ℕ} (q : Fin M) (u : Direction) (hu : ‖u‖ = 1) :
    directionalPauli q u * directionalPauli q u = 1 := by
  rw [G_dir_eq, LQ_mul, pauli_sq]
  have : ∑ a, u a ^ 2 = 1 := by
    have h := EuclideanSpace.norm_sq_eq u
    rw [hu] at h
    simpa [Real.norm_eq_abs, sq_abs] using h.symm
  rw [this, Complex.ofReal_one, one_smul, LQ_one]


lemma G_metric {M : ℕ} (psi : Ket M) (v : Fin M → Direction) (q r : Fin M) :
    orbitMetric psi v q r =
      inner ℂ psi (act (directionalPauli q (v q) * directionalPauli r (v r)) psi) -
      inner ℂ psi (act (directionalPauli q (v q)) psi) *
        inner ℂ psi (act (directionalPauli r (v r)) psi) := by
  unfold orbitMetric fsForm orbitTangent
  simp only [inner_smul_left, inner_smul_right, G_inner_act, G_dir_herm, G_act_mul]
  simp only [Complex.conj_neg_I]
  linear_combination (inner ℂ psi (act (directionalPauli q (v q)) psi) * inner ℂ psi (act (directionalPauli r (v r)) psi) -
    inner ℂ psi (act (directionalPauli q (v q)) (act (directionalPauli r (v r)) psi))) * Complex.I_sq


/-- reduced one-wire matrix -/
noncomputable def RQ {M : ℕ} (psi : Ket M) (q : Fin M) : Matrix Bool Bool ℂ :=
  Matrix.of fun y x => inner ℂ psi (act (LQ q (Matrix.single x y 1)) psi)

lemma act_addM {M : ℕ} (A B : Matrix (Qubits M) (Qubits M) ℂ) (x : Ket M) : act (A + B) x = act A x + act B x := by
  simp [act, Matrix.add_mulVec]
lemma act_smulM {M : ℕ} (c : ℂ) (A : Matrix (Qubits M) (Qubits M) ℂ) (x : Ket M) : act (c • A) x = c • act A x := by
  simp [act, Matrix.smul_mulVec]

lemma RQ_exp {M : ℕ} (psi : Ket M) (q : Fin M) (A : Matrix Bool Bool ℂ) :
    inner ℂ psi (act (LQ q A) psi) = (A * RQ psi q).trace := by
  have hA : A = ∑ x : Bool, ∑ y : Bool, A x y • Matrix.single x y (1 : ℂ) := by
    ext i j; cases i <;> cases j <;> simp [Fintype.sum_bool, Matrix.single_apply]
  conv_lhs => rw [hA]
  simp only [Fintype.sum_bool, LQ_add, LQ_smul, act_addM, act_smulM, inner_add_right, inner_smul_right]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_bool, RQ, Matrix.of_apply]


lemma K_conj {M : ℕ} (U : Fin M → Matrix Bool Bool ℂ) (hU : ∀ j, star (U j) * U j = 1) (q : Fin M)
    (A : Matrix Bool Bool ℂ) :
    (kronAll U)ᴴ * LQ q A * kronAll U = LQ q ((U q)ᴴ * A * U q) := by
  unfold LQ
  rw [G_kron_conjT, G_kron_mul, G_kron_mul]
  congr 1; funext j
  split_ifs with h
  · subst h; rfl
  · rw [Matrix.mul_one, ← Matrix.star_eq_conjTranspose, hU j]

lemma K_unit {M : ℕ} (U : Fin M → Matrix Bool Bool ℂ) (hU : ∀ j, star (U j) * U j = 1) :
    (kronAll U)ᴴ * kronAll U = 1 := by
  rw [G_kron_conjT, G_kron_mul]
  have : (fun j => (U j)ᴴ * U j) = fun _ => (1 : Matrix Bool Bool ℂ) := by
    funext j; rw [← Matrix.star_eq_conjTranspose, hU j]
  rw [this, G_kron_one]

lemma phase_unit (α : ℝ) : conj (Complex.exp (Complex.I * (α : ℂ))) * Complex.exp (Complex.I * (α : ℂ)) = 1 := by
  rw [Complex.conj_mul', show Complex.I * (α : ℂ) = (α : ℂ) * Complex.I by ring, Complex.norm_exp_ofReal_mul_I]
  simp

lemma I_act_smul {M : ℕ} (A : Matrix (Qubits M) (Qubits M) ℂ) (c : ℂ) (x : Ket M) :
    act A (c • x) = c • act A x := by simp [act, Matrix.mulVec_smul]

lemma inner_phi {M : ℕ} (U : Fin M → Matrix Bool Bool ℂ) (α : ℝ) (psi : Ket M)
    (B : Matrix (Qubits M) (Qubits M) ℂ) :
    inner ℂ (Complex.exp (Complex.I * (α : ℂ)) • act (kronAll U) psi)
      (act B (Complex.exp (Complex.I * (α : ℂ)) • act (kronAll U) psi)) =
      inner ℂ psi (act ((kronAll U)ᴴ * B * kronAll U) psi) := by
  rw [I_act_smul, inner_smul_left, inner_smul_right, G_inner_act, ← G_act_mul, ← G_act_mul, ← mul_assoc,
    phase_unit, one_mul]

lemma RQ_phi {M : ℕ} (U : Fin M → Matrix Bool Bool ℂ) (hU : ∀ j, star (U j) * U j = 1) (α : ℝ) (psi : Ket M)
    (q : Fin M) :
    RQ (Complex.exp (Complex.I * (α : ℂ)) • act (kronAll U) psi) q = U q * RQ psi q * (U q)ᴴ := by
  ext y x
  rw [RQ, Matrix.of_apply, inner_phi, K_conj U hU, RQ_exp, Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply, Fintype.sum_bool]
  cases x <;> cases y <;> simp

lemma RQ_herm {M : ℕ} (psi : Ket M) (q : Fin M) : (RQ psi q)ᴴ = RQ psi q := by
  ext y x
  simp only [Matrix.conjTranspose_apply, RQ, Matrix.of_apply]
  rw [show star (inner ℂ psi (act (LQ q (Matrix.single y x 1)) psi)) =
    conj (inner ℂ psi (act (LQ q (Matrix.single y x 1)) psi)) from rfl, inner_conj_symm, G_inner_act, LQ_conjT,
    Matrix.conjTranspose_single, star_one]

lemma f_eq (ρ : Matrix Bool Bool ℂ) (hρ : ρᴴ = ρ) :
    ∑ a : Fin 3, ((pauli a * ρ).trace.re) ^ 2 = 2 * (ρ * ρ).trace.re - (ρ.trace.re) ^ 2 := by
  have h1 : star (ρ false true) = ρ true false := by
    have := congrFun (congrFun hρ true) false; simpa [Matrix.conjTranspose_apply] using this
  have h2 : star (ρ false false) = ρ false false := by
    have := congrFun (congrFun hρ false) false; simpa [Matrix.conjTranspose_apply] using this
  have h3 : star (ρ true true) = ρ true true := by
    have := congrFun (congrFun hρ true) true; simpa [Matrix.conjTranspose_apply] using this
  have i2 : (ρ false false).im = 0 := by
    have := congrArg Complex.im h2; simp at this; linarith
  have i3 : (ρ true true).im = 0 := by
    have := congrArg Complex.im h3; simp at this; linarith
  have r1 : (ρ true false).re = (ρ false true).re := by
    have := congrArg Complex.re h1; simpa using this.symm
  have m1 : (ρ true false).im = -(ρ false true).im := by
    have := congrArg Complex.im h1; simp at this; linarith
  simp only [Fin.sum_univ_three, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_bool]
  simp [pauli, pauliX, pauliY, pauliZ, Complex.mul_re, i2, i3, r1, m1]
  ring

lemma bloch_RQ {M : ℕ} (psi : Ket M) (q : Fin M) :
    ‖bloch psi q‖ ^ 2 = 2 * (RQ psi q * RQ psi q).trace.re - ((RQ psi q).trace.re) ^ 2 := by
  rw [← f_eq _ (RQ_herm psi q), EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp only [bloch, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]
  rw [show localPauli q a = LQ q (pauli a) from rfl, RQ_exp]

lemma conj_tr {V ρ : Matrix Bool Bool ℂ} (hV : star V * V = 1) :
    (V * ρ * Vᴴ).trace = ρ.trace ∧ ((V * ρ * Vᴴ) * (V * ρ * Vᴴ)).trace = (ρ * ρ).trace := by
  have hV' : Vᴴ * V = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact hV
  constructor
  · rw [Matrix.trace_mul_cycle, hV', Matrix.one_mul]
  · have : (V * ρ * Vᴴ) * (V * ρ * Vᴴ) = V * (ρ * ρ) * Vᴴ := by
      simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc Vᴴ V, hV', Matrix.one_mul]
    rw [this, Matrix.trace_mul_cycle, hV', Matrix.one_mul]

end QAlgorithms.Papers.Independent.Information100.P10

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P10 in
open scoped ComplexConjugate in
theorem solution {M : ℕ} (psi : Ket M) (hpsi : IsState psi)
    (alpha : ℝ) (U : Fin M → Matrix.specialUnitaryGroup Bool ℂ) :
    let phi := Complex.exp (Complex.I * (alpha : ℂ)) •
      act (kronAll (fun q => (U q : Matrix Bool Bool ℂ))) psi
    IsState phi ∧ entanglementDistance phi = entanglementDistance psi ∧
      ∀ q, ‖bloch phi q‖ ^ 2 = ‖bloch psi q‖ ^ 2 := by
  intro phi
  have hU : ∀ j, star (U j : Matrix Bool Bool ℂ) * (U j : Matrix Bool Bool ℂ) = 1 := fun j =>
    Matrix.mem_unitaryGroup_iff'.1 (Matrix.mem_specialUnitaryGroup_iff.1 (U j).2).1
  have hst : IsState phi := by
    have h2 : ‖phi‖ ^ 2 = 1 := by
      have h1 : phi = Complex.exp (Complex.I * (alpha : ℂ)) • act (kronAll (fun q => (U q : Matrix Bool Bool ℂ))) psi := rfl
      rw [@norm_sq_eq_re_inner ℂ]
      have : inner ℂ phi phi = inner ℂ phi (act 1 phi) := by simp [act]
      rw [this, h1, inner_phi, Matrix.mul_one, K_unit _ hU]
      have h3 : act 1 psi = psi := by simp [act]
      rw [h3, inner_self_eq_norm_sq_to_K, show ‖psi‖ = 1 from hpsi]; simp
    unfold IsState
    nlinarith [norm_nonneg phi]
  have hb : ∀ q, ‖bloch phi q‖ ^ 2 = ‖bloch psi q‖ ^ 2 := by
    intro q
    rw [bloch_RQ, bloch_RQ]
    rw [show phi = Complex.exp (Complex.I * (alpha : ℂ)) • act (kronAll (fun q => (U q : Matrix Bool Bool ℂ))) psi
      from rfl, RQ_phi _ hU]
    obtain ⟨t1, t2⟩ := conj_tr (ρ := RQ psi q) (hU q)
    rw [t1, t2]
  refine ⟨hst, ?_, hb⟩
  rw [(geometricMinimum _ hst).2.2.2.2.1, (geometricMinimum _ hpsi).2.2.2.2.1]
  simp only [hb]
