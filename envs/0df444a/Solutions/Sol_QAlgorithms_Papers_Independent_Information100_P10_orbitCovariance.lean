-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P10.orbitCovariance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T18:34:16.963073+00:00
-- url     : https://prove2.me/submissions/af3dcf05-bdb8-4a4c-8004-7f31ee1c808d

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P10
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

end QAlgorithms.Papers.Independent.Information100.P10

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P10 in
open scoped ComplexConjugate in
theorem solution {M : ℕ} (psi : Ket M) (hpsi : IsState psi)
    (v : Fin M → Direction) (hv : v ∈ directionDomain M) :
    (∀ q r, orbitMetric psi v q r =
      inner ℂ psi (act (directionalPauli q (v q) * directionalPauli r (v r)) psi) -
      inner ℂ psi (act (directionalPauli q (v q)) psi) *
        inner ℂ psi (act (directionalPauli r (v r)) psi)) ∧
    traceObjective psi v = ∑ q, (1 - (inner ℝ (v q) (bloch psi q)) ^ 2) := by
  refine ⟨fun q r => ?_, ?_⟩
  · unfold orbitMetric fsForm orbitTangent
    simp only [inner_smul_left, inner_smul_right, G_inner_act, G_dir_herm, G_act_mul]
    simp only [Complex.conj_neg_I]
    linear_combination (inner ℂ psi (act (directionalPauli q (v q)) psi) * inner ℂ psi (act (directionalPauli r (v r)) psi) -
      inner ℂ psi (act (directionalPauli q (v q)) (act (directionalPauli r (v r)) psi))) * Complex.I_sq
  · unfold traceObjective
    rw [Matrix.trace, Complex.re_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    have hq : ‖v q‖ = 1 := hv q
    simp only [Matrix.diag]
    unfold orbitMetric fsForm orbitTangent
    simp only [inner_smul_left, inner_smul_right, G_inner_act, G_dir_herm, ← G_act_mul, G_dir_sq q (v q) hq,
      Complex.conj_neg_I, G_dir_exp]
    have h1 : inner ℂ psi (act 1 psi) = 1 := by
      have : act 1 psi = psi := by simp [act]
      rw [this, inner_self_eq_norm_sq_to_K, show ‖psi‖ = 1 from hpsi]; simp
    rw [h1]
    have h2 : ((-Complex.I) * (Complex.I * 1) - Complex.I * ((inner ℝ (v q) (bloch psi q) : ℝ) : ℂ) *
        (-Complex.I * ((inner ℝ (v q) (bloch psi q) : ℝ) : ℂ))) =
        ((1 - (inner ℝ (v q) (bloch psi q)) ^ 2 : ℝ) : ℂ) := by
      push_cast
      linear_combination (-1 + ((inner ℝ (v q) (bloch psi q) : ℝ) : ℂ) ^ 2) * Complex.I_sq
    rw [h2, Complex.ofReal_re]
