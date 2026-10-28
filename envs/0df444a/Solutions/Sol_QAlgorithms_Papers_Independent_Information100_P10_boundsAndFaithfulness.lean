-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P10.boundsAndFaithfulness
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T18:49:43.839713+00:00
-- url     : https://prove2.me/submissions/f04ef459-55a5-47ac-9703-22891ff863cf

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


lemma J_inner_one {M : ℕ} (psi : Ket M) (hpsi : IsState psi) : inner ℂ psi psi = 1 := by
  rw [inner_self_eq_norm_sq_to_K, show ‖psi‖ = 1 from hpsi]; simp

/-- key positivity: for unit `n`, ⟨ψ,(1-D)ψ⟩ = ½‖(1-D)ψ‖² -/
lemma J_key {M : ℕ} (psi : Ket M) (q : Fin M) (n : Direction) (hn : ‖n‖ = 1) :
    inner ℂ psi (act (1 - directionalPauli q n) psi) =
      ((‖act (1 - directionalPauli q n) psi‖ ^ 2 / 2 : ℝ) : ℂ) := by
  set D := directionalPauli q n
  suffices h : 2 * inner ℂ psi (act (1 - D) psi) = (‖act (1 - D) psi‖ : ℂ) ^ 2 by
    push_cast; linear_combination h / 2
  have hT : (1 - D)ᴴ * (1 - D) = 2 • (1 - D) := by
    have hD : D * D = 1 := G_dir_sq q n hn
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, G_dir_herm, sub_mul, mul_sub, mul_sub, hD]
    simp only [Matrix.one_mul, Matrix.mul_one, two_smul]; abel
  rw [show (‖act (1 - D) psi‖ : ℂ) ^ 2 = inner ℂ (act (1 - D) psi) (act (1 - D) psi) from by
    rw [inner_self_eq_norm_sq_to_K]; rfl]
  rw [G_inner_act, ← G_act_mul, hT]
  rw [two_smul, act_addM, inner_add_right]
  ring

lemma J_re {M : ℕ} (psi : Ket M) (hpsi : IsState psi) (q : Fin M) (n : Direction) :
    (inner ℂ psi (act (1 - directionalPauli q n) psi)).re = 1 - inner ℝ n (bloch psi q) := by
  have : act (1 - directionalPauli q n) psi = psi - act (directionalPauli q n) psi := by
    simp [act, Matrix.sub_mulVec]
  rw [this, inner_sub_right, J_inner_one psi hpsi, G_dir_exp]
  simp

lemma J_bound {M : ℕ} (psi : Ket M) (hpsi : IsState psi) (q : Fin M) : ‖bloch psi q‖ ≤ 1 := by
  set b := bloch psi q
  by_cases hb : b = 0
  · rw [hb, norm_zero]; norm_num
  have hbn : 0 < ‖b‖ := norm_pos_iff.2 hb
  set n : Direction := ‖b‖⁻¹ • b
  have hn : ‖n‖ = 1 := by
    simp only [n, norm_smul, norm_inv, norm_norm]; field_simp
  have h1 := congrArg Complex.re (J_key psi q n hn)
  rw [J_re psi hpsi q n, Complex.ofReal_re] at h1
  have h2 : inner ℝ n b = ‖b‖ := by
    simp only [n, real_inner_smul_left, real_inner_self_eq_norm_sq]; field_simp
  rw [h2] at h1
  nlinarith [sq_nonneg ‖act (1 - directionalPauli q n) psi‖]

lemma J_fix {M : ℕ} (psi : Ket M) (hpsi : IsState psi) (q : Fin M) (h : ‖bloch psi q‖ = 1) :
    act (directionalPauli q (bloch psi q)) psi = psi := by
  have h1 := congrArg Complex.re (J_key psi q (bloch psi q) h)
  rw [J_re psi hpsi q, Complex.ofReal_re, real_inner_self_eq_norm_sq, h] at h1
  have h2 : ‖act (1 - directionalPauli q (bloch psi q)) psi‖ = 0 := by nlinarith [norm_nonneg (act (1 - directionalPauli q (bloch psi q)) psi)]
  rw [norm_eq_zero] at h2
  have : act (1 - directionalPauli q (bloch psi q)) psi = psi - act (directionalPauli q (bloch psi q)) psi := by
    simp [act, Matrix.sub_mulVec]
  rw [this, sub_eq_zero] at h2
  exact h2.symm


lemma P_act {M : ℕ} (F : Fin M → Matrix Bool Bool ℂ) (g : Fin M → EuclideanSpace ℂ Bool) :
    act (kronAll F) (prodState g) = prodState (fun j => act (F j) (g j)) := by
  ext z
  simp only [act, prodState, PiLp.toLp_apply, Matrix.mulVec, dotProduct, kronAll, Matrix.of_apply]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Finset.prod_mul_distrib]

lemma P_inner {M : ℕ} (f g : Fin M → EuclideanSpace ℂ Bool) :
    inner ℂ (prodState f) (prodState g) = ∏ j, inner ℂ (f j) (g j) := by
  simp only [prodState, PiLp.inner_apply, PiLp.toLp_apply, RCLike.inner_apply]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [map_prod, Finset.prod_mul_distrib]

lemma one_bloch (u : EuclideanSpace ℂ Bool) (hu : ‖u‖ = 1) :
    ∑ a : Fin 3, (inner ℂ u (act (pauli a) u)).re ^ 2 = 1 := by
  have hn : ‖u‖ ^ 2 = 1 := by rw [hu]; norm_num
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_bool] at hn
  simp only [Complex.sq_norm, Complex.normSq_apply] at hn
  simp only [Fin.sum_univ_three, act, PiLp.inner_apply, RCLike.inner_apply, Fintype.sum_bool, PiLp.toLp_apply,
    Matrix.mulVec, dotProduct]
  simp [pauli, pauliX, pauliY, pauliZ, Complex.mul_re, Complex.mul_im]
  have : ((u true).re * (u true).re + (u true).im * (u true).im +
      ((u false).re * (u false).re + (u false).im * (u false).im)) = 1 := by linarith
  linear_combination (((u true).re * (u true).re + (u true).im * (u true).im +
      ((u false).re * (u false).re + (u false).im * (u false).im)) + 1) * this

lemma sep_bloch {M : ℕ} (z : ℂ) (f : Fin M → EuclideanSpace ℂ Bool) (hz : ‖z‖ = 1)
    (hf : ∀ q, IsState (f q)) (q : Fin M) : ‖bloch (z • prodState f) q‖ = 1 := by
  have hb : ∀ a, (bloch (z • prodState f) q) a = (inner ℂ (f q) (act (pauli a) (f q))).re := by
    intro a
    simp only [bloch, PiLp.toLp_apply]
    rw [I_act_smul, inner_smul_left, inner_smul_right, ← mul_assoc, Complex.conj_mul', hz]
    rw [show localPauli q a = kronAll (fun j => if j = q then pauli a else 1) from rfl, P_act, P_inner]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ q)]
    have : ∏ j ∈ Finset.univ.erase q, inner ℂ (f j) (act (if j = q then pauli a else 1) (f j)) = 1 := by
      refine Finset.prod_eq_one (fun j hj => ?_)
      rw [if_neg (Finset.ne_of_mem_erase hj)]
      have : act (1 : Matrix Bool Bool ℂ) (f j) = f j := by simp [act]
      rw [this, inner_self_eq_norm_sq_to_K, show ‖f j‖ = 1 from hf j]; simp
    rw [this]; simp
  have h2 : ‖bloch (z • prodState f) q‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs, hb]
    exact one_bloch (f q) (hf q)
  nlinarith [norm_nonneg (bloch (z • prodState f) q)]


lemma eig_vec (n : Direction) (hn : ‖n‖ = 1) : ∃ u : EuclideanSpace ℂ Bool, ‖u‖ = 1 ∧
    (1 / 2 : ℂ) • (1 + ∑ a, ((n a : ℝ) : ℂ) • pauli a) = Matrix.of fun x y => u x * conj (u y) := by
  have hn2 : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 := by
    have h := EuclideanSpace.norm_sq_eq n
    rw [hn, Fin.sum_univ_three] at h
    simp only [Real.norm_eq_abs, sq_abs] at h; linarith
  rcases eq_or_lt_of_le (show -1 ≤ n 2 by nlinarith [sq_nonneg (n 0), sq_nonneg (n 1)]) with h | h
  · have hz : n 2 = -1 := h.symm
    have hx : n 0 = 0 := by nlinarith [sq_nonneg (n 0), sq_nonneg (n 1)]
    have hy : n 1 = 0 := by nlinarith [sq_nonneg (n 0), sq_nonneg (n 1)]
    refine ⟨EuclideanSpace.single true 1, by simp, ?_⟩
    ext x y
    cases x <;> cases y <;> simp [Fin.sum_univ_three, pauli, pauliX, pauliY, pauliZ, hx, hy, hz,
      EuclideanSpace.single_apply] <;> norm_num
  · have hpos : 0 < (1 + n 2) / 2 := by linarith
    set s := Real.sqrt ((1 + n 2) / 2) with hs
    have hs0 : 0 < s := Real.sqrt_pos.2 hpos
    have hs2 : s ^ 2 = (1 + n 2) / 2 := Real.sq_sqrt hpos.le
    let u : EuclideanSpace ℂ Bool := WithLp.toLp 2 (fun b => if b then (((n 0 : ℂ) + Complex.I * (n 1 : ℂ)) / (2 * (s : ℂ))) else (s : ℂ))
    have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
    refine ⟨u, ?_, ?_⟩
    · have h2 : ‖u‖ ^ 2 = 1 := by
        rw [EuclideanSpace.norm_sq_eq, Fintype.sum_bool]
        simp only [u, PiLp.toLp_apply, if_true, Bool.false_eq_true, if_false]
        rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_ofNat, Real.norm_eq_abs, abs_of_pos hs0]
        have : ‖(n 0 : ℂ) + Complex.I * (n 1 : ℂ)‖ ^ 2 = n 0 ^ 2 + n 1 ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
        rw [div_pow, this, mul_pow, hs2]
        rw [show (n 0 ^ 2 + n 1 ^ 2) / (2 ^ 2 * ((1 + n 2) / 2)) = (1 - n 2) / 2 by
          rw [div_eq_iff (by positivity)]; nlinarith]
        ring
      nlinarith [norm_nonneg u]
    · ext x y
      have e1 : (s : ℂ) * (s : ℂ) = ((1 + n 2) / 2 : ℝ) := by rw [← hs2]; push_cast; ring
      have hn2C : (n 0 : ℂ) ^ 2 + (n 1 : ℂ) ^ 2 + (n 2 : ℂ) ^ 2 = 1 := by
        have := congrArg (fun r : ℝ => (r : ℂ)) hn2; push_cast at this; exact this
      have key : ((n 0 : ℂ) + Complex.I * (n 1 : ℂ)) * ((n 0 : ℂ) + -(Complex.I * (n 1 : ℂ))) =
          (1 - (n 2 : ℂ)) * (1 + (n 2 : ℂ)) := by
        linear_combination hn2C - (n 1 : ℂ) ^ 2 * Complex.I_sq
      have e1' : (s : ℂ) * (s : ℂ) = (1 + (n 2 : ℂ)) / 2 := by rw [e1]; push_cast; ring
      have h1z : (1 + (n 2 : ℂ)) ≠ 0 := by
        intro hc
        have := congrArg Complex.re hc
        simp at this; linarith
      cases x <;> cases y <;> simp [u, Fin.sum_univ_three, pauli, pauliX, pauliY, pauliZ]
      · rw [e1']; ring
      · simp only [map_ofNat]; field_simp
      · field_simp
      · simp only [map_ofNat]
        rw [div_mul_div_comm, key, show (2 * (s : ℂ)) * (2 * (s : ℂ)) = 4 * ((s : ℂ) * (s : ℂ)) by ring, e1']
        field_simp
        ring


lemma kron_rank1 {M : ℕ} (u : Fin M → EuclideanSpace ℂ Bool) :
    kronAll (fun q => Matrix.of fun x y => u q x * conj (u q y)) =
      Matrix.of fun Y Z => prodState u Y * conj (prodState u Z) := by
  ext Y Z
  simp only [kronAll, prodState, Matrix.of_apply, PiLp.toLp_apply]
  rw [Finset.prod_mul_distrib, map_prod]

lemma act_rank1 {M : ℕ} (U psi : Ket M) :
    act (Matrix.of fun Y Z => U Y * conj (U Z)) psi = inner ℂ U psi • U := by
  ext Y
  simp only [act, PiLp.toLp_apply, Matrix.mulVec, dotProduct, Matrix.of_apply, PiLp.smul_apply, smul_eq_mul,
    PiLp.inner_apply, RCLike.inner_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun Z _ => ?_)
  ring

lemma fix_induct {M : ℕ} (P : Fin M → Matrix Bool Bool ℂ) (psi : Ket M)
    (h : ∀ q, act (LQ q (P q)) psi = psi) :
    ∀ S : Finset (Fin M), act (kronAll (fun j => if j ∈ S then P j else 1)) psi = psi := by
  intro S
  induction S using Finset.induction_on with
  | empty => simp only [Finset.notMem_empty, if_false]; rw [G_kron_one]; simp [act]
  | insert q S hq ih =>
    have : kronAll (fun j => if j ∈ insert q S then P j else 1) =
        LQ q (P q) * kronAll (fun j => if j ∈ S then P j else 1) := by
      unfold LQ; rw [G_kron_mul]; congr 1; funext j
      by_cases hj : j = q
      · subst hj; simp [hq]
      · simp [hj]
    rw [this, G_act_mul, ih, h q]

end QAlgorithms.Papers.Independent.Information100.P10

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P10 in
open scoped ComplexConjugate in
theorem solution {M : ℕ} (psi : Ket M) (hpsi : IsState psi) :
    (∀ q, 0 ≤ localED psi q ∧ localED psi q ≤ 1) ∧
    (0 ≤ entanglementDistance psi ∧ entanglementDistance psi ≤ (M : ℝ)) ∧
    (entanglementDistance psi = 0 ↔ FullySeparable psi) := by
  have hsum := (geometricMinimum psi hpsi).2.2.2.2.2.1
  have hloc : ∀ q, 0 ≤ localED psi q ∧ localED psi q ≤ 1 := by
    intro q
    unfold localED
    have h1 := J_bound psi hpsi q
    constructor <;> nlinarith [norm_nonneg (bloch psi q)]
  refine ⟨hloc, ⟨?_, ?_⟩, ⟨fun h0 => ?_, fun hs => ?_⟩⟩
  · rw [hsum]; exact Finset.sum_nonneg (fun q _ => (hloc q).1)
  · rw [hsum]
    calc ∑ q, localED psi q ≤ ∑ _q : Fin M, (1 : ℝ) := Finset.sum_le_sum (fun q _ => (hloc q).2)
      _ = M := by simp
  · rw [hsum] at h0
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun q _ => (hloc q).1)).1 h0
    have hb1 : ∀ q, ‖bloch psi q‖ = 1 := by
      intro q
      have := hz q (Finset.mem_univ q)
      unfold localED at this
      have h1 := J_bound psi hpsi q
      nlinarith [norm_nonneg (bloch psi q)]
    have hex := fun q => eig_vec (bloch psi q) (hb1 q)
    choose u hu hP using hex
    have hfix : ∀ q, act (LQ q (Matrix.of fun x y => u q x * conj (u q y))) psi = psi := by
      intro q
      rw [← hP q, LQ_smul, LQ_add, LQ_one, ← G_dir_eq, act_smulM, act_addM, J_fix psi hpsi q (hb1 q)]
      have : act (1 : Matrix (Qubits M) (Qubits M) ℂ) psi = psi := by simp [act]
      rw [this, ← two_smul ℂ psi, smul_smul]; norm_num
    have hall := fix_induct _ psi hfix Finset.univ
    simp only [Finset.mem_univ, if_true] at hall
    rw [kron_rank1, act_rank1] at hall
    have hU : ‖prodState u‖ = 1 := by
      have h2 : ‖prodState u‖ ^ 2 = 1 := by
        rw [@norm_sq_eq_re_inner ℂ, P_inner]
        have : ∀ j, inner ℂ (u j) (u j) = 1 := fun j => by
          rw [inner_self_eq_norm_sq_to_K, hu j]; simp
        simp only [this, Finset.prod_const_one]; simp
      nlinarith [norm_nonneg (prodState u)]
    refine ⟨inner ℂ (prodState u) psi, u, ?_, hu, hall.symm⟩
    have := congrArg norm hall
    rw [norm_smul, hU, mul_one, show ‖psi‖ = 1 from hpsi] at this
    exact this
  · obtain ⟨z, f, hz, hf, rfl⟩ := hs
    rw [hsum]
    refine Finset.sum_eq_zero (fun q _ => ?_)
    unfold localED
    rw [sep_bloch z f hz hf q]; norm_num
