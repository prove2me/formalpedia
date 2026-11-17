-- Prove2me | solution 1 for QAOAE3Lin2.General.eq_25
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-17T00:45:18.533926+00:00
-- url     : https://prove2.me/submissions/3588c28c-2145-431d-b173-0ecc1e976446

import Mathlib
import Definitions.Def_QAOAE3Lin2_General_Setting

set_option autoImplicit false


open scoped Matrix
open QAlgorithms

/-! ### Exponentials of idempotents and involutions -/

set_option backward.isDefEq.respectTransparency false in
/-- The exponential of a scalar multiple of an idempotent matrix. -/
theorem q25_exp_idem {ι : Type} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℂ) (hP : P * P = P)
    (c : ℂ) : NormedSpace.exp (c • P) = 1 + (Complex.exp c - 1) • P := by
  have hpow : ∀ n : ℕ, 1 ≤ n → (c • P) ^ n = c ^ n • P := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ k hk ih => rw [pow_succ, ih, smul_mul_smul_comm, hP, ← pow_succ]
  have h1 : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • (c • P) ^ n) (NormedSpace.exp (c • P)) := by
    open scoped Matrix.Norms.Operator in
    exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (c • P)
  have h2 : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • c ^ n) (NormedSpace.exp c) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) c
  have h3 : HasSum (fun n : ℕ => (((n.factorial : ℂ)⁻¹) • c ^ n) • P) (NormedSpace.exp c • P) :=
    h2.smul_const P
  have h4 : HasSum (fun n : ℕ => if n = 0 then (1 - P) else 0) (1 - P) := by
    have := hasSum_single (f := fun n : ℕ => if n = 0 then (1 - P) else 0) 0
      (fun n hn => if_neg hn)
    simpa using this
  have h5 := h3.add h4
  have hfun : (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • (c • P) ^ n) =
      fun n => (((n.factorial : ℂ)⁻¹) • c ^ n) • P + (if n = 0 then (1 - P) else 0) := by
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [hpow n hn, if_neg (by omega), add_zero, smul_assoc]
  rw [hfun] at h1
  have huniq := h1.unique h5
  rw [huniq, ← Complex.exp_eq_exp_ℂ, sub_smul, one_smul]
  abel

/-- Two complementary orthogonal idempotents `Pp`, `Pm` with `Pp - Pm = X` give
`exp(i (π/2) X) = i X`. -/
theorem q25_exp_invol_aux {ι : Type} [Fintype ι] [DecidableEq ι] (Pp Pm X : Matrix ι ι ℂ)
    (hPp : Pp * Pp = Pp) (hPm : Pm * Pm = Pm) (hpm : Pp * Pm = 0) (hmp : Pm * Pp = 0)
    (hsum : Pp + Pm = 1) (hdiff : Pp - Pm = X) :
    NormedSpace.exp ((Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) • X) = Complex.I • X := by
  set c : ℂ := Complex.I * ((Real.pi / 2 : ℝ) : ℂ) with hc
  have hdecomp : c • X = c • Pp + (-c) • Pm := by
    rw [← hdiff]; module
  have hcomm : Commute (c • Pp) ((-c) • Pm) := by
    show c • Pp * ((-c) • Pm) = (-c) • Pm * (c • Pp)
    rw [smul_mul_smul_comm, smul_mul_smul_comm, hpm, hmp, smul_zero, smul_zero]
  have hexp1 : Complex.exp c = Complex.I := by
    rw [hc, mul_comm, Complex.exp_mul_I]
    simp
  have hexp2 : Complex.exp (-c) = -Complex.I := by
    rw [Complex.exp_neg, hexp1, Complex.inv_I]
  rw [hdecomp, Matrix.exp_add_of_commute _ _ hcomm, q25_exp_idem Pp hPp c,
    q25_exp_idem Pm hPm (-c), hexp1, hexp2]
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, hpm, smul_zero, add_zero]
  rw [← hsum, ← hdiff]
  module

/-- For an involution `X`, `exp(i (π/2) X) = i X`. -/
theorem q25_exp_invol {ι : Type} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) (hX : X * X = 1) :
    NormedSpace.exp ((Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) • X) = Complex.I • X := by
  have e1 : (1 + X) * (1 + X) = (2 : ℂ) • (1 + X) := by
    rw [add_mul, one_mul, mul_add, mul_one, hX]; module
  have e2 : (1 - X) * (1 - X) = (2 : ℂ) • (1 - X) := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hX]; module
  have e3 : (1 + X) * (1 - X) = 0 := by
    rw [add_mul, one_mul, mul_sub, mul_one, hX]; abel
  have e4 : (1 - X) * (1 + X) = 0 := by
    rw [sub_mul, one_mul, mul_add, mul_one, hX]; abel
  refine q25_exp_invol_aux ((1 / 2 : ℂ) • (1 + X)) ((1 / 2 : ℂ) • (1 - X)) X ?_ ?_ ?_ ?_ ?_ ?_
  · rw [smul_mul_smul_comm, e1, smul_smul]; norm_num
  · rw [smul_mul_smul_comm, e2, smul_smul]; norm_num
  · rw [smul_mul_smul_comm, e3, smul_zero]
  · rw [smul_mul_smul_comm, e4, smul_zero]
  · module
  · module

open scoped Matrix
open QAlgorithms

/-! ### Bit flips and the Pauli `X` matrices -/

/-- Flip bit `j` of a basis string. -/
def q25flip {n : ℕ} (j : Fin n) (x : Qubits n) : Qubits n := Function.update x j (!x j)

theorem q25flip_same {n : ℕ} (j : Fin n) (x : Qubits n) : q25flip j x j = !x j := by
  simp [q25flip]

theorem q25flip_ne {n : ℕ} (j : Fin n) {k : Fin n} (h : k ≠ j) (x : Qubits n) :
    q25flip j x k = x k := by
  simp [q25flip, Function.update_of_ne h]

theorem q25flip_invol {n : ℕ} (j : Fin n) : Function.Involutive (q25flip (n := n) j) := by
  intro x
  funext k
  by_cases h : k = j
  · subst h
    rw [q25flip_same, q25flip_same, Bool.not_not]
  · rw [q25flip_ne j h, q25flip_ne j h]

theorem q25flip_comm {n : ℕ} (j k : Fin n) (x : Qubits n) :
    q25flip j (q25flip k x) = q25flip k (q25flip j x) := by
  funext l
  by_cases hj : l = j
  · by_cases hk : l = k
    · subst hj; subst hk; rfl
    · subst hj
      rw [q25flip_same, q25flip_ne k hk, q25flip_ne k hk, q25flip_same]
  · by_cases hk : l = k
    · subst hk
      rw [q25flip_ne j hj, q25flip_same, q25flip_same, q25flip_ne j hj]
    · rw [q25flip_ne j hj, q25flip_ne k hk, q25flip_ne k hk, q25flip_ne j hj]

/-- The Pauli `X` on wire `j`, as the permutation matrix of the bit flip. -/
noncomputable def q25X {n : ℕ} (j : Fin n) : Matrix (Qubits n) (Qubits n) ℂ :=
  ((q25flip_invol j).toPerm (q25flip j)).toPEquiv.toMatrix

theorem q25X_apply {n : ℕ} (j : Fin n) (y z : Qubits n) :
    q25X j y z = if q25flip j y = z then 1 else 0 := by
  simp [q25X, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Function.Involutive.coe_toPerm,
    eq_comm]

theorem q25X_mulVec {n : ℕ} (j : Fin n) (u : Qubits n → ℂ) : q25X j *ᵥ u = u ∘ q25flip j := by
  unfold q25X
  rw [PEquiv.toMatrix_toPEquiv_mulVec]
  rfl

theorem q25X_mul_self {n : ℕ} (j : Fin n) : q25X j * q25X j = 1 := by
  unfold q25X
  rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]
  have h : ((q25flip_invol j).toPerm (q25flip j)).trans ((q25flip_invol j).toPerm (q25flip j)) =
      Equiv.refl (Qubits n) := by
    ext x : 1
    simp only [Equiv.trans_apply, Function.Involutive.coe_toPerm, Equiv.refl_apply]
    exact q25flip_invol j x
  rw [h, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]

theorem q25X_comm {n : ℕ} (j k : Fin n) : q25X j * q25X k = q25X k * q25X j := by
  unfold q25X
  rw [← PEquiv.toMatrix_trans, ← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans,
    ← Equiv.toPEquiv_trans]
  have h : ((q25flip_invol j).toPerm (q25flip j)).trans ((q25flip_invol k).toPerm (q25flip k)) =
      ((q25flip_invol k).toPerm (q25flip k)).trans ((q25flip_invol j).toPerm (q25flip j)) := by
    ext x : 1
    simp only [Equiv.trans_apply, Function.Involutive.coe_toPerm]
    exact q25flip_comm k j x
  rw [h]

/-- The QAOA mixer is the sum of the bit-flip matrices. -/
theorem q25_mixer_eq (n : ℕ) : qaoaMixer n = ∑ j : Fin n, q25X j := by
  unfold qaoaMixer
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ext y z
  rw [q25X_apply]
  show (if ∀ a : Fin n, a ∉ Set.range (Stabilizer.wire1 j) → y a = z a then
      pauliX (y j) (z j) else 0) = _
  have hr : ∀ a : Fin n, a ∉ Set.range (Stabilizer.wire1 j) ↔ a ≠ j := by
    intro a
    constructor
    · intro h hj
      exact h ⟨0, hj.symm⟩
    · rintro h ⟨_, rfl⟩
      exact h rfl
  by_cases hf : q25flip j y = z
  · subst hf
    rw [if_pos rfl]
    have hc : ∀ a : Fin n, a ∉ Set.range (Stabilizer.wire1 j) → y a = q25flip j y a :=
      fun a ha => (q25flip_ne j ((hr a).mp ha) y).symm
    rw [if_pos hc, q25flip_same]
    simp [pauliX]
  · rw [if_neg hf]
    by_cases hc : ∀ a : Fin n, a ∉ Set.range (Stabilizer.wire1 j) → y a = z a
    · rw [if_pos hc]
      have hjeq : y j = z j := by
        by_contra hne
        apply hf
        funext a
        by_cases ha : a = j
        · subst ha
          rw [q25flip_same]
          cases hy : y a <;> cases hz : z a <;> simp_all
        · rw [q25flip_ne j ha]
          exact hc a ((hr a).mpr ha)
      simp [pauliX, hjeq]
    · rw [if_neg hc]

/-! ### Conjugating the mixer exponential by a sign matrix -/

theorem q25_Z_conj_X {n : ℕ} (p : Qubits n → ℝ) (s : Fin n → ℝ) (hp : ∀ x, p x * p x = 1)
    (hs : ∀ j x, p (q25flip j x) = s j * p x) (j : Fin n) :
    Matrix.diagonal (fun x => ((p x : ℝ) : ℂ)) * q25X j * Matrix.diagonal (fun x => ((p x : ℝ) : ℂ)) =
      ((s j : ℝ) : ℂ) • q25X j := by
  ext y z
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, q25X_apply]
  by_cases h : q25flip j y = z
  · subst h
    rw [if_pos rfl, hs j y, smul_eq_mul, mul_one, mul_one, ← Complex.ofReal_mul]
    congr 1
    calc p y * (s j * p y) = s j * (p y * p y) := by ring
      _ = s j := by rw [hp y, mul_one]
  · rw [if_neg h]
    simp

/-- At mixer angle `π/4`, a sign matrix that anticommutes with `X_a, X_b, X_c` and commutes
with the other `X_j` passes through the mixer exponential at the cost of `(i X_a)(i X_b)(i X_c)`. -/
theorem q25_conj {n : ℕ} (p : Qubits n → ℝ) (hp : ∀ x, p x * p x = 1) (a b c : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hflip : ∀ j x, p (q25flip j x) = (if j = a ∨ j = b ∨ j = c then (-1 : ℝ) else 1) * p x) :
    Matrix.diagonal (fun x => ((p x : ℝ) : ℂ)) *
        NormedSpace.exp (-(Complex.I * ((Real.pi / 4 : ℝ) : ℂ)) • qaoaMixer n) =
      NormedSpace.exp (-(Complex.I * ((Real.pi / 4 : ℝ) : ℂ)) • qaoaMixer n) *
        ((Complex.I • q25X a) * (Complex.I • q25X b) * (Complex.I • q25X c)) *
          Matrix.diagonal (fun x => ((p x : ℝ) : ℂ)) := by
  classical
  set Z : Matrix (Qubits n) (Qubits n) ℂ := Matrix.diagonal (fun x => ((p x : ℝ) : ℂ)) with hZdef
  set B : Matrix (Qubits n) (Qubits n) ℂ := qaoaMixer n with hBdef
  set c₀ : ℂ := -(Complex.I * ((Real.pi / 4 : ℝ) : ℂ)) with hc₀
  set θ : ℂ := Complex.I * ((Real.pi / 2 : ℝ) : ℂ) with hθ
  have hB : B = ∑ j : Fin n, q25X j := q25_mixer_eq n
  have hZ2 : Z * Z = 1 := by
    rw [hZdef, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext x
    rw [← Complex.ofReal_mul, hp x, Complex.ofReal_one]
  have hZinv : Z⁻¹ = Z := Matrix.inv_eq_right_inv hZ2
  have hZunit : IsUnit Z := ⟨⟨Z, Z, hZ2, hZ2⟩, rfl⟩
  -- the sum of the three flipped `X`'s
  have hsum3 : ∑ j : Fin n, (if j = a ∨ j = b ∨ j = c then q25X j else 0) =
      q25X a + q25X b + q25X c := by
    rw [← Finset.sum_filter]
    have hfil : Finset.univ.filter (fun j : Fin n => j = a ∨ j = b ∨ j = c) = {a, b, c} := by
      ext j; simp
    rw [hfil, Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
      Finset.sum_singleton, add_assoc]
  -- conjugating the mixer
  have h1 : Z * B * Z = B - (2 : ℂ) • (q25X a + q25X b + q25X c) := by
    rw [hB, Finset.mul_sum, Finset.sum_mul, ← hsum3, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hZdef, q25_Z_conj_X p (fun j => if j = a ∨ j = b ∨ j = c then (-1 : ℝ) else 1) hp hflip j]
    by_cases h : j = a ∨ j = b ∨ j = c
    · simp only [h, if_true]
      push_cast
      module
    · simp only [h, if_false]
      push_cast
      module
  have h2 : Z * NormedSpace.exp (c₀ • B) * Z =
      NormedSpace.exp (c₀ • (B - (2 : ℂ) • (q25X a + q25X b + q25X c))) := by
    have hconj := Matrix.exp_conj Z (c₀ • B) hZunit
    rw [hZinv] at hconj
    rw [← hconj, Matrix.mul_smul, Matrix.smul_mul, h1]
  have hcθ : -(c₀ * 2) = θ := by
    rw [hc₀, hθ]
    push_cast
    ring
  have h3 : c₀ • (B - (2 : ℂ) • (q25X a + q25X b + q25X c)) =
      c₀ • B + θ • (q25X a + q25X b + q25X c) := by
    rw [← hcθ]
    module
  have hXc : ∀ j k : Fin n, Commute (q25X j) (q25X k) := fun j k => q25X_comm j k
  have hBX : ∀ k : Fin n, Commute B (q25X k) := by
    intro k
    rw [hB]
    exact Commute.sum_left _ _ _ (fun j _ => hXc j k)
  have hBS : Commute B (q25X a + q25X b + q25X c) :=
    ((hBX a).add_right (hBX b)).add_right (hBX c)
  have h4 : Commute (c₀ • B) (θ • (q25X a + q25X b + q25X c)) :=
    (hBS.smul_left c₀).smul_right θ
  have h6 : NormedSpace.exp (θ • (q25X a + q25X b + q25X c)) =
      (Complex.I • q25X a) * (Complex.I • q25X b) * (Complex.I • q25X c) := by
    have hab' : Commute (θ • q25X a) (θ • q25X b) := ((hXc a b).smul_left θ).smul_right θ
    have hac' : Commute (θ • q25X a) (θ • q25X c) := ((hXc a c).smul_left θ).smul_right θ
    have hbc' : Commute (θ • q25X b) (θ • q25X c) := ((hXc b c).smul_left θ).smul_right θ
    rw [smul_add, smul_add, Matrix.exp_add_of_commute _ _ (hac'.add_left hbc'),
      Matrix.exp_add_of_commute _ _ hab', hθ, q25_exp_invol _ (q25X_mul_self a),
      q25_exp_invol _ (q25X_mul_self b), q25_exp_invol _ (q25X_mul_self c)]
  calc Z * NormedSpace.exp (c₀ • B)
      = Z * NormedSpace.exp (c₀ • B) * (Z * Z) := by rw [hZ2, mul_one]
    _ = Z * NormedSpace.exp (c₀ • B) * Z * Z := by rw [mul_assoc, mul_assoc, mul_assoc]
    _ = NormedSpace.exp (c₀ • B) *
          ((Complex.I • q25X a) * (Complex.I • q25X b) * (Complex.I • q25X c)) * Z := by
        rw [h2, h3, Matrix.exp_add_of_commute _ _ h4, h6]

open scoped Matrix
open QAlgorithms

/-- The exponential of a skew-Hermitian matrix is unitary. -/
theorem ct_exp_unitary {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (hA : Aᴴ = -A) :
    NormedSpace.exp A ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have h1 : star (NormedSpace.exp A) = NormedSpace.exp (-A) := by
    rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hA]
  rw [h1, ← Matrix.exp_add_of_commute (-A) A (Commute.neg_left (Commute.refl A)), neg_add_cancel,
    NormedSpace.exp_zero]

/-- `-(i t) H` is skew-Hermitian for Hermitian `H` and real `t`. -/
theorem ct_skew {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (t : ℝ) : (-(Complex.I * (t : ℂ)) • H)ᴴ = -(-(Complex.I * (t : ℂ)) • H) := by
  rw [Matrix.conjTranspose_smul, hH.eq]
  have hstar : star (-(Complex.I * (t : ℂ))) = Complex.I * (t : ℂ) := by
    simp [Complex.conj_ofReal]
  rw [hstar, neg_smul, neg_neg]

theorem ct_problem_herm {n : ℕ} (f : Qubits n → ℝ) : (problemHamiltonian f).IsHermitian := by
  refine Matrix.IsHermitian.ext (fun y z => ?_)
  simp only [problemHamiltonian, Matrix.diagonal_apply]
  by_cases h : y = z
  · subst h; simp
  · have h' : ¬ z = y := fun hh => h hh.symm
    simp [h, h']

theorem ct_pauliX_herm : pauliX.IsHermitian := by
  refine Matrix.IsHermitian.ext (fun a b => ?_)
  simp only [pauliX, Matrix.of_apply]
  by_cases h : a = b
  · subst h; simp
  · have h' : ¬ b = a := fun hh => h hh.symm
    simp [h, h']

theorem ct_embed_herm {k n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ) (hM : M.IsHermitian)
    (w : Fin k ↪ Fin n) : (embedOp M w).IsHermitian := by
  refine Matrix.IsHermitian.ext (fun y z => ?_)
  simp only [embedOp, Matrix.of_apply]
  by_cases h : ∀ a : Fin n, a ∉ Set.range w → y a = z a
  · have h' : ∀ a : Fin n, a ∉ Set.range w → z a = y a := fun a ha => (h a ha).symm
    rw [if_pos h, if_pos h']
    exact hM.apply (y ∘ w) (z ∘ w)
  · have h' : ¬ ∀ a : Fin n, a ∉ Set.range w → z a = y a :=
      fun hh => h (fun a ha => (hh a ha).symm)
    rw [if_neg h, if_neg h', star_zero]

theorem ct_mixer_herm (n : ℕ) : (qaoaMixer n).IsHermitian := by
  unfold qaoaMixer Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact ct_embed_herm _ (ct_pauliX_herm.submatrix _) _


/-! ### The expectation as a sum over basis strings -/

/-- Heisenberg picture: if the sign matrix `Z` passes through the unitary `E` as `Z E = E W Z`,
then the `Z`-expectation of `E v` is `⟨v, W Z v⟩`. -/
theorem q25_heis {ι : Type} [Fintype ι] [DecidableEq ι] (E W : Matrix ι ι ℂ) (p : ι → ℝ)
    (hE : E ∈ Matrix.unitaryGroup ι ℂ)
    (hZE : Matrix.diagonal (fun x => ((p x : ℝ) : ℂ)) * E =
      E * W * Matrix.diagonal (fun x => ((p x : ℝ) : ℂ)))
    (v : ι → ℂ) :
    ((∑ x, ‖(E *ᵥ v) x‖ ^ 2 * p x : ℝ) : ℂ) =
      star v ⬝ᵥ (W *ᵥ (Matrix.diagonal (fun x => ((p x : ℝ) : ℂ)) *ᵥ v)) := by
  have hEE : Eᴴ * E = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff').mp hE
    rwa [Matrix.star_eq_conjTranspose] at h
  have h1 : ((∑ x, ‖(E *ᵥ v) x‖ ^ 2 * p x : ℝ) : ℂ) =
      star (E *ᵥ v) ⬝ᵥ (Matrix.diagonal (fun x => ((p x : ℝ) : ℂ)) *ᵥ (E *ᵥ v)) := by
    rw [dotProduct]
    push_cast
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Matrix.mulVec_diagonal, Pi.star_apply]
    have hc : star ((E *ᵥ v) x) * (E *ᵥ v) x = ((‖(E *ᵥ v) x‖ : ℂ)) ^ 2 :=
      Complex.conj_mul' ((E *ᵥ v) x)
    calc ((‖(E *ᵥ v) x‖ : ℂ)) ^ 2 * (p x : ℂ)
        = (p x : ℂ) * (star ((E *ᵥ v) x) * (E *ᵥ v) x) := by rw [hc]; ring
      _ = star ((E *ᵥ v) x) * ((p x : ℂ) * (E *ᵥ v) x) := by ring
  rw [h1, Matrix.mulVec_mulVec, hZE, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec]
  have h2 : Eᴴ * (E * W * Matrix.diagonal (fun x => ((p x : ℝ) : ℂ))) =
      W * Matrix.diagonal (fun x => ((p x : ℝ) : ℂ)) := by
    rw [← mul_assoc, ← mul_assoc, hEE, one_mul]
  rw [h2, ← Matrix.mulVec_mulVec]

theorem q25_IX_mulVec {n : ℕ} (j : Fin n) (u : Qubits n → ℂ) (y : Qubits n) :
    ((Complex.I • q25X j) *ᵥ u) y = Complex.I * u (q25flip j y) := by
  rw [Matrix.smul_mulVec, q25X_mulVec]
  rfl

/-- Real part of one term of `⟨v, W Z v⟩`. -/
theorem q25_re_term (r pv θ₁ θ₂ : ℝ) :
    (star (Complex.exp ((θ₁ : ℂ) * Complex.I) * (r : ℂ)) *
        (Complex.I * (Complex.I * (Complex.I *
          (((-pv : ℝ) : ℂ) * (Complex.exp ((θ₂ : ℂ) * Complex.I) * (r : ℂ))))))).re =
      r * r * pv * Real.sin (θ₁ - θ₂) := by
  have h1 : star (Complex.exp ((θ₁ : ℂ) * Complex.I) * (r : ℂ)) =
      Complex.exp (((-θ₁ : ℝ) : ℂ) * Complex.I) * (r : ℂ) := by
    rw [star_mul', Complex.star_def, ← Complex.exp_conj, Complex.conj_ofReal,
      map_mul, Complex.conj_ofReal, Complex.conj_I]
    congr 1
    congr 1
    push_cast
    ring
  rw [h1, Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg, Real.sin_sub]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_neg]
  ring

theorem q25_spin_sq {n : ℕ} (x : Qubits n) (v : Fin n) :
    QAOAE3Lin2.General.spin x v * QAOAE3Lin2.General.spin x v = 1 := by
  unfold QAOAE3Lin2.General.spin
  split_ifs <;> norm_num

theorem q25_spin_flip {n : ℕ} (j v : Fin n) (x : Qubits n) :
    QAOAE3Lin2.General.spin (q25flip j x) v =
      if j = v then -QAOAE3Lin2.General.spin x v else QAOAE3Lin2.General.spin x v := by
  unfold QAOAE3Lin2.General.spin
  by_cases h : j = v
  · subst h
    rw [if_pos rfl, q25flip_same]
    cases x j <;> simp
  · rw [if_neg h, q25flip_ne j (fun hv => h hv.symm)]

/-- The product of three spins changes sign exactly under flips of one of its three bits. -/
theorem q25_p_flip {n : ℕ} (a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (j : Fin n)
    (x : Qubits n) :
    QAOAE3Lin2.General.spin (q25flip j x) a * QAOAE3Lin2.General.spin (q25flip j x) b *
        QAOAE3Lin2.General.spin (q25flip j x) c =
      (if j = a ∨ j = b ∨ j = c then (-1 : ℝ) else 1) *
        (QAOAE3Lin2.General.spin x a * QAOAE3Lin2.General.spin x b * QAOAE3Lin2.General.spin x c) := by
  rw [q25_spin_flip, q25_spin_flip, q25_spin_flip]
  by_cases ha : j = a
  · have hb : j ≠ b := fun h => hab (ha.symm.trans h)
    have hc : j ≠ c := fun h => hac (ha.symm.trans h)
    rw [if_pos ha, if_neg hb, if_neg hc, if_pos (Or.inl ha)]; ring
  · by_cases hb : j = b
    · have hc : j ≠ c := fun h => hbc (hb.symm.trans h)
      rw [if_neg ha, if_pos hb, if_neg hc, if_pos (Or.inr (Or.inl hb))]; ring
    · by_cases hc : j = c
      · rw [if_neg ha, if_neg hb, if_pos hc, if_pos (Or.inr (Or.inr hc))]; ring
      · rw [if_neg ha, if_neg hb, if_neg hc, if_neg (by tauto)]; ring

/-- The `Z_a Z_b Z_c` expectation of the level-one QAOA state at mixer angle `π/4`, as a sum over
basis strings of `z_a z_b z_c sin(γ (C(y) - C(y with bits a, b, c flipped)))`. -/
theorem q25_corr {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool) (i : Fin m)
    (hab : (tri i).1 ≠ (tri i).2.1) (hac : (tri i).1 ≠ (tri i).2.2)
    (hbc : (tri i).2.1 ≠ (tri i).2.2) (γ : ℝ) :
    QAOAE3Lin2.General.corr tri rhs i (-γ) (Real.pi / 4) =
      (Fintype.card (Qubits n) : ℝ)⁻¹ * ∑ y : Qubits n,
        (QAOAE3Lin2.General.spin y (tri i).1 * QAOAE3Lin2.General.spin y (tri i).2.1 *
            QAOAE3Lin2.General.spin y (tri i).2.2) *
          Real.sin (γ * (QAOAE3Lin2.General.satCount tri rhs y -
            QAOAE3Lin2.General.satCount tri rhs
              (q25flip (tri i).2.2 (q25flip (tri i).2.1 (q25flip (tri i).1 y))))) := by
  classical
  set a := (tri i).1 with ha
  set b := (tri i).2.1 with hb
  set c := (tri i).2.2 with hc
  set C : Qubits n → ℝ := QAOAE3Lin2.General.satCount tri rhs with hC
  let p : Qubits n → ℝ := fun y =>
    QAOAE3Lin2.General.spin y a * QAOAE3Lin2.General.spin y b * QAOAE3Lin2.General.spin y c
  let F : Qubits n → Qubits n := fun y => q25flip c (q25flip b (q25flip a y))
  have hp : ∀ x, p x * p x = 1 := by
    intro x
    calc p x * p x = (QAOAE3Lin2.General.spin x a * QAOAE3Lin2.General.spin x a) *
          (QAOAE3Lin2.General.spin x b * QAOAE3Lin2.General.spin x b) *
          (QAOAE3Lin2.General.spin x c * QAOAE3Lin2.General.spin x c) := by
          show QAOAE3Lin2.General.spin x a * QAOAE3Lin2.General.spin x b *
            QAOAE3Lin2.General.spin x c * (QAOAE3Lin2.General.spin x a *
            QAOAE3Lin2.General.spin x b * QAOAE3Lin2.General.spin x c) = _
          ring
      _ = 1 := by rw [q25_spin_sq, q25_spin_sq, q25_spin_sq]; norm_num
  have hflip : ∀ j x, p (q25flip j x) = (if j = a ∨ j = b ∨ j = c then (-1 : ℝ) else 1) * p x :=
    fun j x => q25_p_flip a b c hab hac hbc j x
  have hpF : ∀ y, p (F y) = -p y := by
    intro y
    show p (q25flip c (q25flip b (q25flip a y))) = -p y
    rw [hflip c, hflip b, hflip a]
    simp
  -- the two exponentials
  set E : Matrix (Qubits n) (Qubits n) ℂ :=
    NormedSpace.exp (-(Complex.I * ((Real.pi / 4 : ℝ) : ℂ)) • qaoaMixer n) with hEdef
  set EC : Matrix (Qubits n) (Qubits n) ℂ :=
    NormedSpace.exp (-(Complex.I * ((-γ : ℝ) : ℂ)) • problemHamiltonian C) with hECdef
  have hU : qaoaUnitary C 1 (fun _ => Real.pi / 4) (fun _ => -γ) = E * EC := by
    simp [qaoaUnitary, orderedProd, List.ofFn_succ, hEdef, hECdef]
  have hEunit : E ∈ Matrix.unitaryGroup (Qubits n) ℂ :=
    ct_exp_unitary _ (ct_skew _ (ct_mixer_herm n) _)
  have hEC : EC = Matrix.diagonal (fun x => Complex.exp (((γ * C x : ℝ) : ℂ) * Complex.I)) := by
    rw [hECdef]
    unfold problemHamiltonian
    rw [← Matrix.diagonal_smul, Matrix.exp_diagonal]
    congr 1
    funext x
    rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
    congr 1
    simp only [Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  -- the state before the mixer
  set r : ℝ := (Real.sqrt (Fintype.card (Qubits n)))⁻¹ with hr
  let s : Qubits n → ℂ := fun _ => ((Real.sqrt (Fintype.card (Qubits n)))⁻¹ : ℂ)
  let v : Qubits n → ℂ := EC *ᵥ s
  have hv : ∀ y, v y = Complex.exp (((γ * C y : ℝ) : ℂ) * Complex.I) * (r : ℂ) := by
    intro y
    show (EC *ᵥ s) y = _
    rw [hEC, Matrix.mulVec_diagonal]
    show _ * ((Real.sqrt (Fintype.card (Qubits n)))⁻¹ : ℂ) = _
    rw [hr]
    push_cast
    rfl
  -- the expectation as a sum of squared amplitudes
  have hcorr1 : QAOAE3Lin2.General.corr tri rhs i (-γ) (Real.pi / 4) =
      ∑ x, ‖(E *ᵥ v) x‖ ^ 2 * p x := by
    unfold QAOAE3Lin2.General.corr
    refine Finset.sum_congr rfl (fun x _ => ?_)
    congr 1
    unfold prob ket
    rw [EuclideanSpace.inner_single_left]
    have hst : (QAOAE3Lin2.General.qaoaState1 tri rhs (-γ) (Real.pi / 4)).ofLp x =
        (E *ᵥ v) x := by
      show ((qaoaUnitary C 1 (fun _ => Real.pi / 4) (fun _ => -γ)) *ᵥ s) x = (E *ᵥ (EC *ᵥ s)) x
      rw [hU, Matrix.mulVec_mulVec]
    simp only [map_one, one_mul]
    rw [hst]
  -- Heisenberg picture
  have hconj := q25_conj p hp a b c hab hac hbc hflip
  have hheis := q25_heis E ((Complex.I • q25X a) * (Complex.I • q25X b) * (Complex.I • q25X c)) p
    hEunit hconj v
  -- evaluate the right-hand side termwise
  have hterm : ∀ y, (((Complex.I • q25X a) * (Complex.I • q25X b) * (Complex.I • q25X c)) *ᵥ
      (Matrix.diagonal (fun x => ((p x : ℝ) : ℂ)) *ᵥ v)) y =
      Complex.I * (Complex.I * (Complex.I * (((-p y : ℝ) : ℂ) * v (F y)))) := by
    intro y
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, q25_IX_mulVec, q25_IX_mulVec,
      q25_IX_mulVec, Matrix.mulVec_diagonal]
    show Complex.I * (Complex.I * (Complex.I * (((p (F y) : ℝ) : ℂ) * v (F y)))) = _
    rw [hpF y]
  have hre : QAOAE3Lin2.General.corr tri rhs i (-γ) (Real.pi / 4) =
      ∑ y, (star (v y) * (Complex.I * (Complex.I * (Complex.I *
        (((-p y : ℝ) : ℂ) * v (F y)))))).re := by
    have h := congrArg Complex.re hheis
    rw [Complex.ofReal_re, ← hcorr1] at h
    rw [h, dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [hterm y, Pi.star_apply]
  rw [hre, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [hv y, hv (F y), q25_re_term r (p y) (γ * C y) (γ * C (F y))]
  have hN : (0 : ℝ) ≤ (Fintype.card (Qubits n) : ℝ) := Nat.cast_nonneg _
  have hrr : r * r = (Fintype.card (Qubits n) : ℝ)⁻¹ := by
    rw [hr, ← mul_inv, Real.mul_self_sqrt hN]
  rw [hrr, mul_sub]
  ring

open QAlgorithms

/-! ### Turning the classical objective into spin polynomials -/

/-- The indicator of one E3LIN2 equation is its usual affine spin polynomial. -/
theorem q25_clause_indicator (u v w d : Bool) :
    (if Bool.xor (Bool.xor u v) w = d then (1 : ℝ) else 0) =
      (1 + (if d then (-1 : ℝ) else 1) *
        ((if u then (-1 : ℝ) else 1) * (if v then (-1 : ℝ) else 1) *
          (if w then (-1 : ℝ) else 1))) / 2 := by
  cases u <;> cases v <;> cases w <;> cases d <;> norm_num

/-- The full objective is the sum of the affine spin polynomials of its clauses. -/
theorem q25_satCount_eq_sum {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n)
    (rhs : Fin m → Bool) (x : Qubits n) :
    QAOAE3Lin2.General.satCount tri rhs x =
      ∑ j, (1 + QAOAE3Lin2.General.sgn rhs j *
        (QAOAE3Lin2.General.spin x (tri j).1 *
          QAOAE3Lin2.General.spin x (tri j).2.1 *
          QAOAE3Lin2.General.spin x (tri j).2.2)) / 2 := by
  classical
  unfold QAOAE3Lin2.General.satCount
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun j _ ↦ ?_)
  simpa only [Nat.cast_one, QAOAE3Lin2.General.sgn, QAOAE3Lin2.General.spin] using
    q25_clause_indicator (x (tri j).1) (x (tri j).2.1) (x (tri j).2.2) (rhs j)

/-- Product of the three spins belonging to a clause. -/
def q25prod {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (j : Fin m)
    (x : Qubits n) : ℝ :=
  QAOAE3Lin2.General.spin x (tri j).1 * QAOAE3Lin2.General.spin x (tri j).2.1 *
    QAOAE3Lin2.General.spin x (tri j).2.2

/-- Flipping a bit negates a clause product exactly when that bit occurs in the clause. -/
theorem q25prod_flip {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n)
    (htri : QAOAE3Lin2.General.IsTripleFamily tri) (j : Fin m) (v : Fin n) (x : Qubits n) :
    q25prod tri j (q25flip v x) =
      (if QAOAE3Lin2.General.onTriple (tri j) v then (-1 : ℝ) else 1) * q25prod tri j x := by
  rcases htri.1 j with ⟨hab, hbc⟩
  have hab' : (tri j).1 ≠ (tri j).2.1 := ne_of_lt hab
  have hac' : (tri j).1 ≠ (tri j).2.2 := ne_of_lt (hab.trans hbc)
  have hbc' : (tri j).2.1 ≠ (tri j).2.2 := ne_of_lt hbc
  unfold q25prod
  rw [q25_p_flip (tri j).1 (tri j).2.1 (tri j).2.2 hab' hac' hbc' v x]
  simp only [QAOAE3Lin2.General.onTriple]

/-- A strictly increasing three-element tuple is determined by the three elements it contains. -/
theorem q25_sorted_triple_eq {n : ℕ} (s t : Fin n × Fin n × Fin n)
    (hs : s.1 < s.2.1 ∧ s.2.1 < s.2.2) (ht : t.1 < t.2.1 ∧ t.2.1 < t.2.2)
    (h0 : QAOAE3Lin2.General.onTriple t s.1)
    (h1 : QAOAE3Lin2.General.onTriple t s.2.1)
    (h2 : QAOAE3Lin2.General.onTriple t s.2.2) : t = s := by
  ext
  all_goals
    simp only [QAOAE3Lin2.General.onTriple] at h0 h1 h2
    rcases h0 with h0 | h0 | h0 <;>
      rcases h1 with h1 | h1 | h1 <;>
      rcases h2 with h2 | h2 | h2 <;> omega

theorem q25_sharesOnly_zero {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n)
    (i j : Fin m) :
    QAOAE3Lin2.General.sharesOnly tri i j 0 ↔
      j ≠ i ∧ QAOAE3Lin2.General.onTriple (tri j) (tri i).1 ∧
        ¬ QAOAE3Lin2.General.onTriple (tri j) (tri i).2.1 ∧
        ¬ QAOAE3Lin2.General.onTriple (tri j) (tri i).2.2 := by
  constructor
  · rintro ⟨hji, h0, hrest⟩
    refine ⟨hji, ?_, hrest 1 (by decide), hrest 2 (by decide)⟩
    simpa [QAOAE3Lin2.General.roleBit] using h0
  · rintro ⟨hji, h0, h1, h2⟩
    refine ⟨hji, ?_, ?_⟩
    · simpa [QAOAE3Lin2.General.roleBit] using h0
    · intro r hr
      fin_cases r
      · exact (hr rfl).elim
      · simpa [QAOAE3Lin2.General.roleBit] using h1
      · simpa [QAOAE3Lin2.General.roleBit] using h2

theorem q25_sharesOnly_one {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n)
    (i j : Fin m) :
    QAOAE3Lin2.General.sharesOnly tri i j 1 ↔
      j ≠ i ∧ ¬ QAOAE3Lin2.General.onTriple (tri j) (tri i).1 ∧
        QAOAE3Lin2.General.onTriple (tri j) (tri i).2.1 ∧
        ¬ QAOAE3Lin2.General.onTriple (tri j) (tri i).2.2 := by
  constructor
  · rintro ⟨hji, h1, hrest⟩
    refine ⟨hji, hrest 0 (by decide), ?_, hrest 2 (by decide)⟩
    simpa [QAOAE3Lin2.General.roleBit] using h1
  · rintro ⟨hji, h0, h1, h2⟩
    refine ⟨hji, ?_, ?_⟩
    · simpa [QAOAE3Lin2.General.roleBit] using h1
    · intro r hr
      fin_cases r
      · simpa [QAOAE3Lin2.General.roleBit] using h0
      · exact (hr rfl).elim
      · simpa [QAOAE3Lin2.General.roleBit] using h2

theorem q25_sharesOnly_two {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n)
    (i j : Fin m) :
    QAOAE3Lin2.General.sharesOnly tri i j 2 ↔
      j ≠ i ∧ ¬ QAOAE3Lin2.General.onTriple (tri j) (tri i).1 ∧
        ¬ QAOAE3Lin2.General.onTriple (tri j) (tri i).2.1 ∧
        QAOAE3Lin2.General.onTriple (tri j) (tri i).2.2 := by
  constructor
  · rintro ⟨hji, h2, hrest⟩
    refine ⟨hji, hrest 0 (by decide), hrest 1 (by decide), ?_⟩
    simpa [QAOAE3Lin2.General.roleBit] using h2
  · rintro ⟨hji, h0, h1, h2⟩
    refine ⟨hji, ?_, ?_⟩
    · simpa [QAOAE3Lin2.General.roleBit] using h2
    · intro r hr
      fin_cases r
      · simpa [QAOAE3Lin2.General.roleBit] using h0
      · simpa [QAOAE3Lin2.General.roleBit] using h1
      · exact (hr rfl).elim

/-- Contribution of one clause to the objective change after flipping the central triple. -/
theorem q25_clause_contribution {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n)
    (rhs : Fin m → Bool) (htri : QAOAE3Lin2.General.IsTripleFamily tri)
    (i j : Fin m) (x : Qubits n) :
    (1 + QAOAE3Lin2.General.sgn rhs j * q25prod tri j x) / 2 -
        (1 + QAOAE3Lin2.General.sgn rhs j * q25prod tri j
          (q25flip (tri i).2.2 (q25flip (tri i).2.1 (q25flip (tri i).1 x)))) / 2 =
      (if j = i then QAOAE3Lin2.General.sgn rhs i * q25prod tri i x else 0) +
      QAOAE3Lin2.General.spin x (tri i).1 *
        (if QAOAE3Lin2.General.sharesOnly tri i j 0 then
          QAOAE3Lin2.General.sgn rhs j *
            (q25prod tri j x * QAOAE3Lin2.General.spin x (tri i).1) else 0) +
      QAOAE3Lin2.General.spin x (tri i).2.1 *
        (if QAOAE3Lin2.General.sharesOnly tri i j 1 then
          QAOAE3Lin2.General.sgn rhs j *
            (q25prod tri j x * QAOAE3Lin2.General.spin x (tri i).2.1) else 0) +
      QAOAE3Lin2.General.spin x (tri i).2.2 *
        (if QAOAE3Lin2.General.sharesOnly tri i j 2 then
          QAOAE3Lin2.General.sgn rhs j *
            (q25prod tri j x * QAOAE3Lin2.General.spin x (tri i).2.2) else 0) := by
  have hji_iff : j = i ↔
      QAOAE3Lin2.General.onTriple (tri j) (tri i).1 ∧
      QAOAE3Lin2.General.onTriple (tri j) (tri i).2.1 ∧
      QAOAE3Lin2.General.onTriple (tri j) (tri i).2.2 := by
    constructor
    · rintro rfl
      simp [QAOAE3Lin2.General.onTriple]
    · rintro ⟨h0, h1, h2⟩
      apply htri.2
      exact q25_sorted_triple_eq (tri i) (tri j) (htri.1 i) (htri.1 j) h0 h1 h2
  have hcancel0 (A B : ℝ) :
      QAOAE3Lin2.General.spin x (tri i).1 *
        (A * (B * QAOAE3Lin2.General.spin x (tri i).1)) = A * B := by
    calc
      _ = A * B * (QAOAE3Lin2.General.spin x (tri i).1 *
          QAOAE3Lin2.General.spin x (tri i).1) := by ring
      _ = A * B := by rw [q25_spin_sq]; ring
  have hcancel1 (A B : ℝ) :
      QAOAE3Lin2.General.spin x (tri i).2.1 *
        (A * (B * QAOAE3Lin2.General.spin x (tri i).2.1)) = A * B := by
    calc
      _ = A * B * (QAOAE3Lin2.General.spin x (tri i).2.1 *
          QAOAE3Lin2.General.spin x (tri i).2.1) := by ring
      _ = A * B := by rw [q25_spin_sq]; ring
  have hcancel2 (A B : ℝ) :
      QAOAE3Lin2.General.spin x (tri i).2.2 *
        (A * (B * QAOAE3Lin2.General.spin x (tri i).2.2)) = A * B := by
    calc
      _ = A * B * (QAOAE3Lin2.General.spin x (tri i).2.2 *
          QAOAE3Lin2.General.spin x (tri i).2.2) := by ring
      _ = A * B := by rw [q25_spin_sq]; ring
  have hi0 : QAOAE3Lin2.General.onTriple (tri i) (tri i).1 := by
    simp [QAOAE3Lin2.General.onTriple]
  have hi1 : QAOAE3Lin2.General.onTriple (tri i) (tri i).2.1 := by
    simp [QAOAE3Lin2.General.onTriple]
  have hi2 : QAOAE3Lin2.General.onTriple (tri i) (tri i).2.2 := by
    simp [QAOAE3Lin2.General.onTriple]
  rw [q25prod_flip tri htri j (tri i).2.2,
    q25prod_flip tri htri j (tri i).2.1,
    q25prod_flip tri htri j (tri i).1]
  by_cases h0 : QAOAE3Lin2.General.onTriple (tri j) (tri i).1 <;>
    by_cases h1 : QAOAE3Lin2.General.onTriple (tri j) (tri i).2.1 <;>
    by_cases h2 : QAOAE3Lin2.General.onTriple (tri j) (tri i).2.2
  all_goals
    simp [h0, h1, h2] at hji_iff
    simp [q25_sharesOnly_zero, q25_sharesOnly_one, q25_sharesOnly_two,
      h0, h1, h2, hi0, hi1, hi2, hji_iff,
      hcancel0, hcancel1, hcancel2] <;> ring

/-- Flipping the central triple changes the objective by the central clause and the three
single-overlap polynomials. -/
theorem q25_satCount_diff {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n)
    (rhs : Fin m → Bool) (htri : QAOAE3Lin2.General.IsTripleFamily tri)
    (i : Fin m) (x : Qubits n) :
    QAOAE3Lin2.General.satCount tri rhs x -
        QAOAE3Lin2.General.satCount tri rhs
          (q25flip (tri i).2.2 (q25flip (tri i).2.1 (q25flip (tri i).1 x))) =
      QAOAE3Lin2.General.sgn rhs i * q25prod tri i x +
      QAOAE3Lin2.General.spin x (tri i).1 * QAOAE3Lin2.General.cPoly tri rhs i 0 x +
      QAOAE3Lin2.General.spin x (tri i).2.1 * QAOAE3Lin2.General.cPoly tri rhs i 1 x +
      QAOAE3Lin2.General.spin x (tri i).2.2 * QAOAE3Lin2.General.cPoly tri rhs i 2 x := by
  classical
  calc
    _ = ∑ j, ((1 + QAOAE3Lin2.General.sgn rhs j * q25prod tri j x) / 2 -
        (1 + QAOAE3Lin2.General.sgn rhs j * q25prod tri j
          (q25flip (tri i).2.2 (q25flip (tri i).2.1 (q25flip (tri i).1 x)))) / 2) := by
      rw [q25_satCount_eq_sum, q25_satCount_eq_sum, Finset.sum_sub_distrib]
      rfl
    _ = ∑ j,
        ((if j = i then QAOAE3Lin2.General.sgn rhs i * q25prod tri i x else 0) +
        QAOAE3Lin2.General.spin x (tri i).1 *
          (if QAOAE3Lin2.General.sharesOnly tri i j 0 then
            QAOAE3Lin2.General.sgn rhs j *
              (q25prod tri j x * QAOAE3Lin2.General.spin x (tri i).1) else 0) +
        QAOAE3Lin2.General.spin x (tri i).2.1 *
          (if QAOAE3Lin2.General.sharesOnly tri i j 1 then
            QAOAE3Lin2.General.sgn rhs j *
              (q25prod tri j x * QAOAE3Lin2.General.spin x (tri i).2.1) else 0) +
        QAOAE3Lin2.General.spin x (tri i).2.2 *
          (if QAOAE3Lin2.General.sharesOnly tri i j 2 then
            QAOAE3Lin2.General.sgn rhs j *
              (q25prod tri j x * QAOAE3Lin2.General.spin x (tri i).2.2) else 0)) := by
      refine Finset.sum_congr rfl (fun j _ ↦ ?_)
      exact q25_clause_contribution tri rhs htri i j x
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      simp [QAOAE3Lin2.General.cPoly, QAOAE3Lin2.General.roleBit, q25prod,
        Finset.mul_sum]

/-- A real sign can be moved inside a sine. -/
theorem q25_sign_mul_sin (s t : ℝ) (hs : s * s = 1) :
    s * Real.sin t = Real.sin (s * t) := by
  rcases mul_self_eq_one_iff.mp hs with rfl | rfl
  · simp
  · simp [Real.sin_neg]

/-- The correlation integrand in terms of the three pair-signs and the overlap polynomials. -/
theorem q25_integrand_eq {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n)
    (rhs : Fin m → Bool) (htri : QAOAE3Lin2.General.IsTripleFamily tri)
    (i : Fin m) (x : Qubits n) (γ : ℝ) :
    q25prod tri i x * Real.sin (γ * (QAOAE3Lin2.General.satCount tri rhs x -
      QAOAE3Lin2.General.satCount tri rhs
        (q25flip (tri i).2.2 (q25flip (tri i).2.1 (q25flip (tri i).1 x))))) =
    Real.sin (γ *
      (QAOAE3Lin2.General.sgn rhs i +
        (QAOAE3Lin2.General.spin x (tri i).2.1 * QAOAE3Lin2.General.spin x (tri i).2.2) *
          QAOAE3Lin2.General.cPoly tri rhs i 0 x +
        (QAOAE3Lin2.General.spin x (tri i).1 * QAOAE3Lin2.General.spin x (tri i).2.2) *
          QAOAE3Lin2.General.cPoly tri rhs i 1 x +
        (QAOAE3Lin2.General.spin x (tri i).1 * QAOAE3Lin2.General.spin x (tri i).2.1) *
          QAOAE3Lin2.General.cPoly tri rhs i 2 x)) := by
  have hp : q25prod tri i x * q25prod tri i x = 1 := by
    unfold q25prod
    calc
      _ = (QAOAE3Lin2.General.spin x (tri i).1 * QAOAE3Lin2.General.spin x (tri i).1) *
          (QAOAE3Lin2.General.spin x (tri i).2.1 * QAOAE3Lin2.General.spin x (tri i).2.1) *
          (QAOAE3Lin2.General.spin x (tri i).2.2 * QAOAE3Lin2.General.spin x (tri i).2.2) := by ring
      _ = 1 := by rw [q25_spin_sq, q25_spin_sq, q25_spin_sq]; norm_num
  have hp0 : q25prod tri i x * QAOAE3Lin2.General.spin x (tri i).1 =
      QAOAE3Lin2.General.spin x (tri i).2.1 * QAOAE3Lin2.General.spin x (tri i).2.2 := by
    unfold q25prod
    calc
      _ = (QAOAE3Lin2.General.spin x (tri i).1 * QAOAE3Lin2.General.spin x (tri i).1) *
          (QAOAE3Lin2.General.spin x (tri i).2.1 * QAOAE3Lin2.General.spin x (tri i).2.2) := by ring
      _ = _ := by rw [q25_spin_sq, one_mul]
  have hp1 : q25prod tri i x * QAOAE3Lin2.General.spin x (tri i).2.1 =
      QAOAE3Lin2.General.spin x (tri i).1 * QAOAE3Lin2.General.spin x (tri i).2.2 := by
    unfold q25prod
    calc
      _ = (QAOAE3Lin2.General.spin x (tri i).2.1 * QAOAE3Lin2.General.spin x (tri i).2.1) *
          (QAOAE3Lin2.General.spin x (tri i).1 * QAOAE3Lin2.General.spin x (tri i).2.2) := by ring
      _ = _ := by rw [q25_spin_sq, one_mul]
  have hp2 : q25prod tri i x * QAOAE3Lin2.General.spin x (tri i).2.2 =
      QAOAE3Lin2.General.spin x (tri i).1 * QAOAE3Lin2.General.spin x (tri i).2.1 := by
    unfold q25prod
    calc
      _ = (QAOAE3Lin2.General.spin x (tri i).2.2 * QAOAE3Lin2.General.spin x (tri i).2.2) *
          (QAOAE3Lin2.General.spin x (tri i).1 * QAOAE3Lin2.General.spin x (tri i).2.1) := by ring
      _ = _ := by rw [q25_spin_sq, one_mul]
  calc
    _ = Real.sin (q25prod tri i x * (γ *
        (QAOAE3Lin2.General.satCount tri rhs x -
          QAOAE3Lin2.General.satCount tri rhs
            (q25flip (tri i).2.2 (q25flip (tri i).2.1 (q25flip (tri i).1 x)))))) :=
      q25_sign_mul_sin _ _ hp
    _ = _ := by
      rw [q25_satCount_diff tri rhs htri i x]
      congr 1
      calc
        _ = γ * (QAOAE3Lin2.General.sgn rhs i *
              (q25prod tri i x * q25prod tri i x) +
            (q25prod tri i x * QAOAE3Lin2.General.spin x (tri i).1) *
              QAOAE3Lin2.General.cPoly tri rhs i 0 x +
            (q25prod tri i x * QAOAE3Lin2.General.spin x (tri i).2.1) *
              QAOAE3Lin2.General.cPoly tri rhs i 1 x +
            (q25prod tri i x * QAOAE3Lin2.General.spin x (tri i).2.2) *
              QAOAE3Lin2.General.cPoly tri rhs i 2 x) := by ring
        _ = _ := by rw [hp, hp0, hp1, hp2]; ring

theorem q25_cPoly_eq_sum {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n)
    (rhs : Fin m → Bool) (i : Fin m) (r : Fin 3) (x : Qubits n) :
    QAOAE3Lin2.General.cPoly tri rhs i r x =
      ∑ j, if QAOAE3Lin2.General.sharesOnly tri i j r then
        QAOAE3Lin2.General.sgn rhs j *
          (q25prod tri j x * QAOAE3Lin2.General.spin x
            (QAOAE3Lin2.General.roleBit (tri i) r))
      else 0 := by
  rfl

theorem q25_cPoly_flip_first {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n)
    (rhs : Fin m → Bool) (htri : QAOAE3Lin2.General.IsTripleFamily tri)
    (i : Fin m) (r : Fin 3) (x : Qubits n) :
    QAOAE3Lin2.General.cPoly tri rhs i r (q25flip (tri i).1 x) =
      QAOAE3Lin2.General.cPoly tri rhs i r x := by
  have hab : (tri i).1 ≠ (tri i).2.1 := ne_of_lt (htri.1 i).1
  have hac : (tri i).1 ≠ (tri i).2.2 := ne_of_lt ((htri.1 i).1.trans (htri.1 i).2)
  fin_cases r
  · change QAOAE3Lin2.General.cPoly tri rhs i 0 (q25flip (tri i).1 x) =
      QAOAE3Lin2.General.cPoly tri rhs i 0 x
    rw [q25_cPoly_eq_sum, q25_cPoly_eq_sum]
    refine Finset.sum_congr rfl (fun j _ ↦ ?_)
    by_cases hs : QAOAE3Lin2.General.sharesOnly tri i j 0
    · rw [if_pos hs, if_pos hs, q25prod_flip tri htri, q25_spin_flip]
      have hj := (q25_sharesOnly_zero tri i j).mp hs
      simp [QAOAE3Lin2.General.roleBit, hj.2.1]
    · simp [hs]
  · change QAOAE3Lin2.General.cPoly tri rhs i 1 (q25flip (tri i).1 x) =
      QAOAE3Lin2.General.cPoly tri rhs i 1 x
    rw [q25_cPoly_eq_sum, q25_cPoly_eq_sum]
    refine Finset.sum_congr rfl (fun j _ ↦ ?_)
    by_cases hs : QAOAE3Lin2.General.sharesOnly tri i j 1
    · rw [if_pos hs, if_pos hs, q25prod_flip tri htri, q25_spin_flip]
      have hj := (q25_sharesOnly_one tri i j).mp hs
      simp [QAOAE3Lin2.General.roleBit, hj.2.1, hab]
    · simp [hs]
  · change QAOAE3Lin2.General.cPoly tri rhs i 2 (q25flip (tri i).1 x) =
      QAOAE3Lin2.General.cPoly tri rhs i 2 x
    rw [q25_cPoly_eq_sum, q25_cPoly_eq_sum]
    refine Finset.sum_congr rfl (fun j _ ↦ ?_)
    by_cases hs : QAOAE3Lin2.General.sharesOnly tri i j 2
    · rw [if_pos hs, if_pos hs, q25prod_flip tri htri, q25_spin_flip]
      have hj := (q25_sharesOnly_two tri i j).mp hs
      simp [QAOAE3Lin2.General.roleBit, hj.2.1, hac]
    · simp [hs]

theorem q25_cPoly_flip_second {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n)
    (rhs : Fin m → Bool) (htri : QAOAE3Lin2.General.IsTripleFamily tri)
    (i : Fin m) (r : Fin 3) (x : Qubits n) :
    QAOAE3Lin2.General.cPoly tri rhs i r (q25flip (tri i).2.1 x) =
      QAOAE3Lin2.General.cPoly tri rhs i r x := by
  have hba : (tri i).2.1 ≠ (tri i).1 := (ne_of_lt (htri.1 i).1).symm
  have hbc : (tri i).2.1 ≠ (tri i).2.2 := ne_of_lt (htri.1 i).2
  fin_cases r
  · change QAOAE3Lin2.General.cPoly tri rhs i 0 (q25flip (tri i).2.1 x) =
      QAOAE3Lin2.General.cPoly tri rhs i 0 x
    rw [q25_cPoly_eq_sum, q25_cPoly_eq_sum]
    refine Finset.sum_congr rfl (fun j _ ↦ ?_)
    by_cases hs : QAOAE3Lin2.General.sharesOnly tri i j 0
    · rw [if_pos hs, if_pos hs, q25prod_flip tri htri, q25_spin_flip]
      have hj := (q25_sharesOnly_zero tri i j).mp hs
      simp [QAOAE3Lin2.General.roleBit, hj.2.2.1, hba]
    · simp [hs]
  · change QAOAE3Lin2.General.cPoly tri rhs i 1 (q25flip (tri i).2.1 x) =
      QAOAE3Lin2.General.cPoly tri rhs i 1 x
    rw [q25_cPoly_eq_sum, q25_cPoly_eq_sum]
    refine Finset.sum_congr rfl (fun j _ ↦ ?_)
    by_cases hs : QAOAE3Lin2.General.sharesOnly tri i j 1
    · rw [if_pos hs, if_pos hs, q25prod_flip tri htri, q25_spin_flip]
      have hj := (q25_sharesOnly_one tri i j).mp hs
      simp [QAOAE3Lin2.General.roleBit, hj.2.2.1]
    · simp [hs]
  · change QAOAE3Lin2.General.cPoly tri rhs i 2 (q25flip (tri i).2.1 x) =
      QAOAE3Lin2.General.cPoly tri rhs i 2 x
    rw [q25_cPoly_eq_sum, q25_cPoly_eq_sum]
    refine Finset.sum_congr rfl (fun j _ ↦ ?_)
    by_cases hs : QAOAE3Lin2.General.sharesOnly tri i j 2
    · rw [if_pos hs, if_pos hs, q25prod_flip tri htri, q25_spin_flip]
      have hj := (q25_sharesOnly_two tri i j).mp hs
      simp [QAOAE3Lin2.General.roleBit, hj.2.2.1, hbc]
    · simp [hs]

theorem q25_cPoly_flip_third {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n)
    (rhs : Fin m → Bool) (htri : QAOAE3Lin2.General.IsTripleFamily tri)
    (i : Fin m) (r : Fin 3) (x : Qubits n) :
    QAOAE3Lin2.General.cPoly tri rhs i r (q25flip (tri i).2.2 x) =
      QAOAE3Lin2.General.cPoly tri rhs i r x := by
  have hca : (tri i).2.2 ≠ (tri i).1 :=
    (ne_of_lt ((htri.1 i).1.trans (htri.1 i).2)).symm
  have hcb : (tri i).2.2 ≠ (tri i).2.1 := (ne_of_lt (htri.1 i).2).symm
  fin_cases r
  · change QAOAE3Lin2.General.cPoly tri rhs i 0 (q25flip (tri i).2.2 x) =
      QAOAE3Lin2.General.cPoly tri rhs i 0 x
    rw [q25_cPoly_eq_sum, q25_cPoly_eq_sum]
    refine Finset.sum_congr rfl (fun j _ ↦ ?_)
    by_cases hs : QAOAE3Lin2.General.sharesOnly tri i j 0
    · rw [if_pos hs, if_pos hs, q25prod_flip tri htri, q25_spin_flip]
      have hj := (q25_sharesOnly_zero tri i j).mp hs
      simp [QAOAE3Lin2.General.roleBit, hj.2.2.2, hca]
    · simp [hs]
  · change QAOAE3Lin2.General.cPoly tri rhs i 1 (q25flip (tri i).2.2 x) =
      QAOAE3Lin2.General.cPoly tri rhs i 1 x
    rw [q25_cPoly_eq_sum, q25_cPoly_eq_sum]
    refine Finset.sum_congr rfl (fun j _ ↦ ?_)
    by_cases hs : QAOAE3Lin2.General.sharesOnly tri i j 1
    · rw [if_pos hs, if_pos hs, q25prod_flip tri htri, q25_spin_flip]
      have hj := (q25_sharesOnly_one tri i j).mp hs
      simp [QAOAE3Lin2.General.roleBit, hj.2.2.2, hcb]
    · simp [hs]
  · change QAOAE3Lin2.General.cPoly tri rhs i 2 (q25flip (tri i).2.2 x) =
      QAOAE3Lin2.General.cPoly tri rhs i 2 x
    rw [q25_cPoly_eq_sum, q25_cPoly_eq_sum]
    refine Finset.sum_congr rfl (fun j _ ↦ ?_)
    by_cases hs : QAOAE3Lin2.General.sharesOnly tri i j 2
    · rw [if_pos hs, if_pos hs, q25prod_flip tri htri, q25_spin_flip]
      have hj := (q25_sharesOnly_two tri i j).mp hs
      simp [QAOAE3Lin2.General.roleBit, hj.2.2.2]
    · simp [hs]

/-- The pair-sign form of the correlation integrand. -/
noncomputable def q25g {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n)
    (rhs : Fin m → Bool) (i : Fin m) (γ : ℝ) (x : Qubits n) : ℝ :=
  Real.sin (γ *
    (QAOAE3Lin2.General.sgn rhs i +
      (QAOAE3Lin2.General.spin x (tri i).2.1 * QAOAE3Lin2.General.spin x (tri i).2.2) *
        QAOAE3Lin2.General.cPoly tri rhs i 0 x +
      (QAOAE3Lin2.General.spin x (tri i).1 * QAOAE3Lin2.General.spin x (tri i).2.2) *
        QAOAE3Lin2.General.cPoly tri rhs i 1 x +
      (QAOAE3Lin2.General.spin x (tri i).1 * QAOAE3Lin2.General.spin x (tri i).2.1) *
        QAOAE3Lin2.General.cPoly tri rhs i 2 x))

/-- The four fixed even-minus sign patterns in equation (25). -/
noncomputable def q25four {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n)
    (rhs : Fin m → Bool) (i : Fin m) (γ : ℝ) (x : Qubits n) : ℝ :=
  let d := QAOAE3Lin2.General.sgn rhs i
  let c₁ := QAOAE3Lin2.General.cPoly tri rhs i 0 x
  let c₂ := QAOAE3Lin2.General.cPoly tri rhs i 1 x
  let c₃ := QAOAE3Lin2.General.cPoly tri rhs i 2 x
  Real.sin (γ * (d + c₁ + c₂ + c₃)) + Real.sin (γ * (d + c₁ - c₂ - c₃)) +
    Real.sin (γ * (d - c₁ + c₂ - c₃)) + Real.sin (γ * (d - c₁ - c₂ + c₃))

/-- Flipping the first two central bits runs through all four even-minus pair-sign patterns. -/
theorem q25_orbit_pointwise {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n)
    (rhs : Fin m → Bool) (htri : QAOAE3Lin2.General.IsTripleFamily tri)
    (i : Fin m) (γ : ℝ) (x : Qubits n) :
    q25g tri rhs i γ x + q25g tri rhs i γ (q25flip (tri i).1 x) +
        q25g tri rhs i γ (q25flip (tri i).2.1 x) +
        q25g tri rhs i γ (q25flip (tri i).2.1 (q25flip (tri i).1 x)) =
      q25four tri rhs i γ x := by
  have hab : (tri i).1 ≠ (tri i).2.1 := ne_of_lt (htri.1 i).1
  have hac : (tri i).1 ≠ (tri i).2.2 := ne_of_lt ((htri.1 i).1.trans (htri.1 i).2)
  have hbc : (tri i).2.1 ≠ (tri i).2.2 := ne_of_lt (htri.1 i).2
  unfold q25g q25four
  simp only [q25_cPoly_flip_first tri rhs htri i,
    q25_cPoly_flip_second tri rhs htri i]
  simp only [q25_spin_flip, if_pos rfl, if_neg hab, if_neg hac, if_neg hbc,
    if_neg hab.symm, if_neg hac.symm, if_neg hbc.symm]
  by_cases ha : x (tri i).1 <;>
    by_cases hb : x (tri i).2.1 <;>
    by_cases hc : x (tri i).2.2
  all_goals
    simp [QAOAE3Lin2.General.spin, ha, hb, hc] <;> ring

/-- Reindexing a finite sum by a bit flip does not change it. -/
theorem q25_sum_flip {n : ℕ} (f : Qubits n → ℝ) (j : Fin n) :
    (∑ x, f (q25flip j x)) = ∑ x, f x := by
  simpa only [Function.Involutive.coe_toPerm] using
    (Equiv.sum_comp ((q25flip_invol j).toPerm (q25flip j)) f)

theorem q25_orbit_sum {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n)
    (rhs : Fin m → Bool) (htri : QAOAE3Lin2.General.IsTripleFamily tri)
    (i : Fin m) (γ : ℝ) :
    4 * ∑ x : Qubits n, q25g tri rhs i γ x =
      ∑ x : Qubits n, q25four tri rhs i γ x := by
  have hfirst : (∑ x : Qubits n, q25g tri rhs i γ (q25flip (tri i).1 x)) =
      ∑ x : Qubits n, q25g tri rhs i γ x :=
    q25_sum_flip (q25g tri rhs i γ) (tri i).1
  have hsecond : (∑ x : Qubits n, q25g tri rhs i γ (q25flip (tri i).2.1 x)) =
      ∑ x : Qubits n, q25g tri rhs i γ x :=
    q25_sum_flip (q25g tri rhs i γ) (tri i).2.1
  have hboth :
      (∑ x : Qubits n,
        q25g tri rhs i γ (q25flip (tri i).2.1 (q25flip (tri i).1 x))) =
      ∑ x : Qubits n, q25g tri rhs i γ x := by
    calc
      _ = ∑ x : Qubits n,
          q25g tri rhs i γ (q25flip (tri i).1 (q25flip (tri i).2.1 x)) := by
            refine Finset.sum_congr rfl (fun x _ ↦ ?_)
            rw [q25flip_comm]
      _ = ∑ x : Qubits n, q25g tri rhs i γ (q25flip (tri i).1 x) :=
        q25_sum_flip (fun y ↦ q25g tri rhs i γ (q25flip (tri i).1 y)) (tri i).2.1
      _ = _ := hfirst
  calc
    4 * ∑ x : Qubits n, q25g tri rhs i γ x =
        (∑ x : Qubits n, q25g tri rhs i γ x) +
        (∑ x : Qubits n, q25g tri rhs i γ (q25flip (tri i).1 x)) +
        (∑ x : Qubits n, q25g tri rhs i γ (q25flip (tri i).2.1 x)) +
        (∑ x : Qubits n,
          q25g tri rhs i γ (q25flip (tri i).2.1 (q25flip (tri i).1 x))) := by
            rw [hfirst, hsecond, hboth]
            ring
    _ = ∑ x : Qubits n,
        (q25g tri rhs i γ x + q25g tri rhs i γ (q25flip (tri i).1 x) +
          q25g tri rhs i γ (q25flip (tri i).2.1 x) +
          q25g tri rhs i γ (q25flip (tri i).2.1 (q25flip (tri i).1 x))) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = _ := by
      refine Finset.sum_congr rfl (fun x _ ↦ ?_)
      exact q25_orbit_pointwise tri rhs htri i γ x

open QAOAE3Lin2.General

theorem solution {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool)
    (htri : IsTripleFamily tri) (i : Fin m) (γ : ℝ) :
    (1 / 2) * sgn rhs i * corr tri rhs i (-γ) (Real.pi / 4) = clauseSin tri rhs i γ := by
  have hab : (tri i).1 ≠ (tri i).2.1 := ne_of_lt (htri.1 i).1
  have hac : (tri i).1 ≠ (tri i).2.2 := ne_of_lt ((htri.1 i).1.trans (htri.1 i).2)
  have hbc : (tri i).2.1 ≠ (tri i).2.2 := ne_of_lt (htri.1 i).2
  rw [q25_corr tri rhs i hab hac hbc γ]
  have hint :
      (∑ y : Qubits n,
        (spin y (tri i).1 * spin y (tri i).2.1 * spin y (tri i).2.2) *
          Real.sin (γ * (satCount tri rhs y - satCount tri rhs
            (q25flip (tri i).2.2 (q25flip (tri i).2.1 (q25flip (tri i).1 y)))))) =
      ∑ y : Qubits n, q25g tri rhs i γ y := by
    refine Finset.sum_congr rfl (fun y _ ↦ ?_)
    simpa [q25prod, q25g] using q25_integrand_eq tri rhs htri i y γ
  rw [hint]
  unfold clauseSin avgZ
  change (1 / 2) * sgn rhs i *
      ((Fintype.card (Qubits n) : ℝ)⁻¹ * ∑ x : Qubits n, q25g tri rhs i γ x) =
    (1 / 8) * sgn rhs i *
      ((Fintype.card (Qubits n) : ℝ)⁻¹ * ∑ x : Qubits n, q25four tri rhs i γ x)
  rw [← q25_orbit_sum tri rhs htri i γ]
  ring

