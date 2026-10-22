-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P23.polynomial_irrep_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T01:02:49.189893+00:00
-- url     : https://prove2.me/submissions/0195df24-0162-4e77-9304-15e0c4a42730

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23
noncomputable section

open QAlgorithms.Papers.Independent.Gap48.P23

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Exact frozen coordinate helpers; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)


def g74g_mu (l : ℕ) (v : Fin 2 → ℂ) : Fin (l+1) → ℂ :=
  fun k => (Real.sqrt (l.choose k.val : ℝ) : ℂ) * v 0 ^ (l - k.val) * v 1 ^ k.val

theorem g74g_coef_real (l j r s : ℕ) (hj : j ≤ l) (hr : r ≤ l - j) (hs : s ≤ j) :
    Real.sqrt ((Nat.factorial j : ℝ) * Nat.factorial (l - j) * Nat.factorial (l - r - s) *
      Nat.factorial (l - (l - r - s))) * Real.sqrt (l.choose (l - r - s) : ℝ) =
    Real.sqrt (l.choose j : ℝ) * (l-j).choose r * j.choose s *
      ((Nat.factorial r : ℝ) * Nat.factorial (l - j - r) * Nat.factorial s *
        Nat.factorial (j - s)) := by
  have hk : l - r - s ≤ l := by omega
  set k := l - r - s
  have e1 := Nat.choose_mul_factorial_mul_factorial hr
  have e2 := Nat.choose_mul_factorial_mul_factorial hs
  have e3 := Nat.choose_mul_factorial_mul_factorial hk
  have e4 := Nat.choose_mul_factorial_mul_factorial hj
  set G : ℝ := (Nat.factorial j : ℝ) * Nat.factorial (l - j) with hG
  have hGpos : 0 < G := by positivity
  have hK : (0:ℝ) < (Nat.factorial k : ℝ) * Nat.factorial (l - k) := by positivity
  -- RHS scalar
  have hR : ((l-j).choose r : ℝ) * j.choose s * ((Nat.factorial r : ℝ) * Nat.factorial (l - j - r) *
      Nat.factorial s * Nat.factorial (j - s)) = G := by
    rw [hG, ← e1, ← e2]; push_cast; ring
  rw [show Real.sqrt (l.choose j : ℝ) * ((l-j).choose r : ℝ) * (j.choose s : ℝ) *
      ((Nat.factorial r : ℝ) * Nat.factorial (l - j - r) * Nat.factorial s * Nat.factorial (j - s)) =
      Real.sqrt (l.choose j : ℝ) * (((l-j).choose r : ℝ) * (j.choose s : ℝ) *
      ((Nat.factorial r : ℝ) * Nat.factorial (l - j - r) * Nat.factorial s * Nat.factorial (j - s))) by ring, hR]
  rw [show (Nat.factorial j : ℝ) * Nat.factorial (l - j) * Nat.factorial k * Nat.factorial (l - k) =
      G * ((Nat.factorial k : ℝ) * Nat.factorial (l - k)) by rw [hG]; ring]
  have hCk : (l.choose k : ℝ) = (Nat.factorial l : ℝ) / ((Nat.factorial k : ℝ) * Nat.factorial (l - k)) := by
    rw [← e3]; push_cast; field_simp
  have hCj : (l.choose j : ℝ) = (Nat.factorial l : ℝ) / G := by
    rw [hG, ← e4]; push_cast; field_simp
  rw [hCk, hCj, ← Real.sqrt_mul (by positivity)]
  rw [show G * (↑k.factorial * ↑(l - k).factorial) * (↑l.factorial / (↑k.factorial * ↑(l - k).factorial))
      = (↑l.factorial / G) * G^2 by field_simp]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hGpos.le]

theorem g74g_mulVec (l : ℕ) (M : Op (Fin 2)) (v : Fin 2 → ℂ) :
    (polynomialIrrep l M) *ᵥ (g74g_mu l v) = g74g_mu l (M *ᵥ v) := by
  funext j
  have hJ : j.val ≤ l := by omega
  set J := j.val with hJdef
  set f : ℕ → ℕ → ℂ := fun k r => if r + J ≤ l ∧ r + k ≤ l ∧ l ≤ J + k + r then
    (Real.sqrt ((Nat.factorial J : ℝ) * Nat.factorial (l - J) * Nat.factorial k *
      Nat.factorial (l - k)) : ℂ) *
      (M 0 0 ^ r * M 0 1 ^ (l - J - r) * M 1 0 ^ (l - k - r) * M 1 1 ^ (J + k + r - l) /
          ((Nat.factorial r : ℂ) * Nat.factorial (l - J - r) *
            Nat.factorial (l - k - r) * Nat.factorial (J + k + r - l))) *
      ((Real.sqrt (l.choose k : ℝ) : ℂ) * v 0 ^ (l - k) * v 1 ^ k) else 0 with hf
  have step1 : ((polynomialIrrep l M) *ᵥ (g74g_mu l v)) j =
      ∑ k ∈ Finset.range (l+1), ∑ r ∈ Finset.range (l+1), f k r := by
    simp only [Matrix.mulVec, dotProduct, polynomialIrrep, g74g_mu]
    rw [← Fin.sum_univ_eq_sum_range (fun k => ∑ r ∈ Finset.range (l+1), f k r)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [hf]
    split_ifs with h
    · rfl
    · simp
  rw [step1, Finset.sum_comm]
  rw [← Finset.sum_subset (s₁ := Finset.range (l - J + 1)) (s₂ := Finset.range (l+1))]
  rotate_left
  · intro r; simp only [Finset.mem_range]; omega
  · intro r _ hr
    simp only [Finset.mem_range] at hr
    refine Finset.sum_eq_zero fun k _ => ?_
    simp only [hf]; rw [if_neg (by omega)]
  -- RHS
  simp only [g74g_mu, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [add_pow, add_pow]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm (s := Finset.range (J+1))]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Finset.mem_range] at hr
  have himg : ∀ s ∈ Finset.range (J+1), ∀ t ∈ Finset.range (J+1),
      l - r - s = l - r - t → s = t := by
    intro s hs t ht h; simp only [Finset.mem_range] at hs ht; omega
  rw [← Finset.sum_subset (s₁ := (Finset.range (J+1)).image (fun s => l - r - s))
    (s₂ := Finset.range (l+1)), Finset.sum_image himg]
  rotate_left
  · intro k; simp only [Finset.mem_image, Finset.mem_range]; omega
  · intro k _ hk
    simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and] at hk
    simp only [hf]
    rw [if_neg]
    intro h
    exact hk (l - r - k) (by omega) (by omega)
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [Finset.mem_range] at hs
  have hs' : s ≤ J := by omega
  have hr' : r ≤ l - J := by omega
  simp only [hf]
  rw [if_pos (by omega)]
  have hc := congrArg (fun x : ℝ => (x : ℂ)) (g74g_coef_real l J r s hJ hr' hs')
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast] at hc
  rw [show l - (l - r - s) - r = s by omega, show J + (l - r - s) + r - l = J - s by omega,
    show l - (l - r - s) = r + s by omega,
    show l - r - s = (l - J - r) + (J - s) by omega]
  rw [show l - (l - r - s) = r + s by omega, show l - r - s = (l - J - r) + (J - s) by omega] at hc
  have hden : ((Nat.factorial r : ℂ) * Nat.factorial (l - J - r) * Nat.factorial s *
      Nat.factorial (J - s)) ≠ 0 := by positivity
  rw [mul_pow, mul_pow, mul_pow, mul_pow, pow_add, pow_add]
  field_simp
  linear_combination (M 0 0 ^ r * M 0 1 ^ (l - J - r) * M 1 0 ^ s * M 1 1 ^ (J - s) *
    (v 0 ^ r * v 0 ^ s) * (v 1 ^ (l - J - r) * v 1 ^ (J - s))) * hc

theorem g74g_ext (l : ℕ) (X Y : Op (Fin (l+1)))
    (h : ∀ v : Fin 2 → ℂ, X *ᵥ g74g_mu l v = Y *ᵥ g74g_mu l v) : X = Y := by
  ext j k
  have hrow : ∀ t : ℂ, ∑ i : Fin (l+1), (X j i - Y j i) * (Real.sqrt (l.choose i.val : ℝ) : ℂ) * t ^ i.val = 0 := by
    intro t
    have := congrFun (h ![1, t]) j
    simp only [Matrix.mulVec, dotProduct, g74g_mu] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, mul_one] at this
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  set p : Polynomial ℂ := ∑ i : Fin (l+1),
    Polynomial.C ((X j i - Y j i) * (Real.sqrt (l.choose i.val : ℝ) : ℂ)) * Polynomial.X ^ i.val with hp
  have hp0 : p = 0 := by
    apply Polynomial.funext
    intro t
    rw [hp, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_zero]
    exact hrow t
  have hcoef := congrArg (fun q => Polynomial.coeff q k.val) hp0
  simp only [hp, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hcoef
  rw [Finset.sum_eq_single k] at hcoef
  · rw [if_pos rfl] at hcoef
    have hne : (Real.sqrt (l.choose k.val : ℝ) : ℂ) ≠ 0 := by
      have : 0 < Real.sqrt (l.choose k.val : ℝ) := Real.sqrt_pos.mpr (by
        exact_mod_cast Nat.choose_pos (by omega))
      exact_mod_cast this.ne'
    have := (mul_eq_zero.mp hcoef).resolve_right hne
    exact sub_eq_zero.mp this
  · intro b _ hb
    rw [if_neg (fun h => hb (Fin.ext h.symm))]
  · simp

theorem g74g_mu_smul (l : ℕ) (z : ℂ) (v : Fin 2 → ℂ) :
    g74g_mu l (z • v) = z ^ l • g74g_mu l v := by
  funext k
  have hk : k.val ≤ l := by omega
  simp only [g74g_mu, Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [show z ^ l = z ^ (l - k.val) * z ^ k.val by rw [← pow_add]; congr 1; omega]
  ring

theorem g74g_mul (l : ℕ) (A B : Op (Fin 2)) :
    polynomialIrrep l (A * B) = polynomialIrrep l A * polynomialIrrep l B := by
  apply g74g_ext; intro v
  rw [g74g_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, g74g_mulVec, g74g_mulVec]

theorem g74g_smul (l : ℕ) (z : ℂ) (M : Op (Fin 2)) :
    polynomialIrrep l (z • M) = z ^ l • polynomialIrrep l M := by
  apply g74g_ext; intro v
  rw [g74g_mulVec, Matrix.smul_mulVec, g74g_mu_smul, Matrix.smul_mulVec, g74g_mulVec]

theorem g74g_one (l : ℕ) : polynomialIrrep l 1 = 1 := by
  apply g74g_ext; intro v
  rw [g74g_mulVec, Matrix.one_mulVec, Matrix.one_mulVec]

theorem g74g_diag (l : ℕ) (a d : ℂ) : polynomialIrrep l (Matrix.diagonal ![a,d]) =
      Matrix.diagonal (fun k : Fin (l+1) => a^(l-k.val)*d^k.val) := by
  apply g74g_ext; intro v
  rw [g74g_mulVec]
  funext k
  simp only [g74g_mu, Matrix.mulVec_diagonal, Matrix.cons_val_zero, Matrix.cons_val_one, mul_pow]
  ring

theorem g74g_single (l : ℕ) : polynomialIrrep l (Matrix.single 0 0 1) = Matrix.single 0 0 1 := by
  apply g74g_ext; intro v
  rw [g74g_mulVec]
  funext k
  simp only [g74g_mu, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.single_apply]
  by_cases hk : k = 0
  · subst hk
    simp
  · have hk' : k.val ≠ 0 := fun h => hk (Fin.ext h)
    simp [Ne.symm hk, zero_pow hk']

theorem g74g_transpose (l : ℕ) (M : Op (Fin 2)) :
    polynomialIrrep l M.transpose = (polynomialIrrep l M).transpose := by
  ext j k
  simp only [polynomialIrrep, Matrix.transpose_apply]
  congr 1
  · congr 2; ring
  · refine Finset.sum_congr rfl fun r _ => ?_
    by_cases h : r + j.val ≤ l ∧ r + k.val ≤ l ∧ l ≤ j.val + k.val + r
    · rw [if_pos h, if_pos ⟨h.2.1, h.1, by omega⟩, show k.val + j.val + r - l = j.val + k.val + r - l by omega]
      ring
    · rw [if_neg h, if_neg (by omega)]

theorem g74g_conj (l : ℕ) (M : Op (Fin 2)) :
    polynomialIrrep l (fun i j => conj (M i j)) = (fun i j => conj (polynomialIrrep l M i j)) := by
  funext j k
  simp only [polynomialIrrep, map_mul, map_sum, Complex.conj_ofReal]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs
  · simp [map_div₀, map_mul, map_pow, map_natCast]
  · simp

theorem g74g_conjTranspose (l : ℕ) (M : Op (Fin 2)) :
    polynomialIrrep l Mᴴ = (polynomialIrrep l M)ᴴ := by
  set C : Op (Fin 2) := fun i j => conj (M i j) with hC
  have h1 : Mᴴ = C.transpose := Matrix.ext fun i j => rfl
  rw [h1, g74g_transpose, hC, g74g_conj]
  exact Matrix.ext fun i j => rfl

theorem g74g_stepA {n : ℕ} (S : Submodule ℂ (Fin n → ℂ)) (lam : Fin n → ℂ)
    (hlam : Function.Injective lam) (hS : ∀ v ∈ S, (fun k => lam k * v k) ∈ S) :
    ∀ v ∈ S, ∀ j, v j ≠ 0 → Pi.single j 1 ∈ S := by
  suffices H : ∀ m : ℕ, ∀ v ∈ S, (Finset.univ.filter (fun k => v k ≠ 0)).card ≤ m →
      ∀ j, v j ≠ 0 → Pi.single j 1 ∈ S by
    intro v hv j hj; exact H _ v hv le_rfl j hj
  intro m
  induction m with
  | zero =>
    intro v _ hc j hj
    have : j ∈ Finset.univ.filter (fun k => v k ≠ 0) := by simp [hj]
    rw [Nat.le_zero, Finset.card_eq_zero] at hc
    rw [hc] at this; simp at this
  | succ m ih =>
    intro v hv hc j hj
    by_cases h : ∃ i, i ≠ j ∧ v i ≠ 0
    · obtain ⟨i, hij, hi⟩ := h
      set w : Fin n → ℂ := (fun k => lam k * v k) - lam i • v with hw
      have hwS : w ∈ S := S.sub_mem (hS v hv) (S.smul_mem _ hv)
      have hwk : ∀ k, w k = (lam k - lam i) * v k := by
        intro k; simp [hw]; ring
      apply ih w hwS _ j
      · rw [hwk]
        exact mul_ne_zero (sub_ne_zero.mpr (fun e => hij (hlam e).symm)) hj
      · have hsub : Finset.univ.filter (fun k => w k ≠ 0) ⊆
            (Finset.univ.filter (fun k => v k ≠ 0)).erase i := by
          intro k hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hwk] at hk
          simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨?_, right_ne_zero_of_mul hk⟩
          rintro rfl; simp at hk
        have hmem : i ∈ Finset.univ.filter (fun k => v k ≠ 0) := by simp [hi]
        have := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hmem] at this
        omega
    · push Not at h
      have : (v j)⁻¹ • v = Pi.single j 1 := by
        funext k
        by_cases hk : k = j
        · subst hk; simp [hj]
        · simp [hk, h k hk]
      rw [← this]; exact S.smul_mem _ hv

theorem g74g_mu_e0 (l : ℕ) : g74g_mu l ![1, 0] = Pi.single 0 1 := by
  funext k
  by_cases hk : k = 0
  · subst hk; simp [g74g_mu]
  · have hk' : k.val ≠ 0 := fun h => hk (Fin.ext h)
    simp [g74g_mu, hk, zero_pow hk']

theorem g74g_mu_ne (l : ℕ) (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (k : Fin (l+1)) :
    g74g_mu l ![a, b] k ≠ 0 := by
  simp only [g74g_mu, Matrix.cons_val_zero, Matrix.cons_val_one]
  have : (Real.sqrt (l.choose k.val : ℝ) : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt (l.choose k.val : ℝ) := Real.sqrt_pos.mpr (by
      exact_mod_cast Nat.choose_pos (by omega))
    exact_mod_cast this.ne'
  exact mul_ne_zero (mul_ne_zero this (pow_ne_zero _ ha)) (pow_ne_zero _ hb)

theorem g74g_lam_inj (l : ℕ) :
    Function.Injective (fun k : Fin (l+1) =>
      Complex.exp (Complex.I * (Real.pi / (2 * (l + 1)) : ℝ)) ^ (l - k.val) *
      (conj (Complex.exp (Complex.I * (Real.pi / (2 * (l + 1)) : ℝ)))) ^ k.val) := by
  intro i j hij
  set θ : ℝ := Real.pi / (2 * (l + 1)) with hθ
  have hconj : conj (Complex.exp (Complex.I * (θ:ℂ))) = Complex.exp (-(Complex.I * (θ:ℂ))) := by
    rw [← Complex.exp_conj]; congr 1; simp [Complex.conj_ofReal]
  simp only [hconj, ← Complex.exp_nat_mul] at hij
  rw [← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int] at hij
  obtain ⟨n, hn⟩ := hij
  have him := congrArg Complex.im hn
  have hi : i.val ≤ l := by omega
  have hj : j.val ≤ l := by omega
  simp only [Complex.add_im, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_im,
    Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.ofReal_ofNat,
    Complex.re_ofNat, Complex.im_ofNat, Complex.neg_re] at him
  rw [Nat.cast_sub hi, Nat.cast_sub hj] at him
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [hθ] at him
  field_simp at him
  have hz : ((j.val : ℤ) - i.val) = 2 * n * (l + 1) := by
    have : ((j.val : ℝ) - i.val) = 2 * n * (l + 1) := by nlinarith
    exact_mod_cast this
  apply Fin.ext
  rcases lt_trichotomy n 0 with h | h | h
  · nlinarith
  · subst h; omega
  · nlinarith

/-- PDF p.60, Lemma C.2: no nontrivial invariant complex subspace for the
concrete SU(2) action, including the one-dimensional ell=0 representation. -/
theorem solution (ell : ℕ)
    (S : Submodule ℂ (Fin (ell+1) → ℂ))
    (hS : ∀ U : Matrix.unitaryGroup (Fin 2) ℂ, U.val.det = 1 →
      ∀ v ∈ S, (polynomialIrrep ell U.val).mulVec v ∈ S) : S = ⊥ ∨ S = ⊤ := by
  by_cases hbot : S = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨v, hvS, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h; push Not at h; exact hv0 (funext h)
  -- diagonal element
  set θ : ℝ := Real.pi / (2 * (ell + 1)) with hθ
  set z : ℂ := Complex.exp (Complex.I * (θ : ℂ)) with hz
  have hzz : conj z * z = 1 := by
    rw [hz, ← Complex.exp_conj, ← Complex.exp_add]
    rw [show (starRingEnd ℂ) (Complex.I * (θ:ℂ)) + Complex.I * θ = 0 by
      simp [Complex.conj_ofReal]]
    simp
  have hzz' : z * conj z = 1 := by rw [mul_comm]; exact hzz
  set D : Op (Fin 2) := Matrix.diagonal ![z, conj z] with hD
  have hDU : D ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, hD, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext i; fin_cases i
    · simp [hzz']
    · simp [hzz]
  have hDdet : D.det = 1 := by
    rw [hD, Matrix.det_diagonal, Fin.prod_univ_two]; simp [hzz']
  have hA : ∀ w ∈ S, ∀ i, w i ≠ 0 → Pi.single i 1 ∈ S := by
    apply g74g_stepA S _ (g74g_lam_inj ell)
    intro w hw
    have := hS ⟨D, hDU⟩ hDdet w hw
    simp only [hD, g74g_diag] at this
    have e : (Matrix.diagonal (fun k : Fin (ell+1) => z ^ (ell - k.val) * (conj z) ^ k.val) *ᵥ w) =
        fun k => (z ^ (ell - k.val) * (conj z) ^ k.val) * w k := funext (Matrix.mulVec_diagonal _ w)
    rw [e] at this
    exact this
  have hej := hA v hvS j hj
  -- rotation
  set c : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) with hc
  have hc2 : c * c = 1/2 := by
    rw [hc, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]; push_cast; ring
  have hc0 : c ≠ 0 := by
    rw [hc]; exact_mod_cast inv_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num))
  have hcc : conj c = c := by rw [hc, Complex.conj_ofReal]
  set R : Op (Fin 2) := !![c, -c; c, c] with hR
  have hRU : R ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    ext a b; fin_cases a <;> fin_cases b <;>
      simp [hR, Matrix.mul_apply, Fin.sum_univ_two, hcc, hc2] <;> ring_nf <;> simp [sq, hc2] <;> norm_num
  have hRdet : R.det = 1 := by
    rw [hR, Matrix.det_fin_two_of]; rw [show c * c - -c * c = 2 * (c*c) by ring, hc2]; norm_num
  -- e_0 ∈ S
  have he0 : Pi.single 0 1 ∈ S := by
    have hw := hS ⟨R, hRU⟩ hRdet _ hej
    apply hA _ hw 0
    have : (polynomialIrrep ell R *ᵥ Pi.single j 1) 0 = polynomialIrrep ell R 0 j := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    simp only at this ⊢
    rw [this]
    have h2 : polynomialIrrep ell R 0 j = (polynomialIrrep ell R.transpose) j 0 := by
      rw [g74g_transpose]; rfl
    have h3 : (polynomialIrrep ell R.transpose) j 0 =
        (polynomialIrrep ell R.transpose *ᵥ g74g_mu ell ![1,0]) j := by
      rw [g74g_mu_e0]; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [h2, h3, g74g_mulVec]
    have h4 : R.transpose *ᵥ ![1,0] = ![c, -c] := by
      funext i; fin_cases i <;> simp [hR, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [h4]
    exact g74g_mu_ne ell c (-c) hc0 (neg_ne_zero.mpr hc0) j
  -- all basis vectors
  have hall : ∀ k, Pi.single k 1 ∈ S := by
    intro k
    have hw := hS ⟨R, hRU⟩ hRdet _ he0
    apply hA _ hw k
    simp only
    rw [← g74g_mu_e0, g74g_mulVec]
    have h4 : R *ᵥ ![1,0] = ![c, c] := by
      funext i; fin_cases i <;> simp [hR, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [h4]
    exact g74g_mu_ne ell c c hc0 hc0 k
  rw [eq_top_iff]
  intro x _
  rw [← Finset.univ_sum_single x]
  apply Submodule.sum_mem
  intro i _
  have : Pi.single i (x i) = x i • (Pi.single i 1 : Fin (ell+1) → ℂ) := by
    funext k; by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  rw [this]
  exact S.smul_mem _ (hall i)


end
