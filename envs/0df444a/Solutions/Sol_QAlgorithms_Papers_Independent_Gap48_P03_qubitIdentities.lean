-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P03.qubitIdentities
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T22:39:39.560004+00:00
-- url     : https://prove2.me/submissions/4d304aeb-6ccd-4fb9-a9e9-d17fadefdc23

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P03
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P03

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage depolarizing)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy holevo IsLaw)

open QAlgorithms.Papers.Independent.Information100.P63 (schatten block)

open QAlgorithms.Papers.Independent.Information100.P67 (mapFirst)

open QAlgorithms.Papers.Independent.Claimed50.P43 (ordinaryLimit)

open QAlgorithms.Papers.Independent.Next46.P42 (minimumOutputEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

theorem g73j_clock_entry (d : ℕ) [NeZero d] (k : Fin d) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((k.val + 1 : ℕ) : ℂ) / (d : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I / d) ^ (k.val + 1) := by
  rw [← Complex.exp_nat_mul]; congr 1; ring

theorem g73j_clock_eq (d : ℕ) [NeZero d] :
    clockUnitary d = Matrix.diagonal (fun k : Fin d =>
      Complex.exp (2 * Real.pi * Complex.I / d) ^ (k.val + 1)) := by
  unfold clockUnitary; congr 1; funext k; exact g73j_clock_entry d k

theorem g73j_root_sum (d : ℕ) [NeZero d] (i j : Fin d) :
    ∑ k : Fin d, (starRingEnd ℂ (Complex.exp (2 * Real.pi * Complex.I / d) ^ (i.val + 1))) ^ (k.val + 1) *
      (Complex.exp (2 * Real.pi * Complex.I / d) ^ (j.val + 1)) ^ (k.val + 1) =
      if i = j then (d : ℂ) else 0 := by
  have hd : d ≠ 0 := NeZero.ne d
  set ζ := Complex.exp (2 * Real.pi * Complex.I / d) with hζ
  have hprim : IsPrimitiveRoot ζ d := Complex.isPrimitiveRoot_exp d hd
  have hn : ‖ζ‖ = 1 := hprim.norm'_eq_one hd
  have hne : ζ ≠ 0 := hprim.ne_zero hd
  have hconj : starRingEnd ℂ ζ = ζ⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn]; simp
  set x := ζ⁻¹ ^ (i.val + 1) * ζ ^ (j.val + 1) with hx
  have hterm : ∀ k : Fin d, (starRingEnd ℂ (ζ ^ (i.val + 1))) ^ (k.val + 1) *
      (ζ ^ (j.val + 1)) ^ (k.val + 1) = x ^ (k.val + 1) := by
    intro k; rw [map_pow, hconj, hx, mul_pow]
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  have hxi : x = ζ ^ j.val * (ζ ^ i.val)⁻¹ := by
    rw [hx, inv_pow, pow_succ, pow_succ]; field_simp
  rw [Fin.sum_univ_eq_sum_range (fun k => x ^ (k + 1)) d]
  split_ifs with hij
  · subst hij
    have : x = 1 := by rw [hxi]; field_simp
    simp [this]
  · have hx1 : x ≠ 1 := by
      intro h1
      rw [hxi] at h1
      have : ζ ^ j.val = ζ ^ i.val := by
        have hz : ζ ^ i.val ≠ 0 := pow_ne_zero _ hne
        field_simp at h1; exact h1
      exact hij (Fin.ext (hprim.pow_inj i.isLt j.isLt this.symm))
    have hxd : x ^ d = 1 := by
      rw [hxi, mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm j.val, mul_comm i.val,
        pow_mul, pow_mul, hprim.pow_eq_one]; simp
    have hg := geom_sum_mul x d
    rw [hxd, sub_self] at hg
    have hs : ∑ k ∈ Finset.range d, x ^ k = 0 := by
      rcases mul_eq_zero.1 hg with h | h
      · exact h
      · exact absurd (sub_eq_zero.1 h) hx1
    simp_rw [pow_succ, ← Finset.sum_mul, hs, zero_mul]

theorem g73j_depol_entry (d : ℕ) (p : ℝ) (X : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    QAlgorithms.Papers.Independent.Information100.P08.depolarizing d p X i j =
      ((1 - p : ℝ) : ℂ) * X i j + (p : ℂ) * X.trace * (d : ℂ)⁻¹ * (if i = j then 1 else 0) := by
  simp only [QAlgorithms.Papers.Independent.Information100.P08.depolarizing,
    QAlgorithms.Papers.Independent.Information100.P08.maximallyMixed, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, Complex.real_smul, smul_eq_mul]
  push_cast; split_ifs <;> ring

theorem g73j_inter_entry (d : ℕ) [NeZero d] (lam : ℝ) (X : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    intermediateChannel d lam X i j =
      QAlgorithms.Papers.Independent.Information100.P08.depolarizing d (1 - lam) X i j +
        (((1 - lam) / d : ℝ) : ℂ) * (if i = j then 0 else X i j) := by
  simp only [intermediateChannel, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.diagonal_apply, smul_eq_mul]
  split_ifs with h
  · subst h; simp
  · simp

theorem g73j_clock_sum (d : ℕ) [NeZero d] (Y : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    (∑ k : Fin d, conjSuperop ((clockUnitary d ^ (k.val + 1))ᴴ) Y) i j =
      Y i j * (if i = j then (d : ℂ) else 0) := by
  rw [Matrix.sum_apply]
  have h : ∀ k : Fin d, conjSuperop ((clockUnitary d ^ (k.val + 1))ᴴ) Y i j =
      Y i j * ((starRingEnd ℂ (Complex.exp (2 * Real.pi * Complex.I / d) ^ (i.val + 1))) ^ (k.val + 1) *
      (Complex.exp (2 * Real.pi * Complex.I / d) ^ (j.val + 1)) ^ (k.val + 1)) := by
    intro k
    simp only [conjSuperop, g73j_clock_eq, Matrix.diagonal_pow, Matrix.diagonal_conjTranspose,
      Matrix.conjTranspose_conjTranspose, Matrix.diagonal_mul, Matrix.mul_diagonal, Pi.pow_apply,
      Pi.star_apply, RCLike.star_def, map_pow, Complex.conj_conj]
    ring
  rw [Finset.sum_congr rfl (fun k _ => h k), ← Finset.mul_sum, g73j_root_sum]


theorem g73j_nt (d : ℤ) (hd : 0 < d) (i j l m : ℤ) (hi1 : 1 ≤ i) (hi2 : i ≤ d) (hj1 : 1 ≤ j)
    (hj2 : j ≤ d) (hl1 : 1 ≤ l) (hl2 : l ≤ d) (hm1 : 1 ≤ m) (hm2 : m ≤ d)
    (h1 : d ∣ i - j - l + m) (h2 : 2 * d ^ 2 ∣ i ^ 2 - j ^ 2 - l ^ 2 + m ^ 2) :
    (l = i ∧ m = j) ∨ (l = m ∧ i = j) := by
  obtain ⟨t, ht⟩ := h1
  obtain ⟨s, hs⟩ := h2
  have ht1 : t < 2 := by by_contra h; push Not at h; nlinarith
  have ht2 : -2 < t := by by_contra h; push Not at h; nlinarith
  have hm : m = d * t + j + l - i := by linarith
  subst hm
  interval_cases t
  · -- t = -1
    exfalso
    have hQ : 2 * (i - j) * (i - l) - 2 * d * (j + l - i) + d ^ 2 = 2 * d ^ 2 * s := by
      rw [← hs]; ring
    have hs1 : s < 0 ∨ s = 0 ∨ 0 < s := by omega
    rcases hs1 with h | h | h
    · have : s ≤ -1 := by omega
      nlinarith
    · subst h; nlinarith
    · nlinarith
  · have hQ : (i - j) * (i - l) = d ^ 2 * s := by nlinarith
    have hs0 : s = 0 := by
      rcases lt_trichotomy s 0 with h | h | h
      · exfalso
        have : s ≤ -1 := by omega
        have hb : -(d - 1) ^ 2 ≤ (i - j) * (i - l) := by nlinarith
        nlinarith
      · exact h
      · exfalso
        have : 1 ≤ s := by omega
        have hb : (i - j) * (i - l) ≤ (d - 1) ^ 2 := by nlinarith
        nlinarith
    subst hs0
    simp at hQ
    rcases hQ with h | h
    · right; constructor <;> linarith
    · left; constructor <;> linarith
  · exfalso
    have hQ : 2 * (i - j) * (i - l) + 2 * d * (j + l - i) + d ^ 2 = 2 * d ^ 2 * s := by
      rw [← hs]; ring
    rcases lt_trichotomy s 0 with h | h | h
    · nlinarith
    · subst h; nlinarith
    · have : 1 ≤ s := by omega
      nlinarith

theorem g73j_expsum (N : ℕ) [NeZero N] (n : ℤ) :
    ∑ k : Fin N, Complex.exp (2 * Real.pi * Complex.I * (n * ((k.val + 1 : ℕ) : ℂ)) / N) =
      if (N : ℤ) ∣ n then (N : ℂ) else 0 := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  set x := Complex.exp (2 * Real.pi * Complex.I * n / N) with hx
  have hterm : ∀ k : Fin N, Complex.exp (2 * Real.pi * Complex.I * (n * ((k.val + 1 : ℕ) : ℂ)) / N)
      = x ^ (k.val + 1) := by
    intro k; rw [hx, ← Complex.exp_nat_mul]; congr 1; ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  rw [Fin.sum_univ_eq_sum_range (fun k => x ^ (k + 1)) N]
  have hxN : x ^ N = 1 := by
    rw [hx, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    exact ⟨n, by field_simp⟩
  split_ifs with hdvd
  · obtain ⟨c, hc⟩ := hdvd
    have : x = 1 := by
      rw [hx, Complex.exp_eq_one_iff]; refine ⟨c, ?_⟩; rw [hc]; push_cast; field_simp
    simp [this]
  · have hx1 : x ≠ 1 := by
      intro h1
      rw [hx, Complex.exp_eq_one_iff] at h1
      obtain ⟨c, hc⟩ := h1
      apply hdvd
      refine ⟨c, ?_⟩
      have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have : (n : ℂ) = (N : ℂ) * c := by
        field_simp at hc
        exact hc
      exact_mod_cast this
    have hg := geom_sum_mul x N
    rw [hxN, sub_self] at hg
    have hs : ∑ k ∈ Finset.range N, x ^ k = 0 := by
      rcases mul_eq_zero.1 hg with h | h
      · exact h
      · exact absurd (sub_eq_zero.1 h) hx1
    simp_rw [pow_succ, ← Finset.sum_mul, hs, zero_mul]

/-- explicit entries of the constructed basis -/
theorem g73j_basis_entry (d a : ℕ) [NeZero d] (i k : Fin d) :
    constructedUniformBasis d a i k =
      Complex.exp (2 * Real.pi * Complex.I *
        ((2 * (d : ℂ) * ((k.val + 1 : ℕ) : ℂ) * ((i.val + 1 : ℕ) : ℂ) + (a : ℂ) * ((i.val + 1 : ℕ) : ℂ) ^ 2))
          / (2 * (d : ℂ) ^ 2)) * ((Real.sqrt d : ℂ))⁻¹ := by
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  simp only [constructedUniformBasis, act, clockUnitary, quadraticPhaseUnitary, uniformState,
    Matrix.diagonal_pow, Matrix.diagonal_mul_diagonal, Matrix.mulVec_diagonal, Fintype.card_fin,
    Pi.pow_apply]
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 2
  field_simp

theorem g73j_phase_entry {d : ℕ} (B : Matrix (Fin d) (Fin d) ℂ) (lam : ℝ)
    (X : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    phaseChannel B lam X i j = (lam : ℂ) * X i j + ((1 - lam : ℝ) : ℂ) *
      ∑ k, B i k * (∑ x, ∑ y, starRingEnd ℂ (B x k) * X x y * B y k) * starRingEnd ℂ (B j k) := by
  change (((1 - (1 - lam) : ℝ) : ℂ)) * X i j + (((1 - lam : ℝ) : ℂ)) *
      ∑ k, B i k * (∑ x, ∑ y, starRingEnd ℂ (B x k) * X x y * B y k) * starRingEnd ℂ (B j k) = _
  push_cast; ring_nf

theorem g73j_quad_term (d : ℕ) [NeZero d] (a : ℕ) (i j x y k : Fin d) :
    constructedUniformBasis d a i k * starRingEnd ℂ (constructedUniformBasis d a x k) *
      constructedUniformBasis d a y k * starRingEnd ℂ (constructedUniformBasis d a j k) =
    ((d : ℂ) ^ 2)⁻¹ *
      (Complex.exp (2 * Real.pi * Complex.I *
        ((((i.val : ℤ) - x.val + y.val - j.val : ℤ) : ℂ) * ((k.val + 1 : ℕ) : ℂ)) / d) *
       Complex.exp (2 * Real.pi * Complex.I *
        (((((i.val + 1 : ℕ) : ℤ) ^ 2 - ((x.val + 1 : ℕ) : ℤ) ^ 2 + ((y.val + 1 : ℕ) : ℤ) ^ 2
          - ((j.val + 1 : ℕ) : ℤ) ^ 2 : ℤ) : ℂ) * (a : ℂ)) / (2 * (d : ℂ) ^ 2))) := by
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hdr : (0 : ℝ) ≤ d := by positivity
  simp only [g73j_basis_entry, map_mul, ← Complex.exp_conj, map_inv₀, Complex.conj_ofReal]
  have hs : ((Real.sqrt d : ℂ))⁻¹ * ((Real.sqrt d : ℂ))⁻¹ = ((d : ℂ))⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt hdr]; simp
  have e : ∀ A B C D : ℂ, ∀ s : ℂ, (Complex.exp A * s) * (Complex.exp B * s) * (Complex.exp C * s) *
      (Complex.exp D * s) = (s * s) * (s * s) * Complex.exp (A + B + C + D) := by
    intro A B C D s; simp only [Complex.exp_add]; ring
  rw [e, hs, ← Complex.exp_add]
  rw [show ((d : ℂ) ^ 2)⁻¹ = (d : ℂ)⁻¹ * (d : ℂ)⁻¹ by ring]
  congr 2
  simp only [map_div₀, map_mul, map_add, map_pow, map_natCast, map_ofNat, Complex.conj_I,
    Complex.conj_ofReal]
  push_cast
  field_simp
  ring

theorem g73j_sum_sep {α β : Type} [Fintype α] [Fintype β] (c : ℂ) (f : β → ℂ) (g : α → ℂ) :
    ∑ a, ∑ k, c * (f k * g a) = c * (∑ k, f k) * (∑ a, g a) := by
  simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]

theorem g73j_quad (d : ℕ) [NeZero d] (i j x y : Fin d) :
    ∑ a : Fin (2 * d ^ 2), ∑ k : Fin d,
      constructedUniformBasis d (a.val + 1) i k * starRingEnd ℂ (constructedUniformBasis d (a.val + 1) x k) *
      constructedUniformBasis d (a.val + 1) y k * starRingEnd ℂ (constructedUniformBasis d (a.val + 1) j k) =
    if (x = i ∧ y = j) ∨ (x = y ∧ i = j) then 2 * (d : ℂ) else 0 := by
  haveI : NeZero (2 * d ^ 2) := ⟨by have := NeZero.ne d; positivity⟩
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun k _ => g73j_quad_term d _ i j x y k))]
  rw [g73j_sum_sep]
  have h2 := g73j_expsum (2 * d ^ 2) ((((i.val + 1 : ℕ) : ℤ) ^ 2 - ((x.val + 1 : ℕ) : ℤ) ^ 2 +
    ((y.val + 1 : ℕ) : ℤ) ^ 2 - ((j.val + 1 : ℕ) : ℤ) ^ 2 : ℤ))
  have h1 := g73j_expsum d (((i.val : ℤ) - x.val + y.val - j.val : ℤ))
  rw [show (2 * (d:ℂ)^2) = ((2*d^2 : ℕ) : ℂ) by push_cast; ring]
  rw [h1, h2]
  by_cases hc : (x = i ∧ y = j) ∨ (x = y ∧ i = j)
  · rw [if_pos hc]
    have hA : (d : ℤ) ∣ ((i.val : ℤ) - x.val + y.val - j.val) := by
      rcases hc with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> subst e1 <;> subst e2 <;> simp
    have hB : ((2 * d ^ 2 : ℕ) : ℤ) ∣ (((i.val + 1 : ℕ) : ℤ) ^ 2 - ((x.val + 1 : ℕ) : ℤ) ^ 2 +
        ((y.val + 1 : ℕ) : ℤ) ^ 2 - ((j.val + 1 : ℕ) : ℤ) ^ 2) := by
      rcases hc with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> subst e1 <;> subst e2 <;> simp
    rw [if_pos hA, if_pos hB]
    field_simp
    push_cast; ring
  · rw [if_neg hc]
    by_cases hA : (d : ℤ) ∣ ((i.val : ℤ) - x.val + y.val - j.val)
    · rw [if_pos hA]
      have hB : ¬ (((2 * d ^ 2 : ℕ) : ℤ) ∣ (((i.val + 1 : ℕ) : ℤ) ^ 2 - ((x.val + 1 : ℕ) : ℤ) ^ 2 +
        ((y.val + 1 : ℕ) : ℤ) ^ 2 - ((j.val + 1 : ℕ) : ℤ) ^ 2)) := by
        intro hB
        push_cast at hB
        apply hc
        have hdpos : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
        have := g73j_nt (d : ℤ) hdpos ((i.val : ℤ) + 1) ((j.val : ℤ) + 1) ((x.val : ℤ) + 1)
          ((y.val : ℤ) + 1) (by omega) (by have := i.isLt; omega) (by omega)
          (by have := j.isLt; omega) (by omega) (by have := x.isLt; omega) (by omega)
          (by have := y.isLt; omega) (by convert hA using 1; ring) (by convert hB using 1; ring)
        rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left; exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
        · right; exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
      rw [if_neg hB]; simp
    · rw [if_neg hA]; simp

theorem g73j_q_phase (u w s : ℂ) (hu0 : u ≠ 0) (hw0 : w ≠ 0) (hu : starRingEnd ℂ u = u⁻¹)
    (hw : starRingEnd ℂ w = w⁻¹)
    (hs : starRingEnd ℂ s = s) (hs2 : s ^ 2 = 1 / 2) (lam : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    phaseChannel (!![-u * s, u * s; w * s, w * s]) lam X =
      ((((1 + lam) / 2 : ℝ) : ℂ)) • X + ((((1 - lam) / 2 : ℝ) : ℂ)) •
        conjSuperop (!![0, u * starRingEnd ℂ w; w * starRingEnd ℂ u, 0]) X := by
  have hs4 : s ^ 4 = 1 / 4 := by rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, hs2]; norm_num
  ext i j
  rw [g73j_phase_entry]
  simp only [conjSuperop, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;>
  · simp [hs, hu, hw]
    push_cast
    field_simp
    ring_nf
    simp only [hs2, hs4]
    ring_nf

theorem g73j_exp_eq (A B : ℂ) (n : ℤ) (h : A = B + n * (2 * Real.pi * Complex.I)) :
    Complex.exp A = Complex.exp B := by
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem g73j_exp_neg (A B : ℂ) (n : ℤ) (h : A = B + Real.pi * Complex.I + n * (2 * Real.pi * Complex.I)) :
    Complex.exp A = -Complex.exp B := by
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, Complex.exp_add,
    Complex.exp_pi_mul_I]; ring

theorem g73j_q_basis (a : ℕ) :
    constructedUniformBasis 2 a =
      !![-(Complex.exp (2 * Real.pi * Complex.I * a / 8)) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹,
          Complex.exp (2 * Real.pi * Complex.I * a / 8) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹;
         Complex.exp (Real.pi * Complex.I * a) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹,
          Complex.exp (Real.pi * Complex.I * a) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹] := by
  ext i k
  rw [g73j_basis_entry]
  fin_cases i <;> fin_cases k <;> simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Fin.val_zero, Fin.val_one, Nat.cast_ofNat] <;>
    congr 1
  · exact g73j_exp_neg _ _ 0 (by push_cast; ring)
  · exact g73j_exp_eq _ _ 1 (by push_cast; ring)
  · exact g73j_exp_eq _ _ 1 (by push_cast; ring)
  · exact g73j_exp_eq _ _ 2 (by push_cast; ring)

theorem g73j_conj_neg {n : ℕ} (M X : Matrix (Fin n) (Fin n) ℂ) :
    conjSuperop (-M) X = conjSuperop M X := by
  simp [conjSuperop, Matrix.conjTranspose_neg]

theorem g73j_q_Delta (a : ℕ) (lam : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    constructedPhaseDamping 2 lam a X =
      ((((1 + lam) / 2 : ℝ) : ℂ)) • X + ((((1 - lam) / 2 : ℝ) : ℂ)) •
        conjSuperop (!![0, Complex.exp (-(3 * Real.pi * Complex.I * a / 4));
          Complex.exp (3 * Real.pi * Complex.I * a / 4), 0]) X := by
  unfold constructedPhaseDamping
  rw [g73j_q_basis]
  have hs2 : (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) ^ 2 = 1 / 2 := by
    rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; ring
  rw [g73j_q_phase _ _ _ (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
    (by rw [← Complex.exp_conj, ← Complex.exp_neg]; congr 1; simp [map_div₀, map_ofNat]; ring)
    (by rw [← Complex.exp_conj, ← Complex.exp_neg]; congr 1; simp)
    (by simp) hs2]
  congr 3
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  · rw [← Complex.exp_conj, ← Complex.exp_add]; congr 1; simp [map_div₀, map_ofNat]; ring
  · rw [← Complex.exp_conj, ← Complex.exp_add]; congr 1; simp [map_div₀, map_ofNat]; ring

theorem g73j_q_facts :
    let t := Complex.exp ((Real.pi : ℂ) * Complex.I / 4)
    let t' := Complex.exp (-(Real.pi : ℂ) * Complex.I / 4)
    t * t' = 1 ∧ t ^ 2 = Complex.I ∧ t' ^ 2 = -Complex.I ∧ starRingEnd ℂ t = t' ∧
      starRingEnd ℂ t' = t := by
  intro t t'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← Complex.exp_add]; convert Complex.exp_zero using 2; ring
  · rw [← Complex.exp_nat_mul]
    rw [show ((2:ℕ):ℂ) * ((Real.pi : ℂ) * Complex.I / 4) = Real.pi / 2 * Complex.I by push_cast; ring]
    exact Complex.exp_pi_div_two_mul_I
  · rw [← Complex.exp_nat_mul, g73j_exp_neg _ (Real.pi / 2 * Complex.I) (-1) (by push_cast; ring),
      Complex.exp_pi_div_two_mul_I]
  · rw [← Complex.exp_conj]; congr 1; simp [map_ofNat]
  · rw [← Complex.exp_conj]; congr 1; simp [map_ofNat]

theorem g73j_q_paulis :
    qubitPauli pauliX = !![0, 1; 1, 0] ∧ qubitPauli pauliY = !![0, -Complex.I; Complex.I, 0] ∧
    qubitPauli pauliZ = !![1, 0; 0, -1] := by
  refine ⟨?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [qubitPauli, pauliX, pauliY, pauliZ]

theorem g73j_q_tauc :
    qubitTauConjugate = !![0, Complex.exp (-(Real.pi : ℂ) * Complex.I / 4);
      Complex.exp ((Real.pi : ℂ) * Complex.I / 4), 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [qubitTauConjugate, qubitTau] <;>
    rw [← Complex.exp_conj] <;> congr 1 <;> simp [map_ofNat]

theorem g73j_q_sig (a : ℕ) (lam : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ)
    (sgn : ℂ) (hsgn : sgn = 1 ∨ sgn = -1)
    (h01 : Complex.exp (-(3 * Real.pi * Complex.I * a / 4)) = sgn * M 0 1)
    (h10 : Complex.exp (3 * Real.pi * Complex.I * a / 4) = sgn * M 1 0)
    (h00 : M 0 0 = 0) (h11 : M 1 1 = 0) :
    constructedPhaseDamping 2 lam a X =
      ((((1 + lam) / 2 : ℝ) : ℂ)) • X + ((((1 - lam) / 2 : ℝ) : ℂ)) • conjSuperop M X := by
  rw [g73j_q_Delta]
  have hM : !![0, Complex.exp (-(3 * Real.pi * Complex.I * a / 4));
          Complex.exp (3 * Real.pi * Complex.I * a / 4), 0] = sgn • M := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [h01, h10, h00, h11]
  rw [hM]
  rcases hsgn with h | h <;> subst h
  · rw [one_smul]
  · rw [neg_smul, one_smul, g73j_conj_neg]

theorem g73j_sum8 {M : Type} [AddCommMonoid M] (f : ℕ → M) :
    ∑ a : Fin 8, f (a.val + 1) = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := by
  simp [Fin.sum_univ_eight]

theorem g73j_conj2 (M X : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    conjSuperop M X i j = M i 0 * X 0 0 * starRingEnd ℂ (M j 0) + M i 0 * X 0 1 * starRingEnd ℂ (M j 1) +
      M i 1 * X 1 0 * starRingEnd ℂ (M j 0) + M i 1 * X 1 1 * starRingEnd ℂ (M j 1) := by
  simp only [conjSuperop, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    RCLike.star_def]
  ring

theorem g73j_q_tau : qubitTau = !![0, Complex.exp ((Real.pi : ℂ) * Complex.I / 4);
     Complex.exp (-(Real.pi : ℂ) * Complex.I / 4), 0] := rfl

theorem g73j_q_t' : Complex.exp (-(Real.pi : ℂ) * Complex.I / 4) =
    -(Complex.I * Complex.exp ((Real.pi : ℂ) * Complex.I / 4)) := by
  rw [g73j_exp_neg _ ((Real.pi : ℂ) * Complex.I / 4 + Real.pi / 2 * Complex.I) (-1)
    (by push_cast; ring), Complex.exp_add, Complex.exp_pi_div_two_mul_I]; ring

/-- King quant-ph/0204172v2, PDF pp.16-18, (73)-(85).
Normalized states, complex off-diagonal conjugation, and the two-channel Omega average.
The four Delta terms are output-conjugated phase-damping maps. -/
theorem solution (lam : ℝ) (hlow : -1 / 3 ≤ lam) (hhigh : lam ≤ 1) :
    let lp : ℂ := ((1 + lam) / 2 : ℝ)
    let lm : ℂ := ((1 - lam) / 2 : ℝ)
    let sx := qubitPauli pauliX
    let sy := qubitPauli pauliY
    let sz := qubitPauli pauliZ
    clockUnitary 2 = -sz ∧
    quadraticPhaseUnitary 2 = !![Complex.exp ((Real.pi : ℂ) * Complex.I / 4), 0; 0, -1] ∧
    ∀ rho : Matrix (Fin 2) (Fin 2) ℂ, IsDensityMatrix rho →
      let a := rho 0 0
      let b := rho 1 1
      let c := rho 0 1
      depolarizing 2 (1 - lam) rho = !![lp*a + lm*b, (lam : ℂ)*c;
        (lam : ℂ)*conj c, lm*a + lp*b] ∧
      intermediateChannel 2 lam rho = !![lp*a + lm*b, lp*c; lp*conj c, lm*a + lp*b] ∧
      depolarizing 2 (1 - lam) rho = (((2*lam/(1+lam) : ℝ) : ℂ)) • intermediateChannel 2 lam rho +
        ((((1-lam)/(2*(1+lam)) : ℝ) : ℂ)) •
          (intermediateChannel 2 lam rho + conjSuperop sz (intermediateChannel 2 lam rho)) ∧
      constructedPhaseDamping 2 lam 2 rho = constructedPhaseDamping 2 lam 6 rho ∧
      constructedPhaseDamping 2 lam 2 rho = lp • rho + lm • conjSuperop sy rho ∧
      constructedPhaseDamping 2 lam 4 rho = constructedPhaseDamping 2 lam 8 rho ∧
      constructedPhaseDamping 2 lam 4 rho = lp • rho + lm • conjSuperop sx rho ∧
      constructedPhaseDamping 2 lam 1 rho = constructedPhaseDamping 2 lam 5 rho ∧
      constructedPhaseDamping 2 lam 1 rho = lp • rho + lm • conjSuperop qubitTau rho ∧
      constructedPhaseDamping 2 lam 3 rho = constructedPhaseDamping 2 lam 7 rho ∧
      constructedPhaseDamping 2 lam 3 rho = lp • rho + lm • conjSuperop qubitTauConjugate rho ∧
      intermediateChannel 2 lam rho = (1/8 : ℂ) •
        (∑ a : Fin 8, constructedPhaseDamping 2 lam (a.val+1) rho) ∧
      intermediateChannel 2 lam rho = (1/2 : ℂ) •
        (constructedPhaseDamping 2 lam 2 rho + constructedPhaseDamping 2 lam 4 rho) ∧
      depolarizing 2 (1 - lam) rho =
        ((((1+3*lam)/(4*(1+lam)) : ℝ) : ℂ)) •
          (constructedPhaseDamping 2 lam 2 rho + constructedPhaseDamping 2 lam 4 rho) +
        ((((1-lam)/(4*(1+lam)) : ℝ) : ℂ)) •
          (conjSuperop sz (constructedPhaseDamping 2 lam 2 rho) +
           conjSuperop sz (constructedPhaseDamping 2 lam 4 rho)) := by
  dsimp only
  obtain ⟨htt, ht2, ht'2, hct, hct'⟩ := g73j_q_facts
  obtain ⟨hpx, hpy, hpz⟩ := g73j_q_paulis
  have hpi2 := Complex.exp_pi_div_two_mul_I
  refine ⟨?_, ?_, fun rho hrho => ?_⟩
  · rw [hpz]; ext i j; fin_cases i <;> fin_cases j <;> simp [clockUnitary]
    · rw [g73j_exp_neg _ 0 0 (by push_cast; ring)]; simp
    · rw [g73j_exp_eq _ 0 1 (by push_cast; ring)]; simp
  · ext i j; fin_cases i <;> fin_cases j <;> simp [quadraticPhaseUnitary]
    · congr 1; push_cast; ring
    · rw [g73j_exp_neg _ 0 0 (by push_cast; ring)]; simp
  have hH : rho 1 0 = starRingEnd ℂ (rho 0 1) := (hrho.1.isHermitian.apply 1 0).symm
  have hD : QAlgorithms.Papers.Independent.Information100.P08.depolarizing 2 (1 - lam) rho =
      !![(((1 + lam) / 2 : ℝ) : ℂ) * rho 0 0 + (((1 - lam) / 2 : ℝ) : ℂ) * rho 1 1, (lam : ℂ) * rho 0 1;
        (lam : ℂ) * starRingEnd ℂ (rho 0 1), (((1 - lam) / 2 : ℝ) : ℂ) * rho 0 0 + (((1 + lam) / 2 : ℝ) : ℂ) * rho 1 1] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [g73j_depol_entry, Matrix.trace, Fin.sum_univ_two, hH] <;> ring
  have hO : intermediateChannel 2 lam rho =
      !![(((1 + lam) / 2 : ℝ) : ℂ) * rho 0 0 + (((1 - lam) / 2 : ℝ) : ℂ) * rho 1 1, (((1 + lam) / 2 : ℝ) : ℂ) * rho 0 1;
        (((1 + lam) / 2 : ℝ) : ℂ) * starRingEnd ℂ (rho 0 1), (((1 - lam) / 2 : ℝ) : ℂ) * rho 0 0 + (((1 + lam) / 2 : ℝ) : ℂ) * rho 1 1] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [g73j_inter_entry, g73j_depol_entry, Matrix.trace, Fin.sum_univ_two, hH] <;> ring
  have h1 := g73j_q_sig 1 lam rho qubitTau (-1) (Or.inr rfl)
    (by rw [neg_one_mul]; exact g73j_exp_neg _ _ (-1) (by simp [qubitTau]; push_cast; ring))
    (by rw [neg_one_mul]; exact g73j_exp_neg _ _ 0 (by simp [qubitTau]; push_cast; ring)) rfl rfl
  have h2 := g73j_q_sig 2 lam rho (qubitPauli pauliY) (-1) (Or.inr rfl)
    (by rw [hpy]; simp; rw [g73j_exp_eq _ (Real.pi / 2 * Complex.I) (-1) (by push_cast; ring), hpi2])
    (by rw [hpy]; simp; rw [g73j_exp_neg _ (Real.pi / 2 * Complex.I) 0 (by push_cast; ring), hpi2])
    (by rw [hpy]; simp) (by rw [hpy]; simp)
  have h3 := g73j_q_sig 3 lam rho qubitTauConjugate 1 (Or.inl rfl)
    (by rw [g73j_q_tauc, one_mul]; exact g73j_exp_eq _ _ (-1) (by simp; push_cast; ring))
    (by rw [g73j_q_tauc, one_mul]; exact g73j_exp_eq _ _ 1 (by simp; push_cast; ring))
    (by rw [g73j_q_tauc]; simp) (by rw [g73j_q_tauc]; simp)
  have h4 := g73j_q_sig 4 lam rho (qubitPauli pauliX) (-1) (Or.inr rfl)
    (by rw [hpx]; simp; rw [g73j_exp_neg _ 0 (-2) (by push_cast; ring)]; simp)
    (by rw [hpx]; simp; rw [g73j_exp_neg _ 0 1 (by push_cast; ring)]; simp)
    (by rw [hpx]; simp) (by rw [hpx]; simp)
  have h5 := g73j_q_sig 5 lam rho qubitTau 1 (Or.inl rfl)
    (by rw [one_mul]; exact g73j_exp_eq _ _ (-2) (by simp [qubitTau]; push_cast; ring))
    (by rw [one_mul]; exact g73j_exp_eq _ _ 2 (by simp [qubitTau]; push_cast; ring)) rfl rfl
  have h6 := g73j_q_sig 6 lam rho (qubitPauli pauliY) 1 (Or.inl rfl)
    (by rw [hpy]; simp; rw [g73j_exp_neg _ (Real.pi / 2 * Complex.I) (-3) (by push_cast; ring), hpi2])
    (by rw [hpy]; simp; rw [g73j_exp_eq _ (Real.pi / 2 * Complex.I) 2 (by push_cast; ring), hpi2])
    (by rw [hpy]; simp) (by rw [hpy]; simp)
  have h7 := g73j_q_sig 7 lam rho qubitTauConjugate (-1) (Or.inr rfl)
    (by rw [g73j_q_tauc, neg_one_mul]; exact g73j_exp_neg _ _ (-3) (by simp; push_cast; ring))
    (by rw [g73j_q_tauc, neg_one_mul]; exact g73j_exp_neg _ _ 2 (by simp; push_cast; ring))
    (by rw [g73j_q_tauc]; simp) (by rw [g73j_q_tauc]; simp)
  have h8 := g73j_q_sig 8 lam rho (qubitPauli pauliX) 1 (Or.inl rfl)
    (by rw [hpx]; simp; rw [g73j_exp_eq _ 0 (-3) (by push_cast; ring)]; simp)
    (by rw [hpx]; simp; rw [g73j_exp_eq _ 0 3 (by push_cast; ring)]; simp)
    (by rw [hpx]; simp) (by rw [hpx]; simp)
  have hl : (1 + (lam : ℂ)) ≠ 0 := by
    have : (0 : ℝ) < 1 + lam := by linarith
    exact_mod_cast this.ne'
  have hs8 := g73j_sum8 (fun n => constructedPhaseDamping 2 lam n rho)
  refine ⟨hD, hO, ?_, by rw [h2, h6], h2, by rw [h4, h8], h4, by rw [h1, h5], h1, by rw [h3, h7], h3,
    ?_, ?_, ?_⟩
  · rw [hD, hO, hpz]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, g73j_conj2]
    fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring
  · rw [hs8, h1, h2, h3, h4, h5, h6, h7, h8, hO, hpx, hpy, g73j_q_tauc, g73j_q_tau, g73j_q_t']
    rw [g73j_q_t'] at hct
    generalize Complex.exp ((Real.pi : ℂ) * Complex.I / 4) = t at ht2 hct ⊢
    have h3 : t ^ 3 = Complex.I * t := by rw [pow_succ, ht2]
    have h4 : t ^ 4 = -1 := by rw [show t ^ 4 = (t ^ 2) ^ 2 by ring, ht2, Complex.I_sq]
    have h5 : t ^ 5 = -t := by rw [pow_succ, h4]; ring
    have h6 : t ^ 6 = -Complex.I := by rw [pow_succ, h5]; rw [← ht2]; ring
    have hI4 : Complex.I ^ 4 = 1 := by rw [show Complex.I ^ 4 = (Complex.I ^ 2) ^ 2 by ring, Complex.I_sq]; norm_num
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, g73j_conj2]
    fin_cases i <;> fin_cases j <;> simp [hct, hH] <;> ring_nf <;>
      (try simp only [ht2, h3, h4, h5, h6, Complex.I_sq, hI4]) <;> ring_nf <;>
      (try simp only [ht2, h3, h4, h5, h6, Complex.I_sq, hI4]) <;> ring_nf
  · rw [h2, h4, hO, hpx, hpy]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, g73j_conj2]
    fin_cases i <;> fin_cases j <;> simp [hH] <;> ring_nf <;> (try simp only [Complex.I_sq]) <;> ring_nf
  · rw [hD, h2, h4, hpz, hpx, hpy]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, g73j_conj2]
    fin_cases i <;> fin_cases j <;> simp [hH] <;> field_simp <;> ring_nf <;>
      (try simp only [Complex.I_sq]) <;> ring_nf



end
