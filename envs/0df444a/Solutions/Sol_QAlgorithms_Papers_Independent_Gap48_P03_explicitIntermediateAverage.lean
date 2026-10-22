-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P03.explicitIntermediateAverage
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T22:08:42.796622+00:00
-- url     : https://prove2.me/submissions/ece6836a-6e3a-4b5c-865d-b5104f00b855

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

theorem g73j_swap4 {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (F : α → β → γ → δ → ℂ) :
    ∑ a, ∑ k, ∑ x, ∑ y, F a k x y = ∑ x, ∑ y, ∑ a, ∑ k, F a k x y := by
  calc ∑ a, ∑ k, ∑ x, ∑ y, F a k x y = ∑ a, ∑ x, ∑ y, ∑ k, F a k x y := by
        apply Finset.sum_congr rfl; intro a _
        rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro x _; rw [Finset.sum_comm]
    _ = ∑ x, ∑ y, ∑ a, ∑ k, F a k x y := by
        rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro x _; rw [Finset.sum_comm]

theorem g73j_cond_sum {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) (c : ℂ) (i j : Fin d) :
    ∑ x, ∑ y, X x y * (if (x = i ∧ y = j) ∨ (x = y ∧ i = j) then c else 0) =
      c * (if i = j then X.trace else X i j) := by
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, Matrix.trace, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro x _
    rw [Finset.sum_eq_single x]
    · rw [if_pos (Or.inr ⟨rfl, rfl⟩)]; simp only [Matrix.diag]; ring
    · intro y _ hy; rw [if_neg]
      · simp
      · rintro (⟨h1, h2⟩ | ⟨h1, _⟩)
        · exact hy (h2.trans h1.symm)
        · exact hy h1.symm
    · simp
  · rw [if_neg h, Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · rw [if_pos (Or.inl ⟨rfl, rfl⟩)]; ring
      · intro y _ hy; rw [if_neg]
        · simp
        · rintro (⟨_, h2⟩ | ⟨_, h2⟩)
          · exact hy h2
          · exact h h2
      · simp
    · intro x _ hx; apply Finset.sum_eq_zero; intro y _; rw [if_neg]
      · simp
      · rintro (⟨h1, _⟩ | ⟨_, h2⟩)
        · exact hx h1
        · exact h h2
    · simp

theorem g73j_average (d : ℕ) [NeZero d] (lam : ℝ) (X : Matrix (Fin d) (Fin d) ℂ) :
    intermediateChannel d lam X = (((2 * d^2 : ℕ) : ℂ)⁻¹) •
        ∑ a : Fin (2 * d^2), constructedPhaseDamping d lam (a.val + 1) X := by
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  ext i j
  rw [g73j_inter_entry, g73j_depol_entry, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  simp only [constructedPhaseDamping, g73j_phase_entry, Finset.sum_add_distrib]
  have hr : ∑ a : Fin (2 * d ^ 2), ((1 - lam : ℝ) : ℂ) * ∑ k,
      constructedUniformBasis d (a.val + 1) i k *
        (∑ x, ∑ y, starRingEnd ℂ (constructedUniformBasis d (a.val + 1) x k) * X x y *
          constructedUniformBasis d (a.val + 1) y k) *
        starRingEnd ℂ (constructedUniformBasis d (a.val + 1) j k) =
      ((1 - lam : ℝ) : ℂ) * (2 * (d : ℂ) * (if i = j then X.trace else X i j)) := by
    rw [← Finset.mul_sum, ← g73j_cond_sum, ← Finset.sum_congr rfl (fun x _ =>
      Finset.sum_congr rfl (fun y _ => congrArg (X x y * ·) (g73j_quad d i j x y)))]
    congr 1
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [g73j_swap4]
    apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro y _
    apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro k _
    ring
  rw [hr]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  split_ifs with h
  · field_simp; ring
  · field_simp; ring

theorem g73j_pair_term (d : ℕ) [NeZero d] (a : ℕ) (i k l : Fin d) :
    starRingEnd ℂ (constructedUniformBasis d a i k) * constructedUniformBasis d a i l =
    (d : ℂ)⁻¹ * Complex.exp (2 * Real.pi * Complex.I *
        ((((l.val : ℤ) - k.val : ℤ) : ℂ) * ((i.val + 1 : ℕ) : ℂ)) / d) := by
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hdr : (0 : ℝ) ≤ d := by positivity
  simp only [g73j_basis_entry, map_mul, ← Complex.exp_conj, map_inv₀, Complex.conj_ofReal]
  have hs : ((Real.sqrt d : ℂ))⁻¹ * ((Real.sqrt d : ℂ))⁻¹ = ((d : ℂ))⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt hdr]; simp
  have e : ∀ A B : ℂ, ∀ s : ℂ, (Complex.exp A * s) * (Complex.exp B * s) =
      (s * s) * Complex.exp (A + B) := by
    intro A B s; simp only [Complex.exp_add]; ring
  rw [e, hs]
  congr 2
  simp only [map_div₀, map_mul, map_add, map_pow, map_natCast, map_ofNat, Complex.conj_I,
    Complex.conj_ofReal]
  push_cast
  field_simp
  ring

theorem g73j_basis_unitary (d : ℕ) [NeZero d] (a : ℕ) :
    (constructedUniformBasis d a)ᴴ * constructedUniformBasis d a = 1 := by
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  ext k l
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def, g73j_pair_term]
  rw [← Finset.mul_sum, g73j_expsum, Matrix.one_apply]
  by_cases h : k = l
  · subst h; simp [hd]
  · rw [if_neg h, if_neg]
    · simp
    · intro hdvd
      have := Int.eq_zero_of_abs_lt_dvd hdvd (by
        rw [abs_lt]; constructor <;> have := k.isLt <;> have := l.isLt <;> omega)
      exact h (Fin.ext (by omega))

theorem g73j_act_ket {d : ℕ} (B : Matrix (Fin d) (Fin d) ℂ) (k i : Fin d) :
    act B (ket k) i = B i k := by
  simp [act, ket, Matrix.mulVec, dotProduct, EuclideanSpace.single_apply]

theorem g73j_basis_uniform (d : ℕ) [NeZero d] (a : ℕ) :
    IsUniformBasis (constructedUniformBasis d a) := by
  intro k i j
  have key : ∀ i : Fin d, ‖act (constructedUniformBasis d a) (ket k) i‖ = (Real.sqrt d)⁻¹ := by
    intro i
    rw [g73j_act_ket, g73j_basis_entry, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [show (2 * (Real.pi : ℂ) * Complex.I *
        ((2 * (d : ℂ) * ((k.val + 1 : ℕ) : ℂ) * ((i.val + 1 : ℕ) : ℂ) + (a : ℂ) * ((i.val + 1 : ℕ) : ℂ) ^ 2))
          / (2 * (d : ℂ) ^ 2)) = ((2 * Real.pi * ((2 * (d : ℝ) * ((k.val + 1 : ℕ) : ℝ) *
            ((i.val + 1 : ℕ) : ℝ) + (a : ℝ) * ((i.val + 1 : ℕ) : ℝ) ^ 2)) / (2 * (d : ℝ) ^ 2) : ℝ) : ℂ)
              * Complex.I by push_cast; ring]
    rw [Complex.norm_exp_ofReal_mul_I, one_mul]
  rw [key i, key j]

/-- Fourier phases used for the Kraus decomposition of the phase channel. -/
def g73j_D (d : ℕ) (s : Fin d) : Fin d → ℂ := fun k =>
  Complex.exp (2 * Real.pi * Complex.I * (((k.val : ℤ) : ℂ) * ((s.val + 1 : ℕ) : ℂ)) / d)

def g73j_c (d : ℕ) (lam : ℝ) (s : Fin d) : ℝ :=
  (1 - lam) / d + if s.val + 1 = d then lam else 0

theorem g73j_D_mul_conj (d : ℕ) [NeZero d] (s k l : Fin d) :
    g73j_D d s k * starRingEnd ℂ (g73j_D d s l) =
      Complex.exp (2 * Real.pi * Complex.I * ((((k.val : ℤ) - l.val : ℤ) : ℂ) * ((s.val + 1 : ℕ) : ℂ)) / d) := by
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  simp only [g73j_D, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_div₀, map_mul, map_natCast, map_ofNat, Complex.conj_I, Complex.conj_ofReal, map_intCast]
  push_cast; ring

theorem g73j_D_norm (d : ℕ) [NeZero d] (s k : Fin d) :
    starRingEnd ℂ (g73j_D d s k) * g73j_D d s k = 1 := by
  rw [mul_comm, g73j_D_mul_conj]; simp

theorem g73j_D_last (d : ℕ) [NeZero d] (s k : Fin d) (hs : s.val + 1 = d) : g73j_D d s k = 1 := by
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  rw [g73j_D, Complex.exp_eq_one_iff]
  refine ⟨k.val, ?_⟩
  rw [hs]; push_cast; field_simp

theorem g73j_c_sum (d : ℕ) [NeZero d] (lam : ℝ) (k l : Fin d) :
    ∑ s, (g73j_c d lam s : ℂ) * (g73j_D d s k * starRingEnd ℂ (g73j_D d s l)) =
      (lam : ℂ) + ((1 - lam : ℝ) : ℂ) * (if k = l then 1 else 0) := by
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  simp only [g73j_c, Complex.ofReal_add, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
    g73j_D_mul_conj]
  rw [g73j_expsum]
  have hlast : ∑ s : Fin d, ((if s.val + 1 = d then lam else 0 : ℝ) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * ((((k.val : ℤ) - l.val : ℤ) : ℂ) * ((s.val + 1 : ℕ) : ℂ)) / d)
      = lam := by
    rw [Finset.sum_eq_single ⟨d - 1, by omega⟩]
    · rw [if_pos (by simp; omega)]
      have : Complex.exp (2 * Real.pi * Complex.I * ((((k.val : ℤ) - l.val : ℤ) : ℂ) *
          ((d - 1 + 1 : ℕ) : ℂ)) / d) = 1 := by
        rw [Complex.exp_eq_one_iff]; refine ⟨(k.val : ℤ) - l.val, ?_⟩
        rw [Nat.sub_add_cancel hpos]; push_cast; field_simp
      exact (congrArg (fun z => (lam : ℂ) * z) this).trans (mul_one _)
    · intro s _ hs; rw [if_neg]; · simp
      intro h; apply hs; ext; simp; omega
    · simp
  rw [hlast]
  by_cases h : k = l
  · subst h; simp
  · rw [if_neg, if_neg h]; · simp
    intro hdvd
    have := Int.eq_zero_of_abs_lt_dvd hdvd (by
      rw [abs_lt]; constructor <;> have := k.isLt <;> have := l.isLt <;> omega)
    exact h (Fin.ext (by omega))

theorem g73j_Z_unitary {d : ℕ} [NeZero d] (B : Matrix (Fin d) (Fin d) ℂ) (hB : Bᴴ * B = 1)
    (s : Fin d) :
    (B * Matrix.diagonal (g73j_D d s) * Bᴴ)ᴴ * (B * Matrix.diagonal (g73j_D d s) * Bᴴ) = 1 := by
  have hB' : B * Bᴴ = 1 := mul_eq_one_comm.mp hB
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.diagonal_conjTranspose]
  have hdd : Matrix.diagonal (star (g73j_D d s)) * Matrix.diagonal (g73j_D d s) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext k; exact g73j_D_norm d s k
  calc B * (Matrix.diagonal (star (g73j_D d s)) * Bᴴ) * (B * Matrix.diagonal (g73j_D d s) * Bᴴ)
      = B * (Matrix.diagonal (star (g73j_D d s)) * (Bᴴ * B) * Matrix.diagonal (g73j_D d s)) * Bᴴ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hB, Matrix.mul_one, hdd, Matrix.mul_one, hB']

theorem g73j_c_total (d : ℕ) [NeZero d] (lam : ℝ) : ∑ s, g73j_c d lam s = 1 := by
  have hdr : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  simp only [g73j_c, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [Finset.sum_eq_single ⟨d - 1, by omega⟩]
  · rw [if_pos (by simp; omega)]; field_simp; ring
  · intro s _ hs; rw [if_neg]
    intro h; apply hs; ext; simp; omega
  · simp

theorem g73j_phase_channel {d : ℕ} [NeZero d] (B : Matrix (Fin d) (Fin d) ℂ) (hB : Bᴴ * B = 1)
    (lam : ℝ) (h1 : 0 ≤ 1 + ((d : ℝ) - 1) * lam) (h2 : lam ≤ 1) :
    IsChannel (phaseChannel B lam) := by
  have hB' : B * Bᴴ = 1 := mul_eq_one_comm.mp hB
  have hdr : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hc : ∀ s, 0 ≤ g73j_c d lam s := by
    intro s; unfold g73j_c
    split_ifs
    · have : (1 - lam) / d + lam = (1 + ((d : ℝ) - 1) * lam) / d := by field_simp; ring
      rw [this]; exact div_nonneg h1 hdr.le
    · simp only [add_zero]; apply div_nonneg _ hdr.le; linarith
  have hsq : ∀ s, star ((Real.sqrt (g73j_c d lam s) : ℝ) : ℂ) * ((Real.sqrt (g73j_c d lam s) : ℝ) : ℂ) =
      ((g73j_c d lam s : ℝ) : ℂ) := by
    intro s
    rw [RCLike.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hc s)]
  have hsq' : ∀ s, ((Real.sqrt (g73j_c d lam s) : ℝ) : ℂ) * star ((Real.sqrt (g73j_c d lam s) : ℝ) : ℂ) =
      ((g73j_c d lam s : ℝ) : ℂ) := by
    intro s; rw [mul_comm, hsq]
  refine ⟨d, fun s => ((Real.sqrt (g73j_c d lam s) : ℝ) : ℂ) •
    (B * Matrix.diagonal (g73j_D d s) * Bᴴ), ?_, ?_⟩
  · unfold IsKrausFamily
    simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hsq, hsq',
      g73j_Z_unitary B hB]
    rw [← Finset.sum_smul]
    have := g73j_c_total d lam
    have : ∑ s, ((g73j_c d lam s : ℝ) : ℂ) = 1 := by exact_mod_cast this
    rw [this, one_smul]
  · intro X
    set Y := Bᴴ * X * B with hY
    have hW : ∀ s, ((Real.sqrt (g73j_c d lam s) : ℝ) : ℂ) • (B * Matrix.diagonal (g73j_D d s) * Bᴴ) * X *
        (((Real.sqrt (g73j_c d lam s) : ℝ) : ℂ) • (B * Matrix.diagonal (g73j_D d s) * Bᴴ))ᴴ =
        B * (((g73j_c d lam s : ℝ) : ℂ) • (Matrix.diagonal (g73j_D d s) * Y *
          Matrix.diagonal (star (g73j_D d s)))) * Bᴴ := by
      intro s
      simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hsq', hsq,
        Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose, hY]
      simp only [Matrix.mul_assoc]
    have hM : ∑ s, ((g73j_c d lam s : ℝ) : ℂ) • (Matrix.diagonal (g73j_D d s) * Y *
          Matrix.diagonal (star (g73j_D d s))) =
        (lam : ℂ) • Y + ((1 - lam : ℝ) : ℂ) • Matrix.diagonal (fun k => Y k k) := by
      ext k l
      simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
        Matrix.add_apply, Matrix.diagonal_apply, smul_eq_mul, Pi.star_apply, RCLike.star_def]
      have := g73j_c_sum d lam k l
      calc ∑ s, ((g73j_c d lam s : ℝ) : ℂ) * (g73j_D d s k * Y k l * starRingEnd ℂ (g73j_D d s l))
          = Y k l * ∑ s, ((g73j_c d lam s : ℝ) : ℂ) * (g73j_D d s k * starRingEnd ℂ (g73j_D d s l)) := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _; ring
        _ = _ := by
            rw [this]; split_ifs with h
            · subst h; ring
            · ring
    have hK : krausApply (fun s => ((Real.sqrt (g73j_c d lam s) : ℝ) : ℂ) •
        (B * Matrix.diagonal (g73j_D d s) * Bᴴ)) X =
        (lam : ℂ) • X + ((1 - lam : ℝ) : ℂ) • (B * Matrix.diagonal (fun k => Y k k) * Bᴴ) := by
      unfold krausApply
      simp only [hW]
      rw [← Finset.sum_mul, ← Matrix.mul_sum, hM]
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.smul_mul, hY]
      congr 2
      calc B * (Bᴴ * X * B) * Bᴴ = (B * Bᴴ) * X * (B * Bᴴ) := by simp only [Matrix.mul_assoc]
        _ = X := by rw [hB', Matrix.one_mul, Matrix.mul_one]
    rw [hK]
    ext i j
    rw [g73j_phase_entry, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul,
      smul_eq_mul]
    congr 2
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl; intro k _
    rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply, RCLike.star_def, hY]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def]
    congr 2
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro y _
    rw [Finset.sum_mul]
theorem g73j_clock_decomp {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (lam : ℝ) (hlow : -1 / ((d : ℝ)^2 - 1) ≤ lam) (hhigh : lam ≤ 1)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    depolarizing d (1 - lam) X =
      (((lam * d / (1 + ((d : ℝ) - 1) * lam)) : ℝ) : ℂ) • intermediateChannel d lam X +
      ((((1 - lam) / ((1 + ((d : ℝ) - 1) * lam) * d)) : ℝ) : ℂ) •
        ∑ k : Fin d, conjSuperop ((clockUnitary d ^ (k.val + 1))ᴴ) (intermediateChannel d lam X) := by
  have hd1 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hD : 0 < 1 + ((d : ℝ) - 1) * lam := by
    have h1 : (0 : ℝ) < (d : ℝ)^2 - 1 := by nlinarith
    have : -1 ≤ lam * ((d : ℝ)^2 - 1) := by
      rw [div_le_iff₀ h1] at hlow; linarith
    nlinarith
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  have hDC : ((1 + ((d : ℝ) - 1) * lam : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, g73j_clock_sum, g73j_inter_entry,
    g73j_depol_entry]
  push_cast at hDC ⊢
  have h2 : (1 + (d:ℂ) * lam - lam) ≠ 0 := by intro h; apply hDC; linear_combination h
  have h3 : (1 - (lam:ℂ) + lam * d) ≠ 0 := by intro h; apply hDC; linear_combination h
  split_ifs with h
  · field_simp; ring_nf; field_simp; ring
  · field_simp; ring_nf; field_simp; ring

/-- King quant-ph/0204172v2, PDF pp.13-16, Lemma 11, (54)-(57).
The concrete constructed columns are orthonormal and uniform; neither is assumed. -/
theorem solution {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (lam : ℝ) (hlow : -1 / ((d : ℝ) - 1) ≤ lam) (hhigh : lam ≤ 1) :
    (∀ a : Fin (2 * d^2),
      (constructedUniformBasis d (a.val + 1))ᴴ * constructedUniformBasis d (a.val + 1) = 1 ∧
      IsUniformBasis (constructedUniformBasis d (a.val + 1)) ∧
      IsChannel (constructedPhaseDamping d lam (a.val + 1))) ∧
    ∀ X : Matrix (Fin d) (Fin d) ℂ,
      intermediateChannel d lam X = (((2 * d^2 : ℕ) : ℂ)⁻¹) •
        ∑ a : Fin (2 * d^2), constructedPhaseDamping d lam (a.val + 1) X := by
  have hd1 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : 0 ≤ 1 + ((d : ℝ) - 1) * lam := by
    have hp : (0 : ℝ) < (d : ℝ) - 1 := by linarith
    rw [div_le_iff₀ hp] at hlow; linarith
  refine ⟨fun a => ⟨g73j_basis_unitary d _, g73j_basis_uniform d _, ?_⟩, fun X => g73j_average d lam X⟩
  unfold constructedPhaseDamping
  exact g73j_phase_channel _ (g73j_basis_unitary d _) lam h1 hhigh



end
