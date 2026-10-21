-- Prove2me | solution 1 for ShapeMoment.LogConcave.proposition_2_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:46:06.581207+00:00
-- url     : https://prove2.me/submissions/1a58f518-d5ec-425a-a7e6-08679f511a37

import Mathlib
set_option autoImplicit false

noncomputable def GG (u v : ℕ) (x y : ℝ) : ℝ :=
  x ^ ((u : ℝ) / (u + v : ℕ)) * y ^ ((v : ℝ) / (u + v : ℕ))

lemma GG_nonneg (u v : ℕ) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ GG u v x y := by
  unfold GG
  exact mul_nonneg (Real.rpow_nonneg hx _) (Real.rpow_nonneg hy _)

lemma GG_pow (u v : ℕ) (hu : 0 < u) (hv : 0 < v) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    GG u v x y ^ (u + v) = x ^ u * y ^ v := by
  unfold GG
  have hn : ((u + v : ℕ) : ℝ) ≠ 0 := by positivity
  rw [mul_pow, ← Real.rpow_natCast (x ^ _), ← Real.rpow_natCast (y ^ _),
    ← Real.rpow_mul hx, ← Real.rpow_mul hy, div_mul_cancel₀ _ hn, div_mul_cancel₀ _ hn]
  simp

lemma GG_homog (u v : ℕ) (c x y : ℝ) (hc : 0 ≤ c) (hx : 0 ≤ x) (hy : 0 ≤ y) (hu : 0 < u) (hv : 0 < v) :
    GG u v (c * x) (c * y) = c * GG u v x y := by
  unfold GG
  rw [Real.mul_rpow hc hx, Real.mul_rpow hc hy]
  have : c ^ ((u : ℝ) / (u + v : ℕ)) * c ^ ((v : ℝ) / (u + v : ℕ)) = c := by
    rw [← Real.rpow_add' hc]
    · have hn : ((u + v : ℕ) : ℝ) ≠ 0 := by positivity
      have : (u : ℝ) / (u + v : ℕ) + (v : ℝ) / (u + v : ℕ) = 1 := by
        rw [← add_div]; push_cast; exact div_self (by exact_mod_cast hn)
      rw [this]; simp
    · have : (0:ℝ) < (u : ℝ) / (u + v : ℕ) := by positivity
      have : (0:ℝ) < (v : ℝ) / (u + v : ℕ) := by positivity
      linarith
  calc _ = (c ^ ((u : ℝ) / (u + v : ℕ)) * c ^ ((v : ℝ) / (u + v : ℕ))) *
        (x ^ ((u : ℝ) / (u + v : ℕ)) * y ^ ((v : ℝ) / (u + v : ℕ))) := by ring
    _ = _ := by rw [this]

lemma GG_super (u v : ℕ) (hu : 0 < u) (hv : 0 < v) (x y x' y' : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hx' : 0 ≤ x') (hy' : 0 ≤ y') :
    GG u v x y + GG u v x' y' ≤ GG u v (x + x') (y + y') := by
  have hn : (0:ℝ) < ((u + v : ℕ) : ℝ) := by positivity
  set a : ℝ := (u : ℝ) / (u + v : ℕ) with ha
  set b : ℝ := (v : ℝ) / (u + v : ℕ) with hb
  have ha0 : 0 < a := by positivity
  have hb0 : 0 < b := by positivity
  have hab : a + b = 1 := by
    rw [ha, hb, ← add_div]; push_cast; exact div_self (by exact_mod_cast hn.ne')
  -- single-term bound
  have key : ∀ (p q S T : ℝ), 0 ≤ p → 0 ≤ q → p ≤ S → q ≤ T → 0 < S → 0 < T →
      p ^ a * q ^ b ≤ S ^ a * T ^ b * (a * (p / S) + b * (q / T)) := by
    intro p q S T hp hq hpS hqT hS hT
    have h := Real.geom_mean_le_arith_mean2_weighted ha0.le hb0.le (div_nonneg hp hS.le)
      (div_nonneg hq hT.le) hab
    rw [Real.div_rpow hp hS.le, Real.div_rpow hq hT.le] at h
    have hSa : 0 < S ^ a := Real.rpow_pos_of_pos hS _
    have hTb : 0 < T ^ b := Real.rpow_pos_of_pos hT _
    have h2 : p ^ a * q ^ b = S ^ a * T ^ b * (p ^ a / S ^ a * (q ^ b / T ^ b)) := by
      field_simp
    rw [h2]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  unfold GG
  rw [← ha, ← hb]
  have hR : 0 ≤ (x + x') ^ a * (y + y') ^ b :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _)
  rcases (add_nonneg hx hx').eq_or_lt with hS | hS
  · have h1 : x = 0 := by linarith
    have h2 : x' = 0 := by linarith
    subst h1 h2
    simp [Real.zero_rpow ha0.ne']
  rcases (add_nonneg hy hy').eq_or_lt with hT | hT
  · have h1 : y = 0 := by linarith
    have h2 : y' = 0 := by linarith
    subst h1 h2
    simp [Real.zero_rpow hb0.ne']
  have k1 := key x y (x + x') (y + y') hx hy (by linarith) (by linarith) hS hT
  have k2 := key x' y' (x + x') (y + y') hx' hy' (by linarith) (by linarith) hS hT
  have e : a * (x / (x + x')) + b * (y / (y + y')) + (a * (x' / (x + x')) + b * (y' / (y + y'))) = 1 := by
    have : x / (x + x') + x' / (x + x') = 1 := by rw [← add_div]; exact div_self hS.ne'
    have : y / (y + y') + y' / (y + y') = 1 := by rw [← add_div]; exact div_self hT.ne'
    nlinarith
  calc _ ≤ _ + _ := add_le_add k1 k2
    _ = (x + x') ^ a * (y + y') ^ b * (a * (x / (x + x')) + b * (y / (y + y')) + (a * (x' / (x + x')) + b * (y' / (y + y')))) := by ring
    _ = _ := by rw [e, mul_one]

lemma GG_conv (u v : ℕ) (hu : 0 < u) (hv : 0 < v) (x y x' y' s t : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hx' : 0 ≤ x') (hy' : 0 ≤ y') (hs : 0 ≤ s) (ht : 0 ≤ t) :
    s * GG u v x y + t * GG u v x' y' ≤ GG u v (s * x + t * x') (s * y + t * y') := by
  rw [← GG_homog u v s x y hs hx hy hu hv, ← GG_homog u v t x' y' ht hx' hy' hu hv]
  exact GG_super u v hu hv _ _ _ _ (mul_nonneg hs hx) (mul_nonneg hs hy) (mul_nonneg ht hx')
    (mul_nonneg ht hy')

lemma lt_iff_GG (u v : ℕ) (hu : 0 < u) (hv : 0 < v) (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) : z ^ (u + v) < x ^ u * y ^ v ↔ z < GG u v x y := by
  rw [← GG_pow u v hu hv x y hx hy]
  exact pow_lt_pow_iff_left₀ hz (GG_nonneg u v x y hx hy) (by omega)

lemma le_iff_GG (u v : ℕ) (hu : 0 < u) (hv : 0 < v) (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) : z ^ (u + v) ≤ x ^ u * y ^ v ↔ z ≤ GG u v x y := by
  rw [← GG_pow u v hu hv x y hx hy]
  exact pow_le_pow_iff_left₀ hz (GG_nonneg u v x y hx hy) (by omega)

theorem solution (u v : ℕ) (hu : 0 < u) (hv : 0 < v) :
    Convex ℝ {p : ℝ × ℝ × ℝ |
      p.2.2 ^ (u + v) < p.1 ^ u * p.2.1 ^ v ∧
      0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2} := by
  intro p hp q hq s t hs ht hst
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
  obtain ⟨hq1, hq2, hq3, hq4⟩ := hq
  simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  have hz : 0 ≤ s * p.2.2 + t * q.2.2 := by positivity
  have hx : 0 ≤ s * p.1 + t * q.1 := by positivity
  have hy : 0 ≤ s * p.2.1 + t * q.2.1 := by positivity
  refine ⟨?_, hx, hy, hz⟩
  rw [lt_iff_GG u v hu hv _ _ _ hx hy hz]
  rw [lt_iff_GG u v hu hv _ _ _ hp2 hp3 hp4] at hp1
  rw [lt_iff_GG u v hu hv _ _ _ hq2 hq3 hq4] at hq1
  have h := GG_conv u v hu hv p.1 p.2.1 q.1 q.2.1 s t hp2 hp3 hq2 hq3 hs ht
  rcases hs.eq_or_lt with h0 | h0
  · subst h0
    have : t = 1 := by linarith
    subst this
    simp only [zero_mul, zero_add, one_mul] at h ⊢
    linarith
  · nlinarith [mul_pos h0 (sub_pos.2 hp1), mul_nonneg ht (sub_pos.2 hq1).le]
