-- Prove2me | solution 1 for PolySwap.KMS.lemma_3_7
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-16T20:26:01.202088+00:00
-- url     : https://prove2.me/submissions/dce744a0-f295-4f06-a9d2-966616b194c1

import Mathlib
import Definitions.Def_PolySwap_KMS_Complex
import Definitions.Def_PolySwap_KMS_Dehn
import Definitions.Def_PolySwap_KMS_KMSComplex

section Part_Base

open Classical

noncomputable section

namespace PolySwap.KMS.L37

open PolySwap.KMS

/-- The colour sets `([d] choose r+1)`. -/
def Cs (d r : ℕ) : Finset (Finset ℕ) := (Finset.range (d + 1)).powersetCard (r + 1)

/-- Ordered `T`-tuples from `C`. -/
def Tup (C : Finset (Finset ℕ)) (T : ℕ) : Finset (Fin T → Finset ℕ) :=
  Fintype.piFinset fun _ => C

/-- Pairwise disjointness of a tuple. -/
def Disj {T : ℕ} (f : Fin T → Finset ℕ) : Prop := ∀ i j, i ≠ j → Disjoint (f i) (f j)

/-- Requirement codes `(type, ℓ, ℓ', s, s')`. -/
def Qs (r : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  Finset.range 4 ×ˢ Finset.range (r + 1) ×ˢ Finset.range (r + 1) ×ˢ Finset.range 4 ×ˢ
    Finset.range 4

/-- `K` witnesses requirement `q` (conditions (b)–(e) of `IsNice`) for `J`. -/
def Good (d : ℕ) (q : ℕ × ℕ × ℕ × ℕ × ℕ) (J K : Finset ℕ) : Prop :=
  if q.1 = 0 then
    binLo d J q.2.1 ≤ binHi d J q.2.1 → ∀ c ∈ rl d J K, c ∈ bin d J q.2.1 →
      c ≤ binLo d J q.2.1 + (binHi d J q.2.1 - binLo d J q.2.1) / 5
  else if q.1 = 1 then
    binLo d J q.2.1 ≤ binHi d J q.2.1 → ∀ c ∈ rl d J K, c ∈ bin d J q.2.1 →
      binHi d J q.2.1 - (binHi d J q.2.1 - binLo d J q.2.1) / 5 ≤ c
  else if q.1 = 2 then
    binLo d J q.2.1 ≤ binHi d J q.2.1 → ∀ c ∈ rl d J K, c ∈ bin d J q.2.1 →
      binLo d J q.2.1 + 2 * ((binHi d J q.2.1 - binLo d J q.2.1 + 4) / 5) ≤ c ∧
        c ≤ binLo d J q.2.1 + 3 * ((binHi d J q.2.1 - binLo d J q.2.1) / 5)
  else
    binLo d J q.2.1 ≤ binHi d J q.2.1 → binLo d J q.2.2.1 ≤ binHi d J q.2.2.1 →
      Disjoint (rl d J K) (window (binLo d J q.2.1) (binHi d J q.2.1) q.2.2.2.1) ∧
      Disjoint (rl d J K) (window (binLo d J q.2.2.1) (binHi d J q.2.2.1) q.2.2.2.2)

/-- Some bin of `J` has more than `M` colours. -/
def BigBin (d M : ℕ) (J : Finset ℕ) : Prop :=
  ∃ ℓ < J.card, binLo d J ℓ ≤ binHi d J ℓ ∧ M < binHi d J ℓ - binLo d J ℓ + 1

/-- Some nonempty bin of `J` violates condition (a). -/
def ShortGap (d : ℕ) (J : Finset ℕ) : Prop :=
  ∃ ℓ < J.card, binLo d J ℓ ≤ binHi d J ℓ ∧ binHi d J ℓ - binLo d J ℓ ≤ 100

end PolySwap.KMS.L37
end
end Part_Base

section Part_NumAux

namespace PolySwap.KMS.L37.NumAux

open Nat

lemma descFactorial_mul_pow_le (k d : ℕ) (h : k ≤ d) : ∀ r : ℕ,
    k.descFactorial r * d ^ r ≤ k ^ r * d.descFactorial r
  | 0 => by simp
  | r + 1 => by
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, pow_succ, pow_succ]
    have ih := descFactorial_mul_pow_le k d h r
    have h2 : (k - r) * d ≤ k * (d - r) := by
      rcases Nat.lt_or_ge k r with hk | hk
      · simp [Nat.sub_eq_zero_of_le hk.le]
      · have hrd : r ≤ d := hk.trans h
        zify [hk, hrd]
        nlinarith
    calc (k - r) * k.descFactorial r * (d ^ r * d)
        = ((k - r) * d) * (k.descFactorial r * d ^ r) := by ring
      _ ≤ (k * (d - r)) * (k ^ r * d.descFactorial r) := Nat.mul_le_mul h2 ih
      _ = k ^ r * k * ((d - r) * d.descFactorial r) := by ring

lemma choose_mul_pow_le (k d r : ℕ) (h : k ≤ d) :
    k.choose r * d ^ r ≤ k ^ r * d.choose r := by
  have := descFactorial_mul_pow_le k d h r
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose] at this
  refine le_of_mul_le_mul_left ?_ (Nat.factorial_pos r)
  calc r ! * (k.choose r * d ^ r) = r ! * k.choose r * d ^ r := by ring
    _ ≤ k ^ r * (r ! * d.choose r) := this
    _ = r ! * (k ^ r * d.choose r) := by ring

lemma pow_mul_choose_le (m N k : ℕ) :
    (m + 1 - k) ^ k * N.choose k ≤ N ^ k * m.choose k := by
  have h1 := Nat.pow_sub_le_descFactorial m k
  have h2 := Nat.descFactorial_le_pow N k
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h1 h2
  refine le_of_mul_le_mul_left ?_ (Nat.factorial_pos k)
  calc k ! * ((m + 1 - k) ^ k * N.choose k) = (m + 1 - k) ^ k * (k ! * N.choose k) := by ring
    _ ≤ (k ! * m.choose k) * N ^ k := Nat.mul_le_mul h1 h2
    _ = k ! * (N ^ k * m.choose k) := by ring

lemma amgm (x : ℝ) (hx : 0 ≤ x) : x ^ 4 ≤ ((1 + 4 * x) / 5) ^ 5 := by
  have : 0 ≤ (x - 1) ^ 2 * (1024 * x ^ 3 + 203 * x ^ 2 + 22 * x + 1) := by positivity
  nlinarith [this]

lemma p_lower (r : ℕ) (D K Y A p : ℝ) (hD : 0 < D) (hK : 0 < K) (hKD : K ≤ D) (hA : 0 < A)
    (hx : D ^ r < A * K ^ r) (hY : (D + 4 * K) / 5 - 19 - r ≤ Y)
    (hp : (Y / (D + 1)) ^ (r + 1) ≤ p) (hbig : 10 * ((r : ℝ) + 20) * (r + 1) ≤ D + 1) :
    1 / (100000 * A ^ 4) ≤ p ^ 5 := by
  set x := K / D with hxdef
  set θ := (1 + 4 * x) / 5 with hθ
  set ε := ((r : ℝ) + 20) / (D + 1) with hε
  have hx0 : 0 < x := div_pos hK hD
  have hx1 : x ≤ 1 := (div_le_one hD).2 hKD
  have hθ1 : θ ≤ 1 := by rw [hθ]; linarith
  have hθ0 : 1 / 5 ≤ θ := by rw [hθ]; linarith
  have hD1 : 0 < D + 1 := by linarith
  have hε0 : 0 ≤ ε := by positivity
  have hεD : ε * (D + 1) = r + 20 := by rw [hε]; field_simp
  have hε1 : 5 * ε * (r + 1) ≤ 1 / 2 := by
    have : 5 * ε * (r + 1) = 5 * (((r : ℝ) + 20) * (r + 1)) / (D + 1) := by rw [hε]; ring
    rw [this, div_le_iff₀ hD1]; linarith
  have hε2 : 5 * ε ≤ 1 / 2 := by
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    nlinarith
  have hθD : θ * D = (D + 4 * K) / 5 := by rw [hθ, hxdef]; field_simp
  have hy : θ - ε ≤ Y / (D + 1) := by
    rw [le_div_iff₀ hD1]
    have : (θ - ε) * (D + 1) = θ * D + θ - (r + 20) := by rw [sub_mul, hεD]; ring
    rw [this, hθD]; linarith
  have hy2 : θ * (1 - 5 * ε) ≤ Y / (D + 1) := by
    have : 0 ≤ ε * (5 * θ - 1) := mul_nonneg hε0 (by linarith)
    nlinarith
  have hbern : 1 / 2 ≤ (1 - 5 * ε) ^ (r + 1) := by
    have := one_add_mul_le_pow (a := -(5 * ε)) (by linarith) (r + 1)
    push_cast at this
    have h' : (1 : ℝ) + -(5 * ε) = 1 - 5 * ε := by ring
    rw [h'] at this
    nlinarith
  have hp2 : θ ^ r * θ / 2 ≤ p := by
    have h1 : (θ * (1 - 5 * ε)) ^ (r + 1) ≤ (Y / (D + 1)) ^ (r + 1) :=
      pow_le_pow_left₀ (mul_nonneg (by linarith) (by linarith)) hy2 _
    rw [mul_pow, pow_succ] at h1
    have : 0 ≤ θ ^ r * θ := by positivity
    nlinarith
  have hxr : 1 / A < x ^ r := by
    rw [hxdef, div_pow, div_lt_div_iff₀ hA (by positivity)]; linarith
  have hu : (1 / A) ^ 4 ≤ (θ ^ r) ^ 5 := by
    calc (1 / A) ^ 4 ≤ (x ^ r) ^ 4 := pow_le_pow_left₀ (by positivity) hxr.le _
      _ = (x ^ 4) ^ r := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ (θ ^ 5) ^ r := pow_le_pow_left₀ (by positivity) (amgm x hx0.le) _
      _ = (θ ^ r) ^ 5 := by rw [← pow_mul, ← pow_mul, mul_comm]
  have hθ5 : (1 / 5 : ℝ) ^ 5 ≤ θ ^ 5 := pow_le_pow_left₀ (by norm_num) hθ0 _
  calc 1 / (100000 * A ^ 4) = (1 / A) ^ 4 * (1 / 5) ^ 5 / 32 := by field_simp; norm_num
    _ ≤ (θ ^ r) ^ 5 * θ ^ 5 / 32 := by gcongr
    _ = (θ ^ r * θ / 2) ^ 5 := by ring
    _ ≤ p ^ 5 := pow_le_pow_left₀ (by positivity) hp2 _

lemma big_const :
    (5120 : ℝ) * (100 ! : ℕ) * (100000 * 40 ^ 4) ^ 20 * 2 ^ 82 ≤ (10 ^ 4) ^ 108 := by
  norm_num [Nat.factorial]

lemma one_sub_pow_le_exp (p : ℝ) (N : ℕ) (hp1 : p ≤ 1) :
    (1 - p) ^ N ≤ Real.exp (-(p * N)) := by
  have h1 : 1 - p ≤ Real.exp (-p) := by linarith [Real.add_one_le_exp (-p)]
  calc (1 - p) ^ N ≤ Real.exp (-p) ^ N := pow_le_pow_left₀ (by linarith) h1 _
    _ = Real.exp ((N : ℝ) * (-p)) := (Real.exp_nat_mul _ _).symm
    _ = Real.exp (-(p * N)) := by ring_nf

lemma sub_one_pow (t : ℝ) (ht : 200 ≤ t) : t ^ 100 / 2 ≤ (t - 1) ^ 100 := by
  have ht0 : 0 < t := by linarith
  have hb := one_add_mul_le_pow (a := -(1 / t)) (by
    have : 1 / t ≤ 1 := by rw [div_le_one ht0]; linarith
    linarith) 100
  have h1 : (1 : ℝ) / 2 ≤ 1 + ((100 : ℕ) : ℝ) * -(1 / t) := by
    have : 100 / t ≤ 1 / 2 := by rw [div_le_iff₀ ht0]; linarith
    push_cast; rw [mul_neg, mul_one_div]; linarith
  have h2 : (t - 1) ^ 100 = t ^ 100 * (1 + -(1 / t)) ^ 100 := by
    rw [← mul_pow]; congr 1; field_simp; ring
  rw [h2]
  calc t ^ 100 / 2 = t ^ 100 * (1 / 2) := by ring
    _ ≤ t ^ 100 * (1 + -(1 / t)) ^ 100 := by gcongr; exact h1.trans hb

lemma core (G ρ t : ℝ) (hG : 0 ≤ G) (hGbig : G * 2 ^ 82 ≤ (10 ^ 4) ^ 108)
    (hρ : 10 ^ 4 ≤ ρ) (ht : ρ ^ 10 ≤ t) : G * (ρ + 1) ^ 82 ≤ t ^ 19 := by
  have hρ0 : 0 < ρ := by linarith
  have h1 : (ρ + 1) ^ 82 ≤ 2 ^ 82 * ρ ^ 82 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have h2 : ((10 : ℝ) ^ 4) ^ 108 ≤ ρ ^ 108 := pow_le_pow_left₀ (by norm_num) hρ _
  have h3 : ρ ^ 190 ≤ t ^ 19 := by
    calc ρ ^ 190 = (ρ ^ 10) ^ 19 := by rw [← pow_mul]
      _ ≤ t ^ 19 := pow_le_pow_left₀ (by positivity) ht _
  have hρ82 : 0 < ρ ^ 82 := by positivity
  calc G * (ρ + 1) ^ 82 ≤ G * (2 ^ 82 * ρ ^ 82) := mul_le_mul_of_nonneg_left h1 hG
    _ = (G * 2 ^ 82) * ρ ^ 82 := by ring
    _ ≤ ((10 : ℝ) ^ 4) ^ 108 * ρ ^ 82 := mul_le_mul_of_nonneg_right hGbig hρ82.le
    _ ≤ ρ ^ 108 * ρ ^ 82 := mul_le_mul_of_nonneg_right h2 hρ82.le
    _ = ρ ^ 190 := by ring
    _ ≤ t ^ 19 := h3

lemma kz (c F ρ t p : ℝ) (ht : 200 ≤ t) (hc : 0 < c) (hρ : 0 ≤ ρ)
    (hpB : 1 ≤ p ^ 5 * (c * t ^ 4 * (ρ + 1) ^ 4))
    (hcore : 5120 * F * c ^ 20 * (ρ + 1) ^ 82 ≤ t ^ 19) :
    2560 * t * (ρ + 1) ^ 2 * F ≤ (p * (t - 1)) ^ 100 := by
  have ht0 : 0 < t := by linarith
  set B := c * t ^ 4 * (ρ + 1) ^ 4 with hB
  have hB20 : 0 < B ^ 20 := by positivity
  refine le_of_mul_le_mul_right ?_ hB20
  have e1 : 2560 * t * (ρ + 1) ^ 2 * F * B ^ 20 =
      (5120 * F * c ^ 20 * (ρ + 1) ^ 82) * t ^ 81 / 2 := by
    rw [hB]; ring
  have e2 : (p * (t - 1)) ^ 100 * B ^ 20 = (p ^ 5 * B) ^ 20 * (t - 1) ^ 100 :=
    (fun u : ℝ => (by ring : (p * u) ^ 100 * B ^ 20 = (p ^ 5 * B) ^ 20 * u ^ 100)) (t - 1)
  rw [e1, e2]
  have ht81 : 0 < t ^ 81 := by positivity
  have hpow : 1 ≤ (p ^ 5 * B) ^ 20 := one_le_pow₀ hpB
  have htm0 : 0 ≤ (t - 1) ^ 100 := pow_nonneg (by linarith) _
  calc (5120 * F * c ^ 20 * (ρ + 1) ^ 82) * t ^ 81 / 2
      ≤ t ^ 19 * t ^ 81 / 2 := by
        have := mul_le_mul_of_nonneg_right hcore ht81.le
        linarith
    _ = t ^ 100 / 2 := by ring
    _ ≤ (t - 1) ^ 100 := sub_one_pow t ht
    _ ≤ (p ^ 5 * B) ^ 20 * (t - 1) ^ 100 := le_mul_of_one_le_left htm0 hpow

lemma exp_bound_aux (F : ℝ) (hF0 : 0 < F)
    (hFbig : (5120 : ℝ) * F * (100000 * 40 ^ 4) ^ 20 * 2 ^ 82 ≤ (10 ^ 4) ^ 108)
    (hFe : ∀ z : ℝ, 0 ≤ z → z ^ 100 / F ≤ Real.exp z)
    (r T : ℕ) (p : ℝ) (hr : 10 ^ 4 ≤ r) (hT : r ^ 10 ≤ T) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (hp : 1 / (100000 * (40 * (T : ℝ) * (r + 1)) ^ 4) ≤ p ^ 5) :
    2560 * (T : ℝ) * (r + 1) ^ 2 * (1 - p) ^ (T - 1) ≤ 1 := by
  have hT1 : 1 ≤ T := by
    have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
    have h1 : 1 ≤ r ^ 10 := Nat.one_le_pow _ _ hr0
    omega
  have hρ : (10 : ℝ) ^ 4 ≤ (r : ℝ) := by exact_mod_cast hr
  have ht : (r : ℝ) ^ 10 ≤ (T : ℝ) := by exact_mod_cast hT
  have ht200 : (200 : ℝ) ≤ T := by
    have : ((10 : ℝ) ^ 4) ^ 10 ≤ (r : ℝ) ^ 10 := pow_le_pow_left₀ (by norm_num) hρ _
    have h4 : (200 : ℝ) ≤ ((10 : ℝ) ^ 4) ^ 10 := by norm_num
    linarith
  have hN : ((T - 1 : ℕ) : ℝ) = (T : ℝ) - 1 := by rw [Nat.cast_sub hT1]; simp
  have hexp := one_sub_pow_le_exp p (T - 1) hp1
  rw [hN] at hexp
  have hz0 : 0 ≤ p * ((T : ℝ) - 1) := mul_nonneg hp0 (by linarith)
  have hρ0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hB0 : 0 < 100000 * (40 * (T : ℝ) * (r + 1)) ^ 4 := by positivity
  have hpB : 1 ≤ p ^ 5 * (((100000 : ℝ) * 40 ^ 4) * (T : ℝ) ^ 4 * ((r : ℝ) + 1) ^ 4) := by
    have := mul_le_mul_of_nonneg_right hp hB0.le
    rw [one_div, inv_mul_cancel₀ hB0.ne'] at this
    have e : (100000 : ℝ) * (40 * (T : ℝ) * (r + 1)) ^ 4 =
        ((100000 : ℝ) * 40 ^ 4) * (T : ℝ) ^ 4 * ((r : ℝ) + 1) ^ 4 := by ring
    rwa [e] at this
  have hG : (0 : ℝ) ≤ 5120 * F * (100000 * 40 ^ 4) ^ 20 := by positivity
  have hcore := core _ (r : ℝ) (T : ℝ) hG hFbig hρ ht
  have hKz := kz ((100000 : ℝ) * 40 ^ 4) F (r : ℝ) (T : ℝ) p ht200 (by norm_num) hρ0 hpB hcore
  have hKe : 2560 * (T : ℝ) * (r + 1) ^ 2 ≤ Real.exp (p * ((T : ℝ) - 1)) := by
    have := hFe _ hz0
    rw [div_le_iff₀ hF0] at this
    exact le_of_mul_le_mul_right (hKz.trans this) hF0
  have hK0 : (0 : ℝ) ≤ 2560 * (T : ℝ) * (r + 1) ^ 2 := by positivity
  calc 2560 * (T : ℝ) * (r + 1) ^ 2 * (1 - p) ^ (T - 1)
      ≤ 2560 * (T : ℝ) * (r + 1) ^ 2 * Real.exp (-(p * ((T : ℝ) - 1))) :=
        mul_le_mul_of_nonneg_left hexp hK0
    _ = 2560 * (T : ℝ) * (r + 1) ^ 2 / Real.exp (p * ((T : ℝ) - 1)) := by
        rw [Real.exp_neg, div_eq_mul_inv]
    _ ≤ 1 := by rw [div_le_one (Real.exp_pos _)]; exact hKe

lemma exp_bound (r T : ℕ) (p : ℝ) (hr : 10 ^ 4 ≤ r) (hT : r ^ 10 ≤ T) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (hp : 1 / (100000 * (40 * (T : ℝ) * (r + 1)) ^ 4) ≤ p ^ 5) :
    2560 * (T : ℝ) * (r + 1) ^ 2 * (1 - p) ^ (T - 1) ≤ 1 :=
  exp_bound_aux ((100 ! : ℕ) : ℝ) (by exact_mod_cast Nat.factorial_pos 100) big_const
    (fun z hz => Real.pow_div_factorial_le_exp z hz 100) r T p hr hT hp0 hp1 hp


lemma term3 (r T d k0 : ℕ) (hr : 10 ^ 4 ≤ r) (hT : r ^ 10 ≤ T)
    (hdbig : 41 * 41 * 100 * (r + 1) ^ 2 ≤ d) (hk0pos : 1 ≤ k0) (hk0d : k0 ≤ d)
    (hdk : d ^ r < 40 * T * (r + 1) * k0 ^ r) :
    2560 * T * (r + 1) ^ 2 *
      ((d + 1).choose (r + 1) - (d + 1 - (4 * (d - k0) / 5 + 20)).choose (r + 1)) ^ (T - 1) ≤
      (d + 1).choose (r + 1) ^ (T - 1) := by
  generalize hm : d + 1 - (4 * (d - k0) / 5 + 20) = m
  generalize hn : (d + 1).choose (r + 1) = n
  generalize hg : m.choose (r + 1) = g
  have hr0 : 1 ≤ r := le_trans (by norm_num) hr
  have hdr5 : 5 * r + 200 ≤ d := by nlinarith
  have hnpos : 0 < n := hn ▸ Nat.choose_pos (by omega)
  have hmd : m ≤ d + 1 := by omega
  have hgn : g ≤ n := hg ▸ hn ▸ Nat.choose_le_choose _ hmd
  have hlow := pow_mul_choose_le m (d + 1) (r + 1)
  rw [show m + 1 - (r + 1) = m - r by omega, hn, hg] at hlow
  have h5 : d + 4 * k0 ≤ 5 * (m - r) + 95 + 5 * r := by omega
  have hbigN : 10 * (r + 20) * (r + 1) ≤ d + 1 := by nlinarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = (g : ℝ) / n := ⟨_, rfl⟩
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hp1 : p ≤ 1 := hp ▸ div_le_one_of_le₀ (by exact_mod_cast hgn) hnR.le
  have hpow : 1 / (100000 * (40 * (T : ℝ) * (r + 1)) ^ 4) ≤ p ^ 5 := by
    refine p_lower r d k0 ((m - r : ℕ) : ℝ) (40 * (T : ℝ) * (r + 1)) p
      (by exact_mod_cast (show 0 < d by omega)) (by exact_mod_cast hk0pos)
      (by exact_mod_cast hk0d) (by
        have : 0 < T := lt_of_lt_of_le (Nat.pow_pos (n := 10) (show 0 < r by omega)) hT
        positivity) (by exact_mod_cast hdk)
      ?_ ?_ (by exact_mod_cast hbigN)
    · have : ((d + 4 * k0 : ℕ) : ℝ) ≤ ((5 * (m - r) + 95 + 5 * r : ℕ) : ℝ) := by
        exact_mod_cast h5
      push_cast at this
      linarith
    · have hl : (((m - r : ℕ) : ℝ)) ^ (r + 1) * n ≤ ((d : ℝ) + 1) ^ (r + 1) * g := by
        exact_mod_cast hlow
      have hD1 : (0 : ℝ) < ((d : ℝ) + 1) ^ (r + 1) := by positivity
      rw [div_pow, hp, div_le_div_iff₀ hD1 hnR]
      linarith
  have hE := exp_bound r T p hr hT hp0 hp1 hpow
  have hng : ((n - g : ℕ) : ℝ) = n * (1 - p) := by
    rw [Nat.cast_sub hgn, hp]; field_simp
  rw [← Nat.cast_le (α := ℝ)]
  push_cast
  rw [hng]
  have hnT : (0 : ℝ) ≤ (n : ℝ) ^ (T - 1) := by positivity
  calc 2560 * (T : ℝ) * ((r : ℝ) + 1) ^ 2 * ((n : ℝ) * (1 - p)) ^ (T - 1)
      = (2560 * (T : ℝ) * ((r : ℝ) + 1) ^ 2 * (1 - p) ^ (T - 1)) * (n : ℝ) ^ (T - 1) := by
        rw [mul_pow]; ring
    _ ≤ 1 * (n : ℝ) ^ (T - 1) := mul_le_mul_of_nonneg_right hE hnT
    _ = (n : ℝ) ^ (T - 1) := one_mul _

lemma term1 (r T d s : ℕ) (hs : 40 * T * (r + 1) * s.choose r ≤ d.choose r) :
    40 * T * (d + 1) * s.choose r ≤ (d + 1).choose (r + 1) := by
  have hn_id := Nat.add_one_mul_choose_eq d r
  refine le_of_mul_le_mul_right ?_ (show 0 < r + 1 by omega)
  calc 40 * T * (d + 1) * s.choose r * (r + 1)
      = (d + 1) * (40 * T * (r + 1) * s.choose r) := by ring
    _ ≤ (d + 1) * d.choose r := Nat.mul_le_mul_left _ hs
    _ = (d + 1).choose (r + 1) * (r + 1) := hn_id

lemma term2 (r T d : ℕ) (hr0 : 1 ≤ r) (hT41 : 41 ≤ T) (hX : 100 * ((r + 1) * T) ^ 2 ≤ d) :
    4040 * T * (d + 1) * (d - 1).choose (r - 1) ≤ (d + 1).choose (r + 1) := by
  have hn_id := Nat.add_one_mul_choose_eq d r
  have hd1 : 1 ≤ d := by
    have h1 : 0 < (r + 1) * T := by positivity
    have h2 : 0 < ((r + 1) * T) ^ 2 := by positivity
    omega
  have hdc : d * (d - 1).choose (r - 1) = d.choose r * r := by
    have := Nat.add_one_mul_choose_eq (d - 1) (r - 1)
    rwa [Nat.sub_add_cancel hd1, Nat.sub_add_cancel hr0] at this
  refine le_of_mul_le_mul_right ?_ (show 0 < d by omega)
  have h1 : 4040 * T * r * (r + 1) ≤ d := by
    have : 4040 * r ≤ 100 * (r + 1) * T := by nlinarith
    calc 4040 * T * r * (r + 1) = (4040 * r) * ((r + 1) * T) := by ring
      _ ≤ (100 * (r + 1) * T) * ((r + 1) * T) := Nat.mul_le_mul_right _ this
      _ = 100 * ((r + 1) * T) ^ 2 := by ring
      _ ≤ d := hX
  calc 4040 * T * (d + 1) * (d - 1).choose (r - 1) * d
      = 4040 * T * (d + 1) * (d * (d - 1).choose (r - 1)) := by ring
    _ = 4040 * T * r * ((d + 1) * d.choose r) := by rw [hdc]; ring
    _ = (4040 * T * r * (r + 1)) * (d + 1).choose (r + 1) := by rw [hn_id]; ring
    _ ≤ d * (d + 1).choose (r + 1) := Nat.mul_le_mul_right _ h1
    _ = (d + 1).choose (r + 1) * d := by ring

lemma term4 (r T d : ℕ) (hX : 100 * ((r + 1) * T) ^ 2 ≤ d) :
    4 * T * T * (r + 1) * d.choose r ≤ (d + 1).choose (r + 1) := by
  have hn_id := Nat.add_one_mul_choose_eq d r
  refine le_of_mul_le_mul_right ?_ (show 0 < d + 1 by omega)
  have h1 : 4 * T * T * (r + 1) * (r + 1) ≤ d + 1 := by nlinarith
  calc 4 * T * T * (r + 1) * d.choose r * (d + 1)
      = 4 * T * T * (r + 1) * ((d + 1) * d.choose r) := by ring
    _ = (4 * T * T * (r + 1) * (r + 1)) * (d + 1).choose (r + 1) := by rw [hn_id]; ring
    _ ≤ (d + 1) * (d + 1).choose (r + 1) := Nat.mul_le_mul_right _ h1
    _ = (d + 1).choose (r + 1) * (d + 1) := by ring

lemma assemble (T n a b c e P Q G : ℕ) (hT2 : 2 ≤ T) (hP : n ^ (T - 1) = P)
    (hQ : n ^ (T - 2) = Q)
    (ha : 40 * a ≤ n) (hb : 4040 * b ≤ n) (hc : 4 * c ≤ n) (he : 2560 * e * G ≤ P) :
    10 * (a * P + 101 * b * P + 64 * e * (n * G)) + c * (n * Q) ≤ n ^ T := by
  have hPQ : n * Q = P := by rw [← hP, ← hQ, ← pow_succ']; congr 1; omega
  have hnT : n ^ T = n * P := by rw [← hP, ← pow_succ']; congr 1; omega
  rw [hnT, hPQ]
  have e1 := Nat.mul_le_mul_right P ha
  have e2 := Nat.mul_le_mul_right P hb
  have e3 := Nat.mul_le_mul_left n he
  have e4 := Nat.mul_le_mul_right P hc
  nlinarith [e1, e2, e3, e4]

end PolySwap.KMS.L37.NumAux
end Part_NumAux

section Part_Num

open Classical

noncomputable section

namespace PolySwap.KMS.L37

open PolySwap.KMS

/-- The numerical heart of the colour-sampling bound. -/
theorem numeric (r T d : ℕ) (hr : 10 ^ 4 ≤ r) (hT : r ^ 10 ≤ T)
    (hd : 100 * (r + 1) ^ 2 * T ^ 2 ≤ d) : ∃ M : ℕ,
    10 * (T * ((d + 1) * Nat.choose (d - (M + 1)) r * Nat.choose (d + 1) (r + 1) ^ (T - 1)) +
        T * ((d + 1) * 101 * Nat.choose (d - 1) (r - 1) * Nat.choose (d + 1) (r + 1) ^ (T - 1)) +
        T * (64 * (r + 1) ^ 2) * (Nat.choose (d + 1) (r + 1) *
          (Nat.choose (d + 1) (r + 1) - Nat.choose (d + 1 - (4 * M / 5 + 20)) (r + 1)) ^ (T - 1))) +
      T * T * (Nat.choose (d + 1) (r + 1) * ((r + 1) * Nat.choose d r) *
        Nat.choose (d + 1) (r + 1) ^ (T - 2)) ≤
      Nat.choose (d + 1) (r + 1) ^ T := by
  have hr0 : 1 ≤ r := le_trans (by norm_num) hr
  have hrT : r ≤ T := le_trans (Nat.le_self_pow (by norm_num) r) hT
  have hT41 : 41 ≤ T := le_trans (le_trans (by norm_num) hr) hrT
  have hX : 100 * ((r + 1) * T) ^ 2 ≤ d := by rw [mul_pow]; linarith [hd]
  have hX1 : 41 * (r + 1) ≤ (r + 1) * T := by nlinarith
  have hdbig : 41 * 41 * 100 * (r + 1) ^ 2 ≤ d := by nlinarith
  have hdr : r ≤ d := by nlinarith
  have hA2 : 2 ≤ 40 * T * (r + 1) := by nlinarith
  have hCd : 0 < d.choose r := Nat.choose_pos hdr
  have hex : ∃ k : ℕ, d.choose r < 40 * T * (r + 1) * k.choose r := ⟨d, by nlinarith⟩
  have hk0 := Nat.find_spec hex
  have hk0d : Nat.find hex ≤ d := Nat.find_min' hex (by nlinarith)
  have hk0pos : 1 ≤ Nat.find hex := by
    by_contra h
    have h0 : Nat.find hex = 0 := by omega
    rw [h0, Nat.choose_eq_zero_of_lt (show 0 < r by omega)] at hk0
    simp at hk0
  have hs : 40 * T * (r + 1) * (Nat.find hex - 1).choose r ≤ d.choose r :=
    not_lt.mp (Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega))
  generalize Nat.find hex = k0 at hk0 hk0d hk0pos hs
  refine ⟨d - k0, ?_⟩
  rw [show d - (d - k0 + 1) = k0 - 1 by omega]
  have hdk : d ^ r < 40 * T * (r + 1) * k0 ^ r := by
    have hu := NumAux.choose_mul_pow_le k0 d r hk0d
    have hdpos : 0 < d ^ r := Nat.pow_pos (show 0 < d by omega)
    have : d ^ r * d.choose r < (40 * T * (r + 1) * k0 ^ r) * d.choose r := by
      calc d ^ r * d.choose r = d.choose r * d ^ r := by ring
        _ < (40 * T * (r + 1) * k0.choose r) * d ^ r := Nat.mul_lt_mul_of_pos_right hk0 hdpos
        _ = 40 * T * (r + 1) * (k0.choose r * d ^ r) := by ring
        _ ≤ 40 * T * (r + 1) * (k0 ^ r * d.choose r) := Nat.mul_le_mul_left _ hu
        _ = (40 * T * (r + 1) * k0 ^ r) * d.choose r := by ring
    exact Nat.lt_of_mul_lt_mul_right this
  have h1 := NumAux.term1 r T d (k0 - 1) hs
  have h2 := NumAux.term2 r T d hr0 hT41 hX
  have h3 := NumAux.term3 r T d k0 hr hT hdbig hk0pos hk0d hdk
  have h4 := NumAux.term4 r T d hX
  have := NumAux.assemble T ((d + 1).choose (r + 1))
    (T * (d + 1) * (k0 - 1).choose r) (T * (d + 1) * (d - 1).choose (r - 1))
    (T * T * (r + 1) * d.choose r) (T * (r + 1) ^ 2)
    ((d + 1).choose (r + 1) ^ (T - 1)) ((d + 1).choose (r + 1) ^ (T - 2))
    (((d + 1).choose (r + 1) - (d + 1 - (4 * (d - k0) / 5 + 20)).choose (r + 1)) ^ (T - 1))
    (by omega) rfl rfl (by linarith [h1]) (by linarith [h2]) (by linarith [h4])
    (by linarith [h3])
  calc _ = 10 * (T * (d + 1) * (k0 - 1).choose r * (d + 1).choose (r + 1) ^ (T - 1) +
          101 * (T * (d + 1) * (d - 1).choose (r - 1)) * (d + 1).choose (r + 1) ^ (T - 1) +
          64 * (T * (r + 1) ^ 2) * ((d + 1).choose (r + 1) *
            ((d + 1).choose (r + 1) -
              (d + 1 - (4 * (d - k0) / 5 + 20)).choose (r + 1)) ^ (T - 1))) +
        T * T * (r + 1) * d.choose r * ((d + 1).choose (r + 1) *
          (d + 1).choose (r + 1) ^ (T - 2)) := by ring
    _ ≤ _ := this

end PolySwap.KMS.L37
end
end Part_Num

section Part_Fib

open Classical

noncomputable section

namespace PolySwap.KMS.L37

open PolySwap.KMS

theorem disj_injective {d r T : ℕ} {f : Fin T → Finset ℕ} (hf : ∀ i, f i ∈ Cs d r)
    (hd : Disj f) : Function.Injective f := by
  intro i j hij
  by_contra hne
  have h := hd i j hne
  rw [hij, disjoint_self, Finset.bot_eq_empty] at h
  have := hf j
  rw [Cs, Finset.mem_powersetCard, h, Finset.card_empty] at this
  omega

theorem fiber_card {d r T : ℕ} (P : Finset (Finset ℕ) → Prop) (I : Finset (Finset ℕ))
    (hI : I ∈ (disjointColorSets d r T).filter P) :
    (((Tup (Cs d r) T).filter (fun f => Disj f ∧ P (Finset.univ.image f))).filter
      (fun f => Finset.univ.image f = I)).card = T.factorial := by
  simp only [Finset.mem_filter, disjointColorSets, Finset.mem_powersetCard] at hI
  obtain ⟨⟨⟨hIC, hIT⟩, hpd⟩, hP⟩ := hI
  have hcard : (Finset.univ : Finset (Fin T ↪ I)).card = T.factorial := by
    rw [Finset.card_univ, Fintype.card_embedding_eq, Fintype.card_coe, Fintype.card_fin, hIT,
      Nat.descFactorial_self]
  rw [← hcard]
  symm
  apply Finset.card_bij (fun e _ => fun k => (e k : Finset ℕ))
  · intro e _
    have him : Finset.univ.image (fun k => (e k : Finset ℕ)) = I := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 hx
        exact (e k).2
      · rw [Finset.card_image_of_injective _
          (fun a b h => e.injective (Subtype.ext h)), Finset.card_univ, Fintype.card_fin, hIT]
    simp only [Finset.mem_filter, Tup, Fintype.mem_piFinset]
    refine ⟨⟨fun k => hIC (e k).2, fun i j hij => ?_, by rw [him]; exact hP⟩, him⟩
    exact hpd (e i).2 (e j).2 (fun h => hij (e.injective (Subtype.ext h)))
  · intro a _ b _ h
    refine Function.Embedding.ext fun k => Subtype.ext ?_
    exact congrFun h k
  · intro f hf
    simp only [Finset.mem_filter, Tup, Fintype.mem_piFinset] at hf
    obtain ⟨⟨hfC, hd, _⟩, him⟩ := hf
    have hmem : ∀ k, f k ∈ I := fun k => him ▸ Finset.mem_image_of_mem f (Finset.mem_univ k)
    refine ⟨⟨fun k => ⟨f k, hmem k⟩, fun a b h => disj_injective hfC hd (congrArg Subtype.val h)⟩,
      Finset.mem_univ _, rfl⟩

/-- Each collection of `T` disjoint colour sets has exactly `T!` orderings. -/
theorem fiber (d r T : ℕ) (P : Finset (Finset ℕ) → Prop) :
    ((Tup (Cs d r) T).filter (fun f => Disj f ∧ P (Finset.univ.image f))).card =
      T.factorial * ((disjointColorSets d r T).filter P).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun f => Finset.univ.image f)
    (t := (disjointColorSets d r T).filter P), mul_comm]
  · exact Finset.sum_const_nat (fun I hI => fiber_card P I hI)
  · intro f hf
    simp only [Finset.mem_coe, Finset.mem_filter, Tup, Fintype.mem_piFinset] at hf
    obtain ⟨hfC, hd, hP⟩ := hf
    have hinj := disj_injective hfC hd
    simp only [Finset.mem_coe, Finset.mem_filter, disjointColorSets, Finset.mem_powersetCard]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hP⟩
    · intro x hx
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 hx
      exact hfC k
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    · intro x hx y hy hxy
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
      exact hd i j (fun h => hxy (h ▸ rfl))

end PolySwap.KMS.L37
end
end Part_Fib

section Part_TupC

open Classical

noncomputable section

namespace PolySwap.KMS.L37

open PolySwap.KMS

variable (C : Finset (Finset ℕ)) {T : ℕ}

theorem card_pi_one {α : Type*} (s : Fin T → Finset α) (j : Fin T) (c : ℕ)
    (h : ∀ i, i ≠ j → (s i).card = c) :
    (Fintype.piFinset s).card = (s j).card * c ^ (T - 1) := by
  rw [Fintype.card_piFinset, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
    Finset.prod_congr rfl (fun i hi => h i (Finset.ne_of_mem_erase hi)), Finset.prod_const,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]

theorem card_pi_two {α : Type*} (s : Fin T → Finset α) (i j : Fin T) (hij : i ≠ j) (c : ℕ)
    (h : ∀ k, k ≠ i → k ≠ j → (s k).card = c) :
    (Fintype.piFinset s).card = (s i).card * (s j).card * c ^ (T - 2) := by
  have hj : j ∈ Finset.univ.erase i := Finset.mem_erase.2 ⟨hij.symm, Finset.mem_univ _⟩
  rw [Fintype.card_piFinset, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ hj,
    Finset.prod_congr rfl (fun k hk => h k (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk))
      (Finset.ne_of_mem_erase hk)), Finset.prod_const,
    Finset.card_erase_of_mem hj, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin, Nat.sub_sub, mul_assoc]

theorem card_tup : (Tup C T).card = C.card ^ T := by
  rw [Tup, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem count_one (j : Fin T) (P : Finset ℕ → Prop) :
    ((Tup C T).filter (fun f => P (f j))).card = (C.filter P).card * C.card ^ (T - 1) := by
  have : (Tup C T).filter (fun f => P (f j)) =
      Fintype.piFinset (fun i => if i = j then C.filter P else C) := by
    ext f
    simp only [Tup, Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · rintro ⟨h1, h2⟩ i
      by_cases h : i = j
      · subst h; rw [if_pos rfl]; exact Finset.mem_filter.2 ⟨h1 _, h2⟩
      · rw [if_neg h]; exact h1 i
    · intro h
      refine ⟨fun i => ?_, ?_⟩
      · have := h i
        by_cases hi : i = j
        · rw [if_pos hi] at this; exact (Finset.mem_filter.1 this).1
        · rw [if_neg hi] at this; exact this
      · have := h j; rw [if_pos rfl] at this; exact (Finset.mem_filter.1 this).2
  rw [this, card_pi_one _ j C.card (fun i hi => by rw [if_neg hi]), if_pos rfl]

theorem count_pair (i j : Fin T) (hij : i ≠ j) (R : Finset ℕ → Finset ℕ → Prop) :
    ((Tup C T).filter (fun f => R (f i) (f j))).card =
      ((C ×ˢ C).filter (fun p => R p.1 p.2)).card * C.card ^ (T - 2) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun f => (f i, f j))
    (t := (C ×ˢ C).filter (fun p => R p.1 p.2))]
  · apply Finset.sum_const_nat
    rintro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    have : ((Tup C T).filter (fun f => R (f i) (f j))).filter (fun f => (f i, f j) = (a, b)) =
        Fintype.piFinset (fun k => if k = i then {a} else if k = j then {b} else C) := by
      ext f
      simp only [Tup, Finset.mem_filter, Fintype.mem_piFinset, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨h1, _⟩, ha, hb⟩ k
        by_cases hki : k = i
        · subst hki; rw [if_pos rfl, ha]; exact Finset.mem_singleton_self _
        · by_cases hkj : k = j
          · subst hkj; rw [if_neg hki, if_pos rfl, hb]; exact Finset.mem_singleton_self _
          · rw [if_neg hki, if_neg hkj]; exact h1 k
      · intro h
        have hi := h i
        have hj := h j
        rw [if_pos rfl, Finset.mem_singleton] at hi
        rw [if_neg hij.symm, if_pos rfl, Finset.mem_singleton] at hj
        refine ⟨⟨fun k => ?_, by rw [hi, hj]; exact hp.2⟩, hi, hj⟩
        by_cases hki : k = i
        · subst hki; rw [hi]; exact hp.1.1
        · by_cases hkj : k = j
          · subst hkj; rw [hj]; exact hp.1.2
          · have := h k; rwa [if_neg hki, if_neg hkj] at this
    rw [this, card_pi_two _ i j hij C.card (fun k hki hkj => by rw [if_neg hki, if_neg hkj]),
      if_pos rfl, if_neg hij.symm, if_pos rfl, Finset.card_singleton, Finset.card_singleton,
      one_mul, one_mul]
  · intro f hf
    simp only [Finset.mem_coe, Tup, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_product] at hf ⊢
    exact ⟨⟨hf.1 i, hf.1 j⟩, hf.2⟩

theorem count_star (j : Fin T) (P : Finset ℕ → Prop) (R : Finset ℕ → Finset ℕ → Prop) :
    ((Tup C T).filter (fun f => P (f j) ∧ ∀ i, i ≠ j → R (f j) (f i))).card =
      ∑ J ∈ C.filter P, (C.filter (R J)).card ^ (T - 1) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun f => f j) (t := C.filter P)]
  · apply Finset.sum_congr rfl
    intro J hJ
    simp only [Finset.mem_filter] at hJ
    have : ((Tup C T).filter (fun f => P (f j) ∧ ∀ i, i ≠ j → R (f j) (f i))).filter
        (fun f => f j = J) =
        Fintype.piFinset (fun i => if i = j then {J} else C.filter (R J)) := by
      ext f
      simp only [Tup, Finset.mem_filter, Fintype.mem_piFinset]
      constructor
      · rintro ⟨⟨h1, _, h3⟩, hfj⟩ i
        by_cases hi : i = j
        · subst hi; rw [if_pos rfl, hfj]; exact Finset.mem_singleton_self _
        · rw [if_neg hi, Finset.mem_filter, ← hfj]; exact ⟨h1 i, h3 i hi⟩
      · intro h
        have hj := h j
        rw [if_pos rfl, Finset.mem_singleton] at hj
        refine ⟨⟨fun i => ?_, by rw [hj]; exact hJ.2, fun i hi => ?_⟩, hj⟩
        · by_cases hi : i = j
          · subst hi; rw [hj]; exact hJ.1
          · have := h i; rw [if_neg hi] at this; exact (Finset.mem_filter.1 this).1
        · have := h i; rw [if_neg hi] at this; rw [hj]; exact (Finset.mem_filter.1 this).2
    rw [this, card_pi_one _ j _ (fun i hi => by rw [if_neg hi]), if_pos rfl,
      Finset.card_singleton, one_mul]
  · intro f hf
    simp only [Finset.mem_coe, Tup, Finset.mem_filter, Fintype.mem_piFinset] at hf ⊢
    exact ⟨hf.1 j, hf.2.1⟩

end PolySwap.KMS.L37
end
end Part_TupC

section Part_BinsC

open Classical

noncomputable section

namespace PolySwap.KMS.L37

open PolySwap.KMS

variable {d r : ℕ}

namespace BC

variable {J : Finset ℕ}

lemma relabel_inj {j₀ c c' : ℕ} (hj : j₀ ≤ d) (hc : c < d + 1) (hc' : c' < d + 1)
    (h : relabel d j₀ c = relabel d j₀ c') : c = c' := by
  unfold relabel at h
  have e1 : c + (d + 1) - j₀ = c + (d + 1 - j₀) := by omega
  have e2 : c' + (d + 1) - j₀ = c' + (d + 1 - j₀) := by omega
  rw [e1, e2] at h
  have : c ≡ c' [MOD d + 1] := Nat.ModEq.add_right_cancel' _ h
  rwa [Nat.ModEq, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hc'] at this

lemma base_mem (hne : J.Nonempty) : base J ∈ J := by
  simp only [base, dif_pos hne]; exact J.min'_mem hne

lemma rl_lt {K : Finset ℕ} {c : ℕ} (hc : c ∈ rl d J K) : c < d + 1 := by
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hc; exact Nat.mod_lt _ (by omega)

lemma card_rl (hne : J.Nonempty) (hJ : J ⊆ Finset.range (d + 1)) : (rl d J J).card = J.card := by
  have hb := Finset.mem_range.1 (hJ (base_mem hne))
  refine Finset.card_image_of_injOn fun x hx y hy hxy => ?_
  exact relabel_inj (by omega) (Finset.mem_range.1 (hJ hx)) (Finset.mem_range.1 (hJ hy)) hxy

lemma len_sort (hne : J.Nonempty) (hJ : J ⊆ Finset.range (d + 1)) :
    ((rl d J J).sort (· ≤ ·)).length = J.card := by
  rw [Finset.length_sort, card_rl hne hJ]

lemma jAt_eq (hne : J.Nonempty) (hJ : J ⊆ Finset.range (d + 1)) {k : ℕ} (hk : k < J.card) :
    jAt d J k = ((rl d J J).sort (· ≤ ·))[k]'(by rw [len_sort hne hJ]; exact hk) := by
  simp only [jAt, if_pos hk]
  rw [List.getD_eq_getElem]

lemma jAt_card : jAt d J J.card = d + 1 := by simp [jAt]

lemma jAt_mem (hne : J.Nonempty) (hJ : J ⊆ Finset.range (d + 1)) {k : ℕ} (hk : k < J.card) :
    jAt d J k ∈ rl d J J := by
  rw [jAt_eq hne hJ hk, ← Finset.mem_sort (· ≤ ·)]; exact List.getElem_mem _

lemma jAt_le (hne : J.Nonempty) (hJ : J ⊆ Finset.range (d + 1)) (k : ℕ) : jAt d J k ≤ d + 1 := by
  by_cases hk : k < J.card
  · exact (rl_lt (jAt_mem hne hJ hk)).le
  · simp [jAt, hk]

lemma not_between (hne : J.Nonempty) (hJ : J ⊆ Finset.range (d + 1)) {k c : ℕ} (hk : k < J.card)
    (hc : c ∈ rl d J J) (hlt : jAt d J k < c) : jAt d J (k + 1) ≤ c := by
  obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.1 ((Finset.mem_sort (· ≤ ·)).2 hc)
  have hmc : m < J.card := by rw [len_sort hne hJ] at hm; exact hm
  have hkm : k < m := by
    rw [jAt_eq hne hJ hk] at hlt
    exact (Finset.sortedLT_sort (rl d J J)).getElem_lt_getElem_iff.1 hlt
  have hk1 : k + 1 < J.card := by omega
  rw [jAt_eq hne hJ hk1]
  exact (Finset.sortedLT_sort (rl d J J)).getElem_le_getElem_iff.2 (by omega)

lemma bin_not_rl (hne : J.Nonempty) (hJ : J ⊆ Finset.range (d + 1)) {ℓ c : ℕ} (hℓ : ℓ < J.card)
    (hc : c ∈ bin d J ℓ) : c ∉ rl d J J := by
  intro hmem
  simp only [bin, binLo, binHi, Finset.mem_Icc] at hc
  have := not_between hne hJ hℓ hmem (by omega)
  omega

/-- Inverse of `relabel d j`. -/
def ur (d j y : ℕ) : ℕ := (y + j) % (d + 1)

lemma mod2 {x n : ℕ} (h : x < 2 * n) : x % n = if x < n then x else x - n := by
  split_ifs with h1
  · exact Nat.mod_eq_of_lt h1
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

lemma ur_lt (j y : ℕ) : ur d j y < d + 1 := Nat.mod_lt _ (by omega)

lemma relabel_ur {j y : ℕ} (hj : j ≤ d) (hy : y < d + 1) : relabel d j (ur d j y) = y := by
  unfold relabel ur
  rw [mod2 (x := y + j) (by omega)]
  split_ifs with h1
  · rw [mod2 (by omega)]; split_ifs <;> omega
  · rw [mod2 (by omega)]; split_ifs <;> omega

lemma ur_relabel {j c : ℕ} (hj : j ≤ d) (hc : c < d + 1) : ur d j (relabel d j c) = c := by
  unfold relabel ur
  rw [mod2 (x := c + (d + 1) - j) (by omega)]
  split_ifs with h1
  · rw [mod2 (by omega)]; split_ifs <;> omega
  · rw [mod2 (by omega)]; split_ifs <;> omega

lemma shift_inj {n c t t' : ℕ} (ht : t < n) (ht' : t' < n) (h : (c + t) % n = (c + t') % n) :
    t = t' := by
  have : t ≡ t' [MOD n] := Nat.ModEq.add_left_cancel' c h
  rwa [Nat.ModEq, Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt ht'] at this

lemma base_le (hJ : J ∈ Cs d r) : base J ≤ d := by
  have h := Finset.mem_powersetCard.1 hJ
  have hne : J.Nonempty := Finset.card_pos.1 (by omega)
  have := Finset.mem_range.1 (h.1 (base_mem hne)); omega

lemma mem_rl_iff {K : Finset ℕ} (hj : base J ≤ d) (hK : K ⊆ Finset.range (d + 1)) {y : ℕ}
    (hy : y < d + 1) : y ∈ rl d J K ↔ ur d (base J) y ∈ K := by
  constructor
  · intro h
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 h
    rwa [ur_relabel hj (Finset.mem_range.1 (hK hx))]
  · intro h
    exact Finset.mem_image.2 ⟨_, h, relabel_ur hj hy⟩

lemma ur_add {j x t : ℕ} : (ur d j x + t) % (d + 1) = ur d j (x + t) := by
  unfold ur; rw [Nat.mod_add_mod]; congr 1; ring

/-- Counting colour sets containing `A` and avoiding `W`. -/
lemma count_le {A W : Finset ℕ} (hA : A ⊆ Finset.range (d + 1)) (hW : W ⊆ Finset.range (d + 1))
    (hAW : Disjoint A W) :
    ((Cs d r).filter (fun K => A ⊆ K ∧ Disjoint K W)).card ≤
      Nat.choose (d + 1 - A.card - W.card) (r + 1 - A.card) := by
  have hc : ((Finset.range (d + 1) \ (A ∪ W)).powersetCard (r + 1 - A.card)).card =
      Nat.choose (d + 1 - A.card - W.card) (r + 1 - A.card) := by
    rw [Finset.card_powersetCard, Finset.card_sdiff_of_subset (Finset.union_subset hA hW),
      Finset.card_union_of_disjoint hAW, Finset.card_range]; congr 1; omega
  rw [← hc]
  refine Finset.card_le_card_of_injOn (fun K => K \ A) ?_ ?_
  · intro K hK
    simp only [Finset.mem_coe, Finset.mem_filter, Cs, Finset.mem_powersetCard] at hK ⊢
    refine ⟨fun x hx => ?_, ?_⟩
    · obtain ⟨hxK, hxA⟩ := Finset.mem_sdiff.1 hx
      refine Finset.mem_sdiff.2 ⟨hK.1.1 hxK, ?_⟩
      rw [Finset.mem_union, not_or]
      exact ⟨hxA, Finset.disjoint_left.1 hK.2.2 hxK⟩
    · rw [Finset.card_sdiff_of_subset hK.2.1, hK.1.2]
  · intro K hK K' hK' h
    simp only [Finset.mem_coe, Finset.mem_filter] at hK hK'
    simp only at h
    rw [← Finset.sdiff_union_of_subset hK.2.1, ← Finset.sdiff_union_of_subset hK'.2.1, h]

end BC

open BC

lemma cs_facts {J : Finset ℕ} (hJ : J ∈ Cs d r) :
    J ⊆ Finset.range (d + 1) ∧ J.card = r + 1 ∧ J.Nonempty ∧ base J ≤ d := by
  have h := Finset.mem_powersetCard.1 hJ
  exact ⟨h.1, h.2, Finset.card_pos.1 (by omega), base_le hJ⟩

lemma ur_jAt_mem {J : Finset ℕ} (hJ : J ∈ Cs d r) {k : ℕ} (hk : k ≤ J.card) :
    ur d (base J) (jAt d J k) ∈ J := by
  obtain ⟨hs, -, hne, hb⟩ := cs_facts hJ
  rcases Nat.lt_or_eq_of_le hk with hk | rfl
  · have := jAt_mem hne hs hk
    exact (mem_rl_iff hb hs (rl_lt this)).1 this
  · rw [jAt_card]; unfold ur
    rw [show d + 1 + base J = base J + (d + 1) by ring, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
    exact base_mem hne

theorem bigbin_count (M : ℕ) :
    ((Cs d r).filter (BigBin d M)).card ≤ (d + 1) * Nat.choose (d - (M + 1)) r := by
  by_cases hM : M + 1 ≤ d
  swap
  · have : (Cs d r).filter (BigBin d M) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro J hJ ⟨ℓ, hℓ, hab, hM'⟩
      obtain ⟨hs, -, hne, -⟩ := cs_facts hJ
      have := jAt_le hne hs (ℓ + 1)
      simp only [binLo, binHi] at hab hM'
      omega
    simp [this]
  let W : ℕ → Finset ℕ := fun c => (Finset.Icc 1 (M + 1)).image (fun t => (c + t) % (d + 1))
  have hWc : ∀ c, c < d + 1 → (W c).card = M + 1 := by
    intro c hc
    rw [Finset.card_image_of_injOn, Nat.card_Icc]; · omega
    intro t ht t' ht' h
    simp only [Finset.coe_Icc, Set.mem_Icc] at ht ht'
    exact shift_inj (by omega) (by omega) h
  have hsub : (Cs d r).filter (BigBin d M) ⊆ (Finset.range (d + 1)).biUnion
      (fun c => (Cs d r).filter (fun K => {c} ⊆ K ∧ Disjoint K (W c))) := by
    intro J hJf
    obtain ⟨hJ, ℓ, hℓ, hab, hM'⟩ := Finset.mem_filter.1 hJf
    obtain ⟨hs, -, hne, hb⟩ := cs_facts hJ
    have hx := ur_jAt_mem hJ hℓ.le
    refine Finset.mem_biUnion.2 ⟨_, hs hx, Finset.mem_filter.2 ⟨hJ,
      Finset.singleton_subset_iff.2 hx, Finset.disjoint_right.2 fun y hy hyJ => ?_⟩⟩
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
    rw [Finset.mem_Icc] at ht
    rw [ur_add] at hyJ
    have hle := jAt_le hne hs (ℓ + 1)
    have hbin : jAt d J ℓ + t ∈ bin d J ℓ := by
      simp only [bin, binLo, binHi, Finset.mem_Icc] at hab hM' ⊢; omega
    have hlt : jAt d J ℓ + t < d + 1 := by
      simp only [bin, binLo, binHi, Finset.mem_Icc] at hbin; omega
    exact bin_not_rl hne hs hℓ hbin ((mem_rl_iff hb hs hlt).2 hyJ)
  refine (Finset.card_le_card hsub).trans ?_
  refine (Finset.card_biUnion_le_card_mul _ _ _ fun c hc => ?_).trans
    (by rw [Finset.card_range])
  have hc := Finset.mem_range.1 hc
  have hcW : Disjoint {c} (W c) := by
    rw [Finset.disjoint_singleton_left]
    intro h
    obtain ⟨t, ht, he⟩ := Finset.mem_image.1 h
    rw [Finset.mem_Icc] at ht
    have : (c + t) % (d + 1) = (c + 0) % (d + 1) := by rw [he, add_zero, Nat.mod_eq_of_lt hc]
    have := shift_inj (by omega) (by omega) this
    omega
  have hWs : W c ⊆ Finset.range (d + 1) := by
    intro y hy
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hy
    exact Finset.mem_range.2 (Nat.mod_lt _ (by omega))
  refine (count_le (Finset.singleton_subset_iff.2 (Finset.mem_range.2 hc)) hWs hcW).trans
    (le_of_eq ?_)
  rw [hWc c hc, Finset.card_singleton]; congr 1

theorem short_count (_hr : 1 ≤ r) (hd : 103 ≤ d) :
    ((Cs d r).filter (ShortGap d)).card ≤ (d + 1) * 101 * Nat.choose (d - 1) (r - 1) := by
  have hsub : (Cs d r).filter (ShortGap d) ⊆ (Finset.range (d + 1) ×ˢ Finset.Icc 2 102).biUnion
      (fun p => (Cs d r).filter (fun K => {p.1, (p.1 + p.2) % (d + 1)} ⊆ K ∧
        Disjoint K ∅)) := by
    intro J hJf
    obtain ⟨hJ, ℓ, hℓ, hab, h100⟩ := Finset.mem_filter.1 hJf
    obtain ⟨hs, -, hne, hb⟩ := cs_facts hJ
    have hx := ur_jAt_mem hJ hℓ.le
    have hx' := ur_jAt_mem hJ (show ℓ + 1 ≤ J.card by omega)
    simp only [binLo, binHi] at hab h100
    refine Finset.mem_biUnion.2 ⟨(ur d (base J) (jAt d J ℓ), jAt d J (ℓ + 1) - jAt d J ℓ),
      Finset.mem_product.2 ⟨hs hx, Finset.mem_Icc.2 ⟨by omega, by omega⟩⟩,
      Finset.mem_filter.2 ⟨hJ, ?_, Finset.disjoint_empty_right _⟩⟩
    simp only
    rw [ur_add, show jAt d J ℓ + (jAt d J (ℓ + 1) - jAt d J ℓ) = jAt d J (ℓ + 1) by omega]
    exact Finset.insert_subset hx (Finset.singleton_subset_iff.2 hx')
  refine (Finset.card_le_card hsub).trans ?_
  have hpc : (Finset.range (d + 1) ×ˢ Finset.Icc 2 102).card = (d + 1) * 101 := by
    rw [Finset.card_product, Finset.card_range, Nat.card_Icc]
  rw [← hpc]
  refine Finset.card_biUnion_le_card_mul _ _ _ fun p hp => ?_
  obtain ⟨hc, ht⟩ := Finset.mem_product.1 hp
  rw [Finset.mem_range] at hc; rw [Finset.mem_Icc] at ht
  have hne : p.1 ≠ (p.1 + p.2) % (d + 1) := by
    intro h
    have : (p.1 + p.2) % (d + 1) = (p.1 + 0) % (d + 1) := by
      rw [← h, add_zero, Nat.mod_eq_of_lt hc]
    have := shift_inj (by omega) (by omega) this
    omega
  have hA : ({p.1, (p.1 + p.2) % (d + 1)} : Finset ℕ) ⊆ Finset.range (d + 1) :=
    Finset.insert_subset (Finset.mem_range.2 hc)
      (Finset.singleton_subset_iff.2 (Finset.mem_range.2 (Nat.mod_lt _ (by omega))))
  refine (count_le hA (Finset.empty_subset _) (Finset.disjoint_empty_right _)).trans
    (le_of_eq ?_)
  rw [Finset.card_pair hne, Finset.card_empty]; congr 1

theorem pair_count :
    (((Cs d r) ×ˢ (Cs d r)).filter (fun p => ¬ Disjoint p.1 p.2)).card ≤
      (Cs d r).card * ((r + 1) * Nat.choose d r) := by
  rw [Finset.card_filter, Finset.sum_product]
  refine (Finset.sum_le_sum fun K hK => ?_).trans (le_of_eq (by rw [Finset.sum_const, smul_eq_mul]))
  rw [← Finset.card_filter]
  obtain ⟨hs, hcard, -, -⟩ := cs_facts hK
  have hsub : (Cs d r).filter (fun K' => ¬ Disjoint K K') ⊆
      K.biUnion (fun x => (Cs d r).filter (fun K' => {x} ⊆ K' ∧ Disjoint K' ∅)) := by
    intro K' hK'
    obtain ⟨hK'C, hnd⟩ := Finset.mem_filter.1 hK'
    obtain ⟨x, hxK, hxK'⟩ := Finset.not_disjoint_iff.1 hnd
    exact Finset.mem_biUnion.2 ⟨x, hxK, Finset.mem_filter.2 ⟨hK'C,
      Finset.singleton_subset_iff.2 hxK', Finset.disjoint_empty_right _⟩⟩
  refine (Finset.card_le_card hsub).trans ?_
  rw [← hcard]
  refine Finset.card_biUnion_le_card_mul _ _ _ fun x hx => ?_
  refine (count_le (Finset.singleton_subset_iff.2 (hs hx)) (Finset.empty_subset _)
    (Finset.disjoint_empty_right _)).trans (le_of_eq ?_)
  rw [Finset.card_singleton, Finset.card_empty]; congr 1


lemma rl_image_ur {J K : Finset ℕ} (hb : base J ≤ d) (hK : K ⊆ Finset.range (d + 1)) :
    rl d J (K.image (ur d (base J))) = K := by
  unfold rl; rw [Finset.image_image]
  have : Set.EqOn (relabel d (base J) ∘ ur d (base J)) id K :=
    fun y hy => relabel_ur hb (Finset.mem_range.1 (hK hy))
  rw [Finset.image_congr this, Finset.image_id]

lemma window_card {a b s M : ℕ} (h : a ≤ b → b - a + 1 ≤ M) (hs : s < 4) :
    (window a b s).card ≤ 2 * (M / 5) + 10 := by
  unfold window; rw [Nat.card_Icc]
  interval_cases s <;> omega

theorem good_count (M : ℕ) {J : Finset ℕ} (hJ : J ∈ Cs d r) (hJM : ¬ BigBin d M J)
    {q : ℕ × ℕ × ℕ × ℕ × ℕ} (hq : q ∈ Qs r) :
    Nat.choose (d + 1 - (4 * M / 5 + 20)) (r + 1) ≤ ((Cs d r).filter (Good d q J)).card := by
  obtain ⟨hs, hcard, hne, hb⟩ := cs_facts hJ
  have hB : ∀ ℓ < J.card, binLo d J ℓ ≤ binHi d J ℓ → binHi d J ℓ - binLo d J ℓ + 1 ≤ M :=
    fun ℓ hℓ hab => by by_contra h; exact hJM ⟨ℓ, hℓ, hab, by omega⟩
  obtain ⟨ty, ℓ, ℓ', s, s'⟩ := q
  simp only [Qs, Finset.mem_product, Finset.mem_range] at hq
  obtain ⟨hty, hℓ, hℓ', hs4, hs4'⟩ := hq
  rw [← hcard] at hℓ hℓ'
  obtain ⟨S, hS, hSG⟩ : ∃ S : Finset ℕ, S.card ≤ 4 * M / 5 + 20 ∧
      ∀ K, Disjoint (rl d J K) S → Good d (ty, ℓ, ℓ', s, s') J K := by
    have h1 := hB ℓ hℓ
    have h2 := hB ℓ' hℓ'
    interval_cases ty
    · refine ⟨Finset.Ioc (binLo d J ℓ + (binHi d J ℓ - binLo d J ℓ) / 5) (binHi d J ℓ),
        by rw [Nat.card_Ioc]; omega, fun K hK => ?_⟩
      simp only [Good]
      intro hab c hc hcb
      have := Finset.disjoint_left.1 hK hc
      simp only [bin, Finset.mem_Icc, Finset.mem_Ioc] at hcb this
      omega
    · refine ⟨Finset.Ico (binLo d J ℓ) (binHi d J ℓ - (binHi d J ℓ - binLo d J ℓ) / 5),
        by rw [Nat.card_Ico]; omega, fun K hK => ?_⟩
      simp only [Good]
      intro hab c hc hcb
      have := Finset.disjoint_left.1 hK hc
      simp only [bin, Finset.mem_Icc, Finset.mem_Ico] at hcb this
      omega
    · refine ⟨Finset.Ico (binLo d J ℓ) (binLo d J ℓ + 2 * ((binHi d J ℓ - binLo d J ℓ + 4) / 5)) ∪
        Finset.Ioc (binLo d J ℓ + 3 * ((binHi d J ℓ - binLo d J ℓ) / 5)) (binHi d J ℓ),
        (Finset.card_union_le _ _).trans (by rw [Nat.card_Ico, Nat.card_Ioc]; omega),
        fun K hK => ?_⟩
      simp only [Good]
      intro hab c hc hcb
      have := Finset.disjoint_left.1 hK hc
      simp only [bin, Finset.mem_Icc, Finset.mem_Ico, Finset.mem_Ioc, Finset.mem_union,
        not_or] at hcb this
      omega
    · refine ⟨window (binLo d J ℓ) (binHi d J ℓ) s ∪ window (binLo d J ℓ') (binHi d J ℓ') s',
        (Finset.card_union_le _ _).trans ?_, fun K hK => ?_⟩
      · have := window_card h1 hs4
        have := window_card h2 hs4'
        omega
      · simp only [Good]
        intro _ _
        exact Finset.disjoint_union_right.1 hK
  calc Nat.choose (d + 1 - (4 * M / 5 + 20)) (r + 1)
      ≤ ((Finset.range (d + 1) \ S).powersetCard (r + 1)).card := by
        rw [Finset.card_powersetCard]; apply Nat.choose_le_choose
        have := Finset.le_card_sdiff S (Finset.range (d + 1))
        rw [Finset.card_range] at this; omega
    _ ≤ _ := by
      refine Finset.card_le_card_of_injOn (fun K => K.image (ur d (base J))) ?_ ?_
      · intro K hK
        simp only [Finset.mem_coe, Finset.mem_powersetCard] at hK
        have hKr : K ⊆ Finset.range (d + 1) := fun x hx => (Finset.mem_sdiff.1 (hK.1 hx)).1
        simp only [Finset.mem_coe, Finset.mem_filter, Cs, Finset.mem_powersetCard]
        refine ⟨⟨fun y hy => ?_, ?_⟩, hSG _ ?_⟩
        · obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hy; exact Finset.mem_range.2 (ur_lt _ _)
        · rw [Finset.card_image_of_injOn, hK.2]
          intro x hx y hy hxy
          have := congrArg (relabel d (base J)) hxy
          rwa [relabel_ur hb (Finset.mem_range.1 (hKr hx)),
            relabel_ur hb (Finset.mem_range.1 (hKr hy))] at this
        · rw [rl_image_ur hb hKr, Finset.disjoint_left]
          exact fun x hx => (Finset.mem_sdiff.1 (hK.1 hx)).2
      · intro K hK K' hK' h
        simp only [Finset.mem_coe, Finset.mem_powersetCard] at hK hK'
        have := congrArg (rl d J) h
        simp only at this
        rwa [rl_image_ur hb fun x hx => (Finset.mem_sdiff.1 (hK.1 hx)).1,
          rl_image_ur hb fun x hx => (Finset.mem_sdiff.1 (hK'.1 hx)).1] at this

theorem nice_of {I : Finset (Finset ℕ)} (hIC : ∀ J ∈ I, J ∈ Cs d r)
    (h : ∀ J ∈ I, ¬ ShortGap d J ∧ ∀ q ∈ Qs r, ∃ K ∈ I.erase J, Good d q J K) :
    IsNice d I := by
  intro J hJ
  obtain ⟨hsg, hq⟩ := h J hJ
  obtain ⟨-, hcard, -, -⟩ := cs_facts (hIC J hJ)
  have hmem : ∀ ty ℓ ℓ' s s' : ℕ, ty < 4 → ℓ < J.card → ℓ' < J.card → s ≤ 3 → s' ≤ 3 →
      (ty, ℓ, ℓ', s, s') ∈ Qs r := by
    intro ty ℓ ℓ' s s' h1 h2 h3 h4 h5
    simp only [Qs, Finset.mem_product, Finset.mem_range]; omega
  refine ⟨fun ℓ hℓ hab => ?_, fun ℓ hℓ hab => ?_, fun ℓ hℓ hab => ?_, fun ℓ hℓ hab => ?_,
    fun ℓ hℓ ℓ' hℓ' hab hab' s hs s' hs' => ?_⟩
  · by_contra hc; exact hsg ⟨ℓ, hℓ, hab, by omega⟩
  · obtain ⟨K, hK, hG⟩ := hq _ (hmem 0 ℓ 0 0 0 (by omega) hℓ (by omega) (by omega) (by omega))
    simp only [Good] at hG
    exact ⟨K, hK, hG hab⟩
  · obtain ⟨K, hK, hG⟩ := hq _ (hmem 1 ℓ 0 0 0 (by omega) hℓ (by omega) (by omega) (by omega))
    simp only [Good] at hG
    exact ⟨K, hK, hG hab⟩
  · obtain ⟨K, hK, hG⟩ := hq _ (hmem 2 ℓ 0 0 0 (by omega) hℓ (by omega) (by omega) (by omega))
    simp only [Good] at hG
    exact ⟨K, hK, hG hab⟩
  · obtain ⟨K, hK, hG⟩ := hq _ (hmem 3 ℓ ℓ' s s' (by omega) hℓ hℓ' hs hs')
    simp only [Good] at hG
    exact ⟨K, hK, hG hab hab'⟩

end PolySwap.KMS.L37
end
end Part_BinsC

section Part_Main

open Classical

noncomputable section

namespace PolySwap.KMS.L37

open PolySwap.KMS

theorem card_Qs (r : ℕ) : (Qs r).card = 64 * (r + 1) ^ 2 := by
  simp [Qs, Finset.card_product]; ring

theorem cs_nonempty {d r : ℕ} {J : Finset ℕ} (hJ : J ∈ Cs d r) : J.Nonempty := by
  rw [← Finset.card_pos, (Finset.mem_powersetCard.1 hJ).2]; omega

/-- A disjoint tuple avoiding all bad events spans a nice collection. -/
theorem nice_image {d r T M : ℕ} {f : Fin T → Finset ℕ} (hf : f ∈ Tup (Cs d r) T) (hD : Disj f)
    (h1 : ∀ j, ¬ BigBin d M (f j)) (h2 : ∀ j, ¬ ShortGap d (f j))
    (h3 : ∀ j, ∀ q ∈ Qs r, ¬ (∀ i, i ≠ j → ¬ Good d q (f j) (f i))) :
    IsNice d (Finset.univ.image f) := by
  have hmem : ∀ j, f j ∈ Cs d r := fun j => Fintype.mem_piFinset.1 hf j
  refine nice_of (r := r) (fun J hJ => ?_) (fun J hJ => ?_)
  · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hJ; exact hmem j
  · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hJ
    refine ⟨h2 j, fun q hq => ?_⟩
    have := h3 j q hq
    push_neg at this
    obtain ⟨i, hij, hg⟩ := this
    refine ⟨f i, Finset.mem_erase.2 ⟨fun he => ?_, Finset.mem_image.2 ⟨i, by simp, rfl⟩⟩, hg⟩
    have hd := hD i j hij
    rw [he] at hd
    obtain ⟨x, hx⟩ := cs_nonempty (hmem j)
    exact Finset.disjoint_left.1 hd hx hx

theorem main_count (r T d : ℕ) (hr : 10 ^ 4 ≤ r) (hT : r ^ 10 ≤ T)
    (hd : 100 * (r + 1) ^ 2 * T ^ 2 ≤ d) :
    10 * ((Tup (Cs d r) T).filter (fun f => Disj f ∧ ¬ IsNice d (Finset.univ.image f))).card ≤
      ((Tup (Cs d r) T).filter (fun f => Disj f ∧ True)).card := by
  obtain ⟨M, hM⟩ := numeric r T d hr hT hd
  set C := Cs d r with hC
  set n := C.card with hn
  have hnC : n = Nat.choose (d + 1) (r + 1) := by simp [hn, hC, Cs]
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hT1 : 1 ≤ T := le_trans (Nat.one_le_pow _ _ (by omega)) hT
  have hd103 : 103 ≤ d := by
    have : 100 * 1 * 1 ≤ 100 * (r + 1) ^ 2 * T ^ 2 := by
      gcongr <;> exact Nat.one_le_pow _ _ (by omega)
    have h2 : 100 * (2 ^ 2) * 1 ≤ 100 * (r + 1) ^ 2 * T ^ 2 := by
      gcongr
      · omega
      · exact Nat.one_le_pow _ _ (by omega)
    omega
  set g := Nat.choose (d + 1 - (4 * M / 5 + 20)) (r + 1) with hg
  -- the bad events
  set E1 := (Finset.univ : Finset (Fin T)).biUnion
    (fun j => (Tup C T).filter (fun f => BigBin d M (f j))) with hE1
  set E2 := (Finset.univ : Finset (Fin T)).biUnion
    (fun j => (Tup C T).filter (fun f => ShortGap d (f j))) with hE2
  set E3 := (Finset.univ : Finset (Fin T)).biUnion (fun j => (Qs r).biUnion fun q =>
    (Tup C T).filter (fun f => ¬ BigBin d M (f j) ∧ ∀ i, i ≠ j → ¬ Good d q (f j) (f i)))
    with hE3
  have hsub : (Tup C T).filter (fun f => Disj f ∧ ¬ IsNice d (Finset.univ.image f)) ⊆
      E1 ∪ E2 ∪ E3 := by
    intro f hf
    obtain ⟨hfT, hD, hN⟩ := Finset.mem_filter.1 hf
    by_contra hc
    simp only [Finset.mem_union, hE1, hE2, hE3, Finset.mem_biUnion, Finset.mem_univ,
      true_and, Finset.mem_filter, not_or, not_exists, not_and] at hc
    obtain ⟨⟨c1, c2⟩, c3⟩ := hc
    refine hN (nice_image hfT hD (fun j h => c1 j hfT h) (fun j h => c2 j hfT h) ?_)
    intro j q hq hall
    exact c3 j q hq hfT (fun h => (c1 j hfT h).elim) hall
  have hE1c : E1.card ≤ T * ((d + 1) * Nat.choose (d - (M + 1)) r * n ^ (T - 1)) := by
    refine (Finset.card_biUnion_le).trans ?_
    refine (Finset.sum_le_sum (g := fun _ => _) fun j _ => ?_).trans
      (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul])
    rw [count_one]
    exact Nat.mul_le_mul_right _ (bigbin_count M)
  have hE2c : E2.card ≤ T * ((d + 1) * 101 * Nat.choose (d - 1) (r - 1) * n ^ (T - 1)) := by
    refine (Finset.card_biUnion_le).trans ?_
    refine (Finset.sum_le_sum (g := fun _ => _) fun j _ => ?_).trans
      (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul])
    rw [count_one]
    exact Nat.mul_le_mul_right _ (short_count hr1 hd103)
  have hgn : ∀ J ∈ C.filter (fun J => ¬ BigBin d M J), ∀ q ∈ Qs r,
      (C.filter (fun K => ¬ Good d q J K)).card ≤ n - g := by
    intro J hJ q hq
    obtain ⟨hJC, hJM⟩ := Finset.mem_filter.1 hJ
    have h1 := good_count M hJC hJM hq
    rw [← hC, ← hg] at h1
    have h2 := Finset.card_filter_add_card_filter_not (s := C) (Good d q J)
    omega
  have hE3c : E3.card ≤ T * (64 * (r + 1) ^ 2) * (n * (n - g) ^ (T - 1)) := by
    refine (Finset.card_biUnion_le).trans ?_
    refine (Finset.sum_le_sum (g := fun _ => _) fun j _ => ?_).trans
      (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_assoc])
    refine (Finset.card_biUnion_le).trans ?_
    refine (Finset.sum_le_sum (g := fun _ => _) fun q hq => ?_).trans
      (by rw [Finset.sum_const, card_Qs, smul_eq_mul])
    have ecs := count_star C j (fun J => ¬ BigBin d M J) (fun J K => ¬ Good d q J K)
    calc ((Tup C T).filter (fun f => ¬ BigBin d M (f j) ∧
            ∀ i, i ≠ j → ¬ Good d q (f j) (f i))).card
        = ∑ J ∈ C.filter (fun J => ¬ BigBin d M J),
            (C.filter (fun K => ¬ Good d q J K)).card ^ (T - 1) := by convert ecs
      _ ≤ ∑ J ∈ C.filter (fun J => ¬ BigBin d M J), (n - g) ^ (T - 1) :=
          Finset.sum_le_sum fun J hJ => Nat.pow_le_pow_left (hgn J hJ q hq) _
      _ ≤ ∑ J ∈ C, (n - g) ^ (T - 1) := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = n * (n - g) ^ (T - 1) := by rw [Finset.sum_const, smul_eq_mul]
  -- non-disjoint tuples
  set ND := ((Finset.univ : Finset (Fin T)) ×ˢ (Finset.univ : Finset (Fin T))).biUnion
    (fun p => if p.1 = p.2 then ∅ else
      (Tup C T).filter (fun f => ¬ Disjoint (f p.1) (f p.2))) with hND
  have hNDc : ND.card ≤ T * T * (n * ((r + 1) * Nat.choose d r) * n ^ (T - 2)) := by
    refine (Finset.card_biUnion_le).trans ?_
    have : ∀ p ∈ (Finset.univ : Finset (Fin T)) ×ˢ (Finset.univ : Finset (Fin T)),
        (if p.1 = p.2 then (∅ : Finset (Fin T → Finset ℕ)) else
          (Tup C T).filter (fun f => ¬ Disjoint (f p.1) (f p.2))).card ≤
          n * ((r + 1) * Nat.choose d r) * n ^ (T - 2) := by
      intro p _
      split_ifs with h
      · simp
      · have e := count_pair C p.1 p.2 h (fun x y => ¬ Disjoint x y)
        calc ((Tup C T).filter (fun f => ¬ Disjoint (f p.1) (f p.2))).card
            = ((C ×ˢ C).filter (fun p => ¬ Disjoint p.1 p.2)).card * C.card ^ (T - 2) := by
              convert e
          _ ≤ _ := Nat.mul_le_mul_right _ pair_count
    refine (Finset.sum_le_sum this).trans ?_
    rw [Finset.sum_const, smul_eq_mul, Finset.card_product, Finset.card_univ, Fintype.card_fin]
  have hsplit : (Tup C T).card ≤ ((Tup C T).filter (fun f => Disj f ∧ True)).card + ND.card := by
    have : Tup C T ⊆ (Tup C T).filter (fun f => Disj f ∧ True) ∪ ND := by
      intro f hf
      by_cases hD : Disj f
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hf, hD, trivial⟩)
      · refine Finset.mem_union_right _ ?_
        simp only [Disj, not_forall] at hD
        obtain ⟨i, j, hij, hd⟩ := hD
        exact Finset.mem_biUnion.2 ⟨(i, j), by simp, by
          simp only [if_neg hij]; exact Finset.mem_filter.2 ⟨hf, hd⟩⟩
    exact (Finset.card_le_card this).trans (Finset.card_union_le _ _)
  have hcard := card_tup C (T := T)
  rw [← hn] at hcard
  have hbad := (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  rw [← hnC] at hM
  omega

end PolySwap.KMS.L37

open PolySwap.KMS PolySwap.KMS.L37 in
theorem solution (r T d : ℕ) (hr : 10 ^ 4 ≤ r) (hT : r ^ 10 ≤ T)
    (hd : 100 * (r + 1) ^ 2 * T ^ 2 ≤ d) :
    (0.9 : ℝ) * (disjointColorSets d r T).card ≤ niceCount d r T := by
  have h := main_count r T d hr hT hd
  have e1 := fiber d r T (fun I => ¬ IsNice d I)
  have e2 := fiber d r T (fun _ => True)
  rw [Finset.filter_true] at e2
  have h : 10 * (T.factorial * ((disjointColorSets d r T).filter (fun I => ¬ IsNice d I)).card) ≤
      T.factorial * (disjointColorSets d r T).card := by
    convert h using 2
    · convert e1.symm
    · convert e2.symm
  have hpos : 0 < T.factorial := Nat.factorial_pos T
  have h' : 10 * ((disjointColorSets d r T).filter (fun I => ¬ IsNice d I)).card ≤
      (disjointColorSets d r T).card := by
    have : T.factorial * (10 * ((disjointColorSets d r T).filter (fun I => ¬ IsNice d I)).card) ≤
        T.factorial * (disjointColorSets d r T).card := by linarith
    exact Nat.le_of_mul_le_mul_left this hpos
  have hsum := Finset.card_filter_add_card_filter_not (s := disjointColorSets d r T)
    (IsNice d)
  unfold niceCount
  have h1 : ((((disjointColorSets d r T).filter (IsNice d)).card : ℕ) : ℝ) +
      (((disjointColorSets d r T).filter (fun I => ¬ IsNice d I)).card : ℝ) =
      ((disjointColorSets d r T).card : ℝ) := by exact_mod_cast hsum
  have h2 : (10 : ℝ) * (((disjointColorSets d r T).filter (fun I => ¬ IsNice d I)).card : ℝ) ≤
      ((disjointColorSets d r T).card : ℝ) := by exact_mod_cast h'
  linarith
end
end Part_Main

