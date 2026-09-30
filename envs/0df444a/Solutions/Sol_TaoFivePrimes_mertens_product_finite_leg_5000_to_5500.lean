-- Prove2me | solution 1 for TaoFivePrimes.mertens_product_finite_leg_5000_to_5500
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T00:29:09.32726+00:00
-- url     : https://prove2.me/submissions/93c2bf4d-30c3-485e-8cdc-ffa5eac41170

import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib

/-! Mertens product bound on [5000, 5500] by a kernel-checked certificate.
* `isPrB` is trial division by `d < 75`, equivalent to primality below `75 ^ 2`.
* `AB n = (∏ p, ∏ (p - 1))` over primes `p ≤ n`; the real product equals `AB.1 / AB.2`.
* `γ > harmonic 2047 - log 2048` (Mathlib), `harmonic 2047 ≥ N0 / 10 ^ 20` (floor-sum), so
  `exp γ ≥ 1780151 / 10 ^ 6` via `E ^ 2000 ≤ 2 ^ 1664`.
* for each `m ∈ [5000, 5500]`, `2 ^ b ≤ m ^ 2000` gives `log m ≥ b log 2 / 2000`, and one integer
  inequality per `m` closes the goal (with `√x ≤ 74.17`). -/

set_option autoImplicit false

namespace MertensLeg5000

open Real

def isPrB (n : ℕ) : Bool :=
  Nat.ble 2 n && (List.range 75).all (fun d => Nat.blt d 2 || Nat.blt n (d * d) || !(n % d == 0))

theorem isPrB_iff (n : ℕ) (hn : n < 5625) : isPrB n = true ↔ n.Prime := by
  constructor
  · intro h
    simp only [isPrB, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
      Nat.blt_eq] at h
    obtain ⟨h2, hall⟩ := h
    have h2' : 2 ≤ n := Nat.le_of_ble_eq_true h2
    by_contra hnp
    have hp1 : n ≠ 1 := by omega
    have hmp := Nat.minFac_prime hp1
    have hsq := Nat.minFac_sq_le_self (by omega) hnp
    have h2m := hmp.two_le
    have hsq' : n.minFac * n.minFac ≤ n := by rw [← pow_two]; exact hsq
    have hm75 : n.minFac < 75 := by
      by_contra hc
      have h75 : 75 ≤ n.minFac := by omega
      have h3 := le_trans (Nat.mul_le_mul h75 h75) hsq'
      omega
    have hmod : n % n.minFac = 0 := Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd n)
    have := hall n.minFac hm75
    simp [hmod] at this
    omega
  · intro hp
    simp only [isPrB, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
      Nat.blt_eq, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
    refine ⟨Nat.ble_eq_true_of_le hp.two_le, ?_⟩
    intro d _
    by_cases hd2 : d < 2
    · left; left; exact hd2
    by_cases hdd : n < d * d
    · left; right; exact hdd
    right
    intro hmod
    have hdvd : d ∣ n := Nat.dvd_of_mod_eq_zero hmod
    rcases hp.eq_one_or_self_of_dvd d hdvd with h | h
    · omega
    · subst h
      have : d * 2 ≤ d * d := Nat.mul_le_mul_left d (by omega)
      omega

def upd (n : ℕ) (s : ℕ × ℕ) : ℕ × ℕ := if isPrB n then (s.1 * n, s.2 * (n - 1)) else s

def AB : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | n + 1 => upd (n + 1) (AB n)

theorem AB_spec (n : ℕ) (hn : n < 5625) :
    0 < (AB n).2 ∧
      ∏ p ∈ Nat.primesLE n, (p : ℝ) / ((p : ℝ) - 1) = ((AB n).1 : ℝ) / ((AB n).2 : ℝ) := by
  induction n with
  | zero => simp [AB]
  | succ n ih =>
    obtain ⟨hpos, heq⟩ := ih (by omega)
    have hset : Nat.primesLE (n + 1) =
        if (n + 1).Prime then insert (n + 1) (Nat.primesLE n) else Nat.primesLE n := by
      rw [Nat.primesLE_eq_filter_range, Nat.primesLE_eq_filter_range, Finset.range_add_one,
        Finset.filter_insert]
    have hnot : n + 1 ∉ Nat.primesLE n := by
      intro h
      have := Nat.le_of_mem_primesLE h
      omega
    have hiff := isPrB_iff (n + 1) hn
    by_cases hp : (n + 1).Prime
    · have hb : isPrB (n + 1) = true := hiff.2 hp
      have hAB : AB (n + 1) = ((AB n).1 * (n + 1), (AB n).2 * n) := by
        simp [AB, upd, hb]
      rw [hset, if_pos hp, Finset.prod_insert hnot, heq, hAB]
      have hn0 : (0 : ℝ) < n := by
        have := hp.two_le
        exact_mod_cast (show 0 < n by omega)
      have hB0 : (0 : ℝ) < (AB n).2 := by exact_mod_cast hpos
      refine ⟨Nat.mul_pos hpos (by have := hp.two_le; omega), ?_⟩
      push_cast
      rw [div_mul_div_comm]
      congr 1 <;> ring
    · have hb : isPrB (n + 1) = false := by
        cases h : isPrB (n + 1)
        · rfl
        · exact absurd (hiff.1 h) hp
      have hAB : AB (n + 1) = AB n := by simp [AB, upd, hb]
      rw [hset, if_neg hp, hAB]
      exact ⟨hpos, heq⟩

/-! ### Euler–Mascheroni lower bound -/

def hsum : ℕ → ℕ
  | 0 => 0
  | n + 1 => hsum n + 100000000000000000000 / (n + 1)

theorem hsum_le (n : ℕ) : ((hsum n : ℕ) : ℚ) / 100000000000000000000 ≤ harmonic n := by
  induction n with
  | zero => simp [hsum]
  | succ n ih =>
    rw [harmonic_succ]
    have h1 : ((100000000000000000000 / (n + 1) : ℕ) : ℚ) ≤
        (100000000000000000000 : ℚ) / ((n + 1 : ℕ) : ℚ) := Nat.cast_div_le
    have h2 : ((hsum (n + 1) : ℕ) : ℚ) =
        (hsum n : ℚ) + ((100000000000000000000 / (n + 1) : ℕ) : ℚ) := by
      simp only [hsum]; push_cast; ring
    rw [h2, add_div]
    have h3 : ((100000000000000000000 / (n + 1) : ℕ) : ℚ) / 100000000000000000000 ≤
        ((n + 1 : ℕ) : ℚ)⁻¹ := by
      rw [div_le_iff₀ (by norm_num)]
      calc ((100000000000000000000 / (n + 1) : ℕ) : ℚ)
          ≤ (100000000000000000000 : ℚ) / ((n + 1 : ℕ) : ℚ) := h1
        _ = ((n + 1 : ℕ) : ℚ)⁻¹ * 100000000000000000000 := by rw [div_eq_mul_inv, mul_comm]
    linarith

theorem hsum_val : 820159049056771680303 ≤ hsum 2047 := by decide +kernel

theorem gamma_gt : (820159049056771680303 : ℝ) / 100000000000000000000 - 11 * log 2 <
    eulerMascheroniConstant := by
  have h := eulerMascheroniSeq_lt_eulerMascheroniConstant 2047
  have hH : ((820159049056771680303 : ℚ) / 100000000000000000000) ≤ harmonic 2047 := by
    have := hsum_le 2047
    have hv : (820159049056771680303 : ℕ) ≤ hsum 2047 := hsum_val
    have hv' : ((820159049056771680303 : ℕ) : ℚ) ≤ (hsum 2047 : ℚ) := by exact_mod_cast hv
    have : (820159049056771680303 : ℚ) / 100000000000000000000 ≤
        (hsum 2047 : ℚ) / 100000000000000000000 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact_mod_cast hv
    linarith
  have hHR' := (Rat.cast_le (K := ℝ)).2 hH
  rw [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofNat] at hHR'
  have hlog : log ((2047 : ℕ) + 1 : ℝ) = 11 * log 2 := by
    rw [show ((2047 : ℕ) + 1 : ℝ) = 2 ^ 11 by norm_num, Real.log_pow]
    norm_num
  unfold eulerMascheroniSeq at h
  rw [hlog] at h
  generalize ((harmonic 2047 : ℚ) : ℝ) = H at h hHR'
  linarith

theorem E_cert : 1780151 ^ 2000 ≤ 2 ^ 1664 * 1000000 ^ 2000 := by decide +kernel

theorem log_le_of_cert (a c J b : ℕ) (hc : 0 < c) (ha : 0 < a) (h : a ^ J ≤ 2 ^ b * c ^ J) :
    (J : ℝ) * log ((a : ℝ) / c) ≤ b * log 2 := by
  have hcR : ((a : ℝ) / c) ^ J ≤ (2 : ℝ) ^ b := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    exact_mod_cast h
  have := Real.log_le_log (by positivity) hcR
  rw [Real.log_pow, Real.log_pow] at this
  exact this

theorem exp_gamma_ge : (1780151 : ℝ) / 1000000 ≤ exp eulerMascheroniConstant := by
  have hg := gamma_gt
  have hl2 := Real.log_two_lt_d9
  norm_num at hl2
  have hlogE := log_le_of_cert 1780151 1000000 2000 1664 (by norm_num) (by norm_num) E_cert
  simp only [Nat.cast_ofNat] at hlogE
  have hlog2pos : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
  have hle : log ((1780151 : ℝ) / 1000000) ≤ eulerMascheroniConstant := by
    linarith
  calc (1780151 : ℝ) / 1000000 = exp (log ((1780151 : ℝ) / 1000000)) :=
        (Real.exp_log (by norm_num)).symm
    _ ≤ exp eulerMascheroniConstant := Real.exp_le_exp.2 hle

/-! ### the walk -/

def cond (m : ℕ) (s : ℕ × ℕ) (b : ℕ) : Bool :=
  Nat.ble (2 ^ b) (m ^ 2000) &&
    Nat.blt (s.1 * (1000000 * 2000 * 10000000000 * 7417))
      (s.2 * (1780151 * (b * 6931471803 * 7417 + 200 * 2000 * 10000000000)))

def walk : ℕ → ℕ × ℕ → List ℕ → Bool
  | _, _, [] => true
  | m, s, b :: l => cond m s b && walk (m + 1) (upd (m + 1) s) l

theorem walk_sound : ∀ (l : List ℕ) (m : ℕ), walk m (AB m) l = true →
    ∀ k, m ≤ k → k < m + l.length → ∃ b, cond k (AB k) b = true := by
  intro l
  induction l with
  | nil => intro m _ k h1 h2; simp at h2; omega
  | cons b l ih =>
    intro m h k h1 h2
    simp only [walk, Bool.and_eq_true] at h
    by_cases hk : k = m
    · subst hk; exact ⟨b, h.1⟩
    · have h' : walk (m + 1) (AB (m + 1)) l = true := by
        rw [show AB (m + 1) = upd (m + 1) (AB m) from rfl]; exact h.2
      exact ih (m + 1) h' k (by omega) (by simp at h2; omega)

def BS : List ℕ := [
  24575, 24576, 24576, 24577, 24577, 24578, 24578, 24579, 24580, 24580, 24581, 24581, 24582, 24582, 24583, 24584, 24584, 24585, 24585, 24586,
  24586, 24587, 24588, 24588, 24589, 24589, 24590, 24590, 24591, 24592, 24592, 24593, 24593, 24594, 24594, 24595, 24596, 24596, 24597, 24597,
  24598, 24598, 24599, 24600, 24600, 24601, 24601, 24602, 24602, 24603, 24604, 24604, 24605, 24605, 24606, 24606, 24607, 24608, 24608, 24609,
  24609, 24610, 24610, 24611, 24612, 24612, 24613, 24613, 24614, 24614, 24615, 24616, 24616, 24617, 24617, 24618, 24618, 24619, 24620, 24620,
  24621, 24621, 24622, 24622, 24623, 24624, 24624, 24625, 24625, 24626, 24626, 24627, 24628, 24628, 24629, 24629, 24630, 24630, 24631, 24631,
  24632, 24633, 24633, 24634, 24634, 24635, 24635, 24636, 24637, 24637, 24638, 24638, 24639, 24639, 24640, 24641, 24641, 24642, 24642, 24643,
  24643, 24644, 24644, 24645, 24646, 24646, 24647, 24647, 24648, 24648, 24649, 24650, 24650, 24651, 24651, 24652, 24652, 24653, 24653, 24654,
  24655, 24655, 24656, 24656, 24657, 24657, 24658, 24659, 24659, 24660, 24660, 24661, 24661, 24662, 24662, 24663, 24664, 24664, 24665, 24665,
  24666, 24666, 24667, 24667, 24668, 24669, 24669, 24670, 24670, 24671, 24671, 24672, 24673, 24673, 24674, 24674, 24675, 24675, 24676, 24676,
  24677, 24678, 24678, 24679, 24679, 24680, 24680, 24681, 24681, 24682, 24683, 24683, 24684, 24684, 24685, 24685, 24686, 24686, 24687, 24688,
  24688, 24689, 24689, 24690, 24690, 24691, 24691, 24692, 24693, 24693, 24694, 24694, 24695, 24695, 24696, 24696, 24697, 24698, 24698, 24699,
  24699, 24700, 24700, 24701, 24701, 24702, 24702, 24703, 24704, 24704, 24705, 24705, 24706, 24706, 24707, 24707, 24708, 24709, 24709, 24710,
  24710, 24711, 24711, 24712, 24712, 24713, 24714, 24714, 24715, 24715, 24716, 24716, 24717, 24717, 24718, 24718, 24719, 24720, 24720, 24721,
  24721, 24722, 24722, 24723, 24723, 24724, 24724, 24725, 24726, 24726, 24727, 24727, 24728, 24728, 24729, 24729, 24730, 24731, 24731, 24732,
  24732, 24733, 24733, 24734, 24734, 24735, 24735, 24736, 24737, 24737, 24738, 24738, 24739, 24739, 24740, 24740, 24741, 24741, 24742, 24743,
  24743, 24744, 24744, 24745, 24745, 24746, 24746, 24747, 24747, 24748, 24748, 24749, 24750, 24750, 24751, 24751, 24752, 24752, 24753, 24753,
  24754, 24754, 24755, 24756, 24756, 24757, 24757, 24758, 24758, 24759, 24759, 24760, 24760, 24761, 24762, 24762, 24763, 24763, 24764, 24764,
  24765, 24765, 24766, 24766, 24767, 24767, 24768, 24769, 24769, 24770, 24770, 24771, 24771, 24772, 24772, 24773, 24773, 24774, 24774, 24775,
  24776, 24776, 24777, 24777, 24778, 24778, 24779, 24779, 24780, 24780, 24781, 24781, 24782, 24783, 24783, 24784, 24784, 24785, 24785, 24786,
  24786, 24787, 24787, 24788, 24788, 24789, 24789, 24790, 24791, 24791, 24792, 24792, 24793, 24793, 24794, 24794, 24795, 24795, 24796, 24796,
  24797, 24798, 24798, 24799, 24799, 24800, 24800, 24801, 24801, 24802, 24802, 24803, 24803, 24804, 24804, 24805, 24806, 24806, 24807, 24807,
  24808, 24808, 24809, 24809, 24810, 24810, 24811, 24811, 24812, 24812, 24813, 24814, 24814, 24815, 24815, 24816, 24816, 24817, 24817, 24818,
  24818, 24819, 24819, 24820, 24820, 24821, 24821, 24822, 24823, 24823, 24824, 24824, 24825, 24825, 24826, 24826, 24827, 24827, 24828, 24828,
  24829, 24829, 24830, 24830, 24831, 24832, 24832, 24833, 24833, 24834, 24834, 24835, 24835, 24836, 24836, 24837, 24837, 24838, 24838, 24839,
  24839, 24840, 24840, 24841, 24842, 24842, 24843, 24843, 24844, 24844, 24845, 24845, 24846, 24846, 24847, 24847, 24848, 24848, 24849, 24849,
  24850]

theorem walk_ok : walk 5000 (AB 5000) BS = true := by decide +kernel

theorem BS_len : BS.length = 501 := by decide +kernel

theorem cond_real (x : ℝ) (A B b m : ℕ) (hB : 0 < B) (hm : 1 ≤ m) (hmx : (m : ℝ) ≤ x)
    (hx : x ≤ 5500) (hb : 2 ^ b ≤ m ^ 2000)
    (hc : A * (1000000 * 2000 * 10000000000 * 7417) <
      B * (1780151 * (b * 6931471803 * 7417 + 200 * 2000 * 10000000000))) :
    (A : ℝ) / B < exp eulerMascheroniConstant * log x +
      2 * exp eulerMascheroniConstant / Real.sqrt x := by
  have hE := exp_gamma_ge
  have hl2 := Real.log_two_gt_d9
  norm_num at hl2
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hx0 : 0 < x := by linarith
  -- log bound
  have hbR : (2 : ℝ) ^ b ≤ (m : ℝ) ^ 2000 := by exact_mod_cast hb
  have hlogm : (b : ℝ) * log 2 ≤ 2000 * log m := by
    have := Real.log_le_log (by positivity) hbR
    rw [Real.log_pow, Real.log_pow] at this
    exact_mod_cast this
  have hlogx : log (m : ℝ) ≤ log x := Real.log_le_log (by linarith) hmx
  have hb0 : (0 : ℝ) ≤ b := by positivity
  have hL : (b : ℝ) * 6931471803 / (2000 * 10000000000) ≤ log x := by
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  -- sqrt bound
  have hsq : Real.sqrt x ≤ 7417 / 100 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
    linarith
  have hsq0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hS : (200 : ℝ) / 7417 ≤ 2 / Real.sqrt x := by
    rw [div_le_div_iff₀ (by norm_num) hsq0]
    linarith
  set E := exp eulerMascheroniConstant with hEdef
  have hE0 : (0 : ℝ) < 1780151 / 1000000 := by norm_num
  set T : ℝ := (b : ℝ) * 6931471803 / (2000 * 10000000000) + 200 / 7417 with hT
  have hT0 : 0 ≤ T := by positivity
  have hRHS : E * T ≤ E * log x + 2 * E / Real.sqrt x := by
    have : 2 * E / Real.sqrt x = E * (2 / Real.sqrt x) := by ring
    rw [this, hT]
    have hEp : 0 ≤ E := (exp_pos _).le
    nlinarith
  have hET : (1780151 : ℝ) / 1000000 * T ≤ E * T := mul_le_mul_of_nonneg_right hE hT0
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hcR : (A : ℝ) * (1000000 * 2000 * 10000000000 * 7417) <
      B * (1780151 * (b * 6931471803 * 7417 + 200 * 2000 * 10000000000)) := by
    exact_mod_cast hc
  have hmain : (A : ℝ) / B < (1780151 : ℝ) / 1000000 * T := by
    rw [div_lt_iff₀ hBR, hT]
    nlinarith
  linarith

end MertensLeg5000

theorem solution (x : ℝ) (hx : 5000 ≤ x) (hx' : x ≤ 5500) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  set m := ⌊x⌋₊ with hm
  have hm1 : 5000 ≤ m := Nat.le_floor (by exact_mod_cast hx)
  have hm2 : m ≤ 5500 := by
    have := (Nat.floor_lt hx0).2 (show x < ((5501 : ℕ) : ℝ) by push_cast; linarith)
    omega
  have hmx : (m : ℝ) ≤ x := Nat.floor_le hx0
  obtain ⟨hpos, heq⟩ := MertensLeg5000.AB_spec m (by omega)
  obtain ⟨b, hb⟩ := MertensLeg5000.walk_sound MertensLeg5000.BS 5000 MertensLeg5000.walk_ok m hm1
    (by rw [MertensLeg5000.BS_len]; omega)
  simp only [MertensLeg5000.cond, Bool.and_eq_true] at hb
  rw [heq]
  exact MertensLeg5000.cond_real x (MertensLeg5000.AB m).1 (MertensLeg5000.AB m).2 b m hpos (by omega) hmx hx'
    (Nat.le_of_ble_eq_true hb.1) (Nat.le_of_ble_eq_true hb.2)
