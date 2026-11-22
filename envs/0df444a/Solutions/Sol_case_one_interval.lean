-- Prove2me | solution 1 for case_one_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:46:23.525815+00:00
-- url     : https://prove2.me/submissions/0b3c113a-699f-4198-a2f1-59e83c93b122

import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
import Definitions.Def_Polychromatic_FourThree_Combi_CaseOne
import Theorems.Thm_Finpartition_card_of_mem_equipartitionToIco_parts_aux
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
import Theorems.Thm_polychromNumber_pair
import Theorems.Thm_polychromNumber_singleton
import Theorems.Thm_polychromNumber_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ
attribute [local simp] polychromNumber_pair
attribute [local simp] polychromNumber_singleton
attribute [local simp] polychromNumber_univ


section
open Finset Pointwise
section Case1_SingleCycle
variable (m : ℕ)
private lemma phase_ne_of_gap {s j₀ jg : ℕ} (hs3 : 3 ∣ s) (hj₀ : j₀ < s)
    (hgap : (jg + s - j₀) % s = 1 ∨ (jg + s - j₀) % s = 2) :
    j₀ % 3 ≠ jg % 3 := by grind [Nat.div_add_mod, Nat.mul_add_mod]
open Finpartition in
private lemma idx_in_interval' (s m : ℕ) (hs : 0 < s) (hs_le : s ≤ m) (p : ℕ) (hp : p < m) :
    let q := m / s
    let r := m % s
    let bd := r * (q + 1)
    let j := if p < bd then p / (q + 1)
      else r + (p - bd) / q
    j < s ∧
    equiEndpoint m s j ≤ p ∧
    p < equiEndpoint m s (j + 1) := by
  simp only
  set q := m / s
  set r := m % s
  set bd := r * (q + 1)
  have hq_pos : 0 < q := Nat.div_pos hs_le hs
  have hr_lt : r < s := Nat.mod_lt m hs
  have hm_eq : m = s * q + r := (Nat.div_add_mod m s).symm
  have hbd_le_m : bd + (s - r) * q = m := by grind [Nat.sub_add_cancel (Nat.le_of_lt hr_lt)]
  split
  · rename_i hlt
    set j := p / (q + 1)
    have hj_lt_r : j < r := by rw [Nat.div_lt_iff_lt_mul (by omega)]; exact hlt
    have hmod : p % (q + 1) < q + 1 := Nat.mod_lt p (by omega)
    refine ⟨by omega, ?_, ?_⟩ <;> grind [equiEndpoint, Nat.div_add_mod p (q + 1)]
  · rename_i hge
    push Not at hge
    set d := (p - bd) / q
    have hmod : (p - bd) % q < q := Nat.mod_lt _ hq_pos
    have hd_lt : d < s - r := by rw [Nat.div_lt_iff_lt_mul hq_pos]; omega
    set j := r + d
    refine ⟨by omega, ?_, ?_⟩ <;> grind [equiEndpoint, Nat.div_add_mod (p - bd) q]
private lemma equiEndpoint_diff_ge (m s j : ℕ) : m / s ≤ Finpartition.equiEndpoint m s (j + 1) -
        Finpartition.equiEndpoint m s j := by grind [Finpartition.equiEndpoint]
open Finpartition in
private lemma gap_exceeds_ilen (m s g : ℕ) (hs : 0 < s) (h_lb : (m + s - 1) / s < g) (j : ℕ) :
    equiEndpoint m s (j + 1) - equiEndpoint m s j < g := by
  rw [Finpartition.card_of_mem_equipartitionToIco_parts_aux]
  set q := m / s
  set r := m % s
  by_cases hr : j < r
  · rw [if_pos hr]
    have : (q + 1) * s ≤ m + s - 1 := by grind [Nat.div_add_mod m s]
    have := (Nat.le_div_iff_mul_le hs).mpr this
    omega
  · rw [if_neg hr]
    have : q * s ≤ m + s - 1 := le_trans (Nat.div_mul_le_self m s) (by omega)
    have := (Nat.le_div_iff_mul_le hs).mpr this
    omega
open Finpartition in
private lemma idx_range_from_endpoints' (m s : ℕ) (a b p : ℕ)
    (ha_le : equiEndpoint m s a ≤ p)
    (hp_lt : p < equiEndpoint m s b)
    (j : ℕ)
    (hj_lo : equiEndpoint m s j ≤ p)
    (hj_hi : p < equiEndpoint m s (j + 1)) :
    a ≤ j ∧ j < b := by
  refine ⟨?_, ?_⟩ <;> by_contra! h
  · have : equiEndpoint m s (j + 1) ≤ equiEndpoint m s a := equiEndpoint_monotone (by omega)
    omega
  · have : equiEndpoint m s b ≤ equiEndpoint m s j := equiEndpoint_monotone (by omega)
    omega
private lemma gap_bound_interval (s g m : ℕ) (hs : 0 < s) (hs3 : 3 ≤ s) (hs_le : s ≤ m)
    (h_lb : (m + s - 1) / s < g) (h_ub : g < 2 * (m / s))
    (v : ℕ) (hv_lt : v < m) :
    let bd := (m % s) * (m / s + 1)
    let idx (p : ℕ) : ℕ :=
      if p < bd then p / (m / s + 1)
      else m % s + (p - bd) / (m / s)
    let j₀ := idx v
    let jg := idx ((v + g) % m)
    (jg + s - j₀) % s = 1 ∨ (jg + s - j₀) % s = 2 := by
  simp only
  set q := m / s
  set r := m % s
  set bd := r * (q + 1)
  set idx := fun p ↦
    if p < bd then p / (q + 1) else r + (p - bd) / q
  set j₀ := idx v
  set jg := idx ((v + g) % m)
  obtain ⟨hj₀_lt, hv_lo, hv_hi⟩ : j₀ < s ∧ Finpartition.equiEndpoint m s j₀ ≤ v ∧
      v < Finpartition.equiEndpoint m s (j₀ + 1) := idx_in_interval' s m hs hs_le v hv_lt
  have hvg_lt : (v + g) % m < m := Nat.mod_lt _ (by omega)
  obtain ⟨hjg_lt, hvg_lo, hvg_hi⟩ : jg < s ∧ Finpartition.equiEndpoint m s jg ≤ (v + g) % m ∧
      (v + g) % m < Finpartition.equiEndpoint m s (jg + 1) :=
    idx_in_interval' s m hs hs_le ((v + g) % m) hvg_lt
  have hpast : Finpartition.equiEndpoint m s (j₀ + 1) ≤ v + g := by
    have := gap_exceeds_ilen m s g hs h_lb j₀; omega
  have hwithin : v + g < Finpartition.equiEndpoint m s (j₀ + 3) := by
    have := equiEndpoint_diff_ge m s (j₀ + 1)
    have := equiEndpoint_diff_ge m s (j₀ + 2)
    grind [Finpartition.equiEndpoint_monotone]
  have hg_lt_m : g < m := by have hqs : q * s ≤ m := Nat.div_mul_le_self m s; nlinarith
  by_cases hvg_wrap : v + g < m
  · have hvg_eq : (v + g) % m = v + g := Nat.mod_eq_of_lt hvg_wrap
    rw [hvg_eq] at hvg_lo hvg_hi
    have hrange : j₀ + 1 ≤ jg ∧ jg < j₀ + 3 := by
      by_cases hj3 : j₀ + 3 ≤ s
      · exact idx_range_from_endpoints' m s (j₀+1) (j₀+3) (v+g) hpast hwithin jg hvg_lo hvg_hi
      · have hvg_lt_ep : v + g < Finpartition.equiEndpoint m s s := by
          grind [Finpartition.equiEndpoint_hi (by omega : s ≠ 0) (n := m) (k := s)]
        have := idx_range_from_endpoints' m s (j₀+1) s (v+g) hpast hvg_lt_ep jg hvg_lo hvg_hi
        omega
    have : jg + s - j₀ = s + 1 ∨ jg + s - j₀ = s + 2 := by omega
    rcases this with h | h <;> [left; right] <;>
      rw [h, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  · push Not at hvg_wrap
    have hvg_eq : (v + g) % m = v + g - m := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hvg_eq] at hvg_lo hvg_hi
    have hj0_ge : j₀ ≥ s - 2 := by
      by_contra! h
      have : Finpartition.equiEndpoint m s (j₀ + 3) ≤
          Finpartition.equiEndpoint m s s := Finpartition.equiEndpoint_monotone (by omega)
      have := Finpartition.equiEndpoint_hi (by omega : s ≠ 0) (n := m) (k := s)
      omega
    have hr_lt : r < s := Nat.mod_lt m hs
    have hep_j3 : Finpartition.equiEndpoint m s (j₀ + 3) = q * (j₀ + 3) + r := by
      grind [Finpartition.equiEndpoint]
    have hm_eq : m = q * s + r := by grind [Nat.div_add_mod m s]
    have hm_le_ep : m ≤ Finpartition.equiEndpoint m s (j₀ + 3) := by grind
    have hep_diff : Finpartition.equiEndpoint m s (j₀ + 3) - m =
        q * (j₀ + 3 - s) := by rw [hep_j3, hm_eq]; grind [Nat.mul_add]
    have hvgm_ub : v + g - m < Finpartition.equiEndpoint m s (j₀ + 3 - s) := by
      calc v + g - m < q * (j₀ + 3 - s) := by grind
        _ ≤ Finpartition.equiEndpoint m s (j₀ + 3 - s) := by
          change q * _ ≤ q * _ + min r _
          omega
    have hrange := idx_range_from_endpoints' m s
      0 (j₀ + 3 - s) (v + g - m)
      (by unfold Finpartition.equiEndpoint; simp)
      hvgm_ub jg hvg_lo hvg_hi
    have : jg + s - j₀ = 1 ∨ jg + s - j₀ = 2 := by omega
    rcases this with h | h <;> [left; right] <;> rw [h, Nat.mod_eq_of_lt (by omega)]
private lemma eqp_idx_m (q r s : ℕ) (hq : 0 < q) (hr : r < s) : eqp_idx q r (s * q + r) = s := by
  have hge : ¬(s * q + r < r * (q + 1)) := by nlinarith
  simp only [eqp_idx, if_neg hge]
  have hsub : s * q + r - r * (q + 1) = (s - r) * q := by grind
  rw [hsub, Nat.mul_div_cancel _ hq]
  omega
private lemma div_step (a b : ℕ) :
    (a + 1) / b = a / b ∨ (a + 1) / b = a / b + 1 := by grind [Nat.succ_div]
private lemma eqp_idx_step (q r p : ℕ) (hq : 0 < q) : eqp_idx q r (p + 1) = eqp_idx q r p ∨
    eqp_idx q r (p + 1) = eqp_idx q r p + 1 := by
  unfold eqp_idx
  split_ifs with h1 h2
  · exact div_step p (q + 1)
  · omega
  · right
    have hpeq : p + 1 = r * (q + 1) := by omega
    have h_succ : (p + 1) / (q + 1) = r := by rw [hpeq]; exact Nat.mul_div_cancel r (by omega)
    have hne : p / (q + 1) ≠ r := fun heq =>
      absurd (heq ▸ Nat.div_mul_le_self p (q + 1)) (by omega)
    have := div_step p (q + 1)
    rw [hpeq, Nat.sub_self, Nat.zero_div]
    omega
  · have hsub : p + 1 - r * (q + 1) = (p - r * (q + 1)) + 1 := by omega
    rw [hsub]
    have := div_step (p - r * (q + 1)) q
    omega
private lemma mod_step (a b : ℕ) (h : (a + 1) / b = a / b) :
    (a + 1) % b = a % b + 1 := by grind [Nat.div_add_mod a b, Nat.div_add_mod (a + 1) b]
private lemma mod_zero_step (a b : ℕ) (h : (a + 1) / b = a / b + 1) : (a + 1) % b = 0 := by
  grind [Nat.succ_div, Nat.dvd_iff_mod_eq_zero]
private lemma eqp_off_succ_same (q r p : ℕ) (hq : 0 < q) (h : eqp_idx q r (p + 1) = eqp_idx q r p) :
    eqp_off q r (p + 1) = eqp_off q r p + 1 := by
  unfold eqp_off
  by_cases h1 : p + 1 < r * (q + 1) <;> by_cases h2 : p < r * (q + 1)
  · rw [if_pos h1, if_pos h2]
    exact mod_step p (q + 1) (by simpa [eqp_idx, h1, h2] using h)
  · omega
  · exfalso
    simp only [eqp_idx, if_neg h1, if_pos h2] at h
    exact absurd (h ▸ Nat.le_add_right r _) (by rwa [Nat.not_le, Nat.div_lt_iff_lt_mul (by omega)])
  · rw [if_neg h1, if_neg h2]
    have hsub : p + 1 - r * (q + 1) = (p - r * (q + 1)) + 1 := by omega
    rw [hsub]
    exact mod_step (p - r * (q + 1)) q
      (by simp only [eqp_idx, if_neg h1, if_neg h2] at h; rw [hsub] at h; omega)
private lemma eqp_off_succ_new (q r p : ℕ) (h : eqp_idx q r (p + 1) ≠ eqp_idx q r p) :
    eqp_off q r (p + 1) = 0 := by
  unfold eqp_off
  by_cases h1 : p + 1 < r * (q + 1) <;> by_cases h2 : p < r * (q + 1)
  · rw [if_pos h1]
    exact mod_zero_step p (q + 1)
      (by simp only [eqp_idx, if_pos h1, if_pos h2] at h; have := div_step p (q + 1); omega)
  · omega
  · rw [if_neg h1]
    have : p + 1 = r * (q + 1) := by omega
    simp [this]
  · rw [if_neg h1]
    have hsub : p + 1 - r * (q + 1) = (p - r * (q + 1)) + 1 := by omega
    rw [hsub]
    refine mod_zero_step (p - r * (q + 1)) q ?_
    simp only [eqp_idx, if_neg h1, if_neg h2] at h
    rw [hsub] at h
    have := div_step (p - r * (q + 1)) q
    omega
private lemma gap_mod_cases_gen (s j₀ jg d : ℕ) (hj₀ : j₀ < s) (hjg : jg < s)
    (hmod : (jg + s - j₀) % s = d) :
    jg + s - j₀ = d ∨ jg + s - j₀ = s + d := by
  have hd_hi : jg + s - j₀ < 2 * s := by omega
  have hdiv := Nat.div_add_mod (jg + s - j₀) s
  rw [hmod] at hdiv
  have hq_lt : (jg + s - j₀) / s < 2 := by rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
  rcases Nat.eq_zero_or_pos ((jg + s - j₀) / s) with h | h <;> grind
open Finpartition in
private lemma straddle1_gap2 (s g m : ℕ) (hs : 0 < s) (hs3 : 3 ≤ s) (hs_le : s ≤ m)
    (h_lb : (m + s - 1) / s < g) (h_ub : g < 2 * (m / s))
    (v j₀ jg : ℕ) (hv : v < m)
    (hj₀_lt : j₀ < s) (hjg_lt : jg < s)
    (hv_hi : v < equiEndpoint m s (j₀ + 1))
    (hvg_lo : equiEndpoint m s jg ≤ (v + g) % m)
    (hvg_hi : (v + g) % m < equiEndpoint m s (jg + 1))
    (hstrad : equiEndpoint m s (j₀ + 1) ≤ v + 1)
    (hgap : (jg + s - j₀) % s = 1 ∨ (jg + s - j₀) % s = 2) :
    (jg + s - j₀) % s = 2 := by
  by_contra hne
  have hgap1 : (jg + s - j₀) % s = 1 := by tauto
  have hv_eq : v + 1 = equiEndpoint m s (j₀ + 1) := by omega
  have hjg_cases := gap_mod_cases_gen s j₀ jg 1 hj₀_lt hjg_lt hgap1
  have hq_pos : 0 < m / s := by grind
  have hg_lt_m : g < m := by have := Nat.div_mul_le_self m s; nlinarith
  have hep_s : equiEndpoint m s s = m := equiEndpoint_hi (by omega)
  by_cases hj₀_lt_s : j₀ + 1 < s
  · have hjg_val : jg = j₀ + 1 := by omega
    have hilen := gap_exceeds_ilen m s g hs h_lb (j₀ + 1)
    have hmono : equiEndpoint m s (j₀ + 1) ≤
        equiEndpoint m s (j₀ + 1 + 1) := equiEndpoint_monotone (by omega)
    by_cases hwrap : v + g < m
    · rw [hjg_val, Nat.mod_eq_of_lt hwrap] at hvg_hi; omega
    · push Not at hwrap
      rw [hjg_val, Nat.mod_eq_sub_mod hwrap, Nat.mod_eq_of_lt (by omega)] at hvg_lo; omega
  · have hj₀_eq : j₀ = s - 1 := by omega
    have hjg_val : jg = 0 := by omega
    rw [hj₀_eq, Nat.sub_add_cancel (by omega), hep_s] at hv_eq
    have hv_val : v = m - 1 := by omega
    have hg_pos : 0 < g := by grind
    have hvg_mod : (v + g) % m = g - 1 := by
      have : m - 1 + g = m + (g - 1) := by omega
      rw [hv_val, this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    rw [hjg_val, hvg_mod] at hvg_hi
    simp only [Nat.zero_add] at hvg_hi
    have hep1 : equiEndpoint m s 1 ≤ (m + s - 1) / s := by
      rw [equiEndpoint]
      simp only [Nat.mul_one]
      by_cases hr : m % s = 0
      · simp only [hr, zero_min]; exact Nat.div_le_div_right (by omega)
      · have : min (m % s) 1 = 1 := by omega
        rw [this]
        apply (Nat.le_div_iff_mul_le hs).mpr
        grind [Nat.div_add_mod m s]
    omega
open Finpartition in
private lemma straddle2_gap1 (s g m : ℕ) (hs3 : 3 ≤ s) (hs_le : s ≤ m)
    (h_lb : (m + s - 1) / s < g) (h_ub : g < 2 * (m / s))
    (v j₀ jg : ℕ) (hv : v < m)
    (hj₀_lt : j₀ < s) (hjg_lt : jg < s)
    (hv_lo : equiEndpoint m s j₀ ≤ v)
    (hv_hi : v < equiEndpoint m s (j₀ + 1))
    (hvg_hi : (v + g) % m < equiEndpoint m s (jg + 1))
    (hstrad : equiEndpoint m s (jg + 1) ≤ (v + g) % m + 1)
    (hgap : (jg + s - j₀) % s = 1 ∨ (jg + s - j₀) % s = 2) :
    (jg + s - j₀) % s = 1 := by
  by_contra hne
  have hgap2 : (jg + s - j₀) % s = 2 := by tauto
  have hvg_eq : (v + g) % m + 1 = equiEndpoint m s (jg + 1) := by omega
  have hq_pos : 0 < m / s := by grind
  have hg_lt_m : g < m := by have := Nat.div_mul_le_self m s; nlinarith
  have hjg_cases := gap_mod_cases_gen s j₀ jg 2 hj₀_lt hjg_lt hgap2
  have hep0 : equiEndpoint m s 0 = 0 := by simp [equiEndpoint]
  have hep_s : equiEndpoint m s s = m := equiEndpoint_hi (by omega)
  by_cases hj_nowrap : j₀ + 2 < s
  · have hjg_val : jg = j₀ + 2 := by omega
    rw [hjg_val] at hvg_eq
    set e1 := equiEndpoint m s (j₀ + 1) with he1
    set e2 := equiEndpoint m s (j₀ + 1 + 1) with he2
    set e3 := equiEndpoint m s (j₀ + 1 + 1 + 1) with he3
    have hd1 := equiEndpoint_diff_ge m s (j₀ + 1)
    have hd2 := equiEndpoint_diff_ge m s (j₀ + 1 + 1)
    by_cases hwrap : v + g < m
    · have : (v + g) % m = v + g := Nat.mod_eq_of_lt hwrap
      omega
    · push Not at hwrap
      have : (v + g) % m = v + g - m := by
        rw [Nat.mod_eq_sub_mod hwrap, Nat.mod_eq_of_lt (by omega)]
      omega
  · have hjg_val : jg = j₀ + 2 - s := by omega
    have hpos_wrap : m ≤ v + g := by
      by_contra! h
      have : (v + g) % m = v + g := Nat.mod_eq_of_lt h
      have : equiEndpoint m s (jg + 1) ≤ equiEndpoint m s j₀ := equiEndpoint_monotone (by omega)
      grind
    have hvg_mod : (v + g) % m = v + g - m := by
      rw [Nat.mod_eq_sub_mod hpos_wrap, Nat.mod_eq_of_lt (by omega)]
    by_cases hj₀_eq : j₀ = s - 2
    · have hjg0 : jg = 0 := by omega
      rw [hjg0] at hvg_eq
      simp only [Nat.zero_add] at hvg_eq
      rw [hj₀_eq] at hv_hi
      have : s - 2 + 1 = s - 1 := by omega
      rw [this] at hv_hi
      have hd1 := equiEndpoint_diff_ge m s (s - 1)
      rw [Nat.sub_add_cancel (by omega), hep_s] at hd1
      have hep_s1_le : equiEndpoint m s (s - 1) ≤ m :=
        le_trans (equiEndpoint_monotone (by omega)) hep_s.le
      have hd2 := equiEndpoint_diff_ge m s 0
      grind
    · have hj₀_eq2 : j₀ = s - 1 := by omega
      have hjg1 : jg = 1 := by omega
      rw [hjg1] at hvg_eq
      rw [hj₀_eq2, Nat.sub_add_cancel (by omega), hep_s] at hv_hi
      have hd1 := equiEndpoint_diff_ge m s 0
      rw [hep0, Nat.zero_add] at hd1
      have hd2 := equiEndpoint_diff_ge m s 1
      grind
private lemma eqp_idx_succ_lt_m (q r s p : ℕ) (hq_pos : 0 < q) (hr_lt : r < s)
    (hm_eq : m = s * q + r)
    (hp : p < m) :
    p + 1 < m ∨ eqp_idx q r (p + 1) = s := by grind [eqp_idx_m]
private lemma non_straddle_witness (q r p : ℕ) (hq_pos : 0 < q)
    (hp : p < m) (hp1 : p + 1 < m)
    (hsame : eqp_idx q r (p + 1) = eqp_idx q r p)
    (j : ℕ) (hj : j = eqp_idx q r p)
    (t : ℕ) (hpair : t = j % 3 ∨ t = (j + 1) % 3) :
    ∃ d ∈ ({0, 1} : Finset ℕ),
      (eqp_idx q r ((p + d) % m) + eqp_off q r ((p + d) % m) % 2) % 3 = t := by
  have hoff := eqp_off_succ_same q r p hq_pos hsame
  have : (j + (eqp_off q r p) % 2) % 3 = t ∨ (j + ((eqp_off q r p) + 1) % 2) % 3 = t := by omega
  rcases this with h | h
  · exact ⟨0, by simp, by simp only [Nat.add_zero, Nat.mod_eq_of_lt hp, ← hj]; exact h⟩
  · exact ⟨1, by simp, by rw [Nat.mod_eq_of_lt hp1, hsame, ← hj, hoff]; exact h⟩
private lemma straddle_boundary_color (q r s p : ℕ) (hq_pos : 0 < q) (hr_lt : r < s) (hs3 : 3 ∣ s)
    (hm_eq : m = s * q + r)
    (hp : p < m)
    (hstep : eqp_idx q r (p + 1) = eqp_idx q r p + 1)
    (j : ℕ) (hj : j = eqp_idx q r p) :
    (eqp_idx q r ((p + 1) % m) + eqp_off q r ((p + 1) % m) % 2) % 3 = (j + 1) % 3 := by
  by_cases h : p + 1 < m
  · rw [Nat.mod_eq_of_lt h]
    have hoff := eqp_off_succ_new q r p (by omega)
    rw [hstep, ← hj, hoff]
  · have hpm : p + 1 = m := by omega
    rw [hpm, Nat.mod_self, show eqp_idx q r 0 = 0 by simp [eqp_idx],
      show eqp_off q r 0 = 0 by simp [eqp_off]]
    rw [hpm] at hstep
    have hm_idx : eqp_idx q r m = s := by rw [hm_eq]; exact eqp_idx_m q r s hq_pos hr_lt
    grind
private lemma vg_mod_shift (v g d : ℕ) : (v + (g + d)) % m = ((v + g) % m + d) % m := by
  grind [Nat.add_mod (v + g) d m, Nat.add_mod ((v + g) % m) d m,
    Nat.mod_mod_of_dvd _ (dvd_refl m)]
private lemma lift_coloring_witness {m g : ℕ} [NeZero m] [Fact (1 < m)]
    (hg_lt : g + 1 < m) {c : ℕ → ℕ} (hc_lt : ∀ p, c p < 3)
    (hc_period : ∀ p, c (p % m) = c p)
    {n : ZMod m} {k : Fin 3}
    (h : ∃ a ∈ ({0, 1, g, g + 1} : Finset ℕ), c (n.val + a) = k.val) :
    ∃ s ∈ ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)),
      (⟨c (n + s).val, hc_lt _⟩ : Fin 3) = k := by
  obtain ⟨a, ha, hca⟩ := h
  have ha_lt : a < m := by grind
  exact ⟨(a : ZMod m),
    by simp only [Finset.mem_insert, Finset.mem_singleton] at ha ⊢
       rcases ha with rfl | rfl | rfl | rfl <;> simp,
    by ext
       change c (n + (a : ZMod m)).val = k.val
       have : (n + (a : ZMod m)).val = (n.val + a) % m := by
         rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt ha_lt]
       rw [this, hc_period, hca]⟩
section Case1c
end Case1c
section Case1d
end Case1d
end Case1_SingleCycle
end

set_option autoImplicit true
open Finset Pointwise
variable (m : ℕ)
theorem _root_.solution (s g : ℕ) (hs : 0 < s) (hs3 : 3 ∣ s)
    (h_lb : (m + s - 1) / s < g) (h_ub : g < 2 * (m / s)) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  set q := m / s
  set r := m % s
  have hm_eq : m = s * q + r := (Nat.div_add_mod m s).symm
  have hr_lt : r < s := Nat.mod_lt m hs
  have hq_pos : 0 < q := by nlinarith [Nat.div_mul_le_self m s, h_lb, h_ub]
  have hs_le : s ≤ m := by nlinarith [Nat.div_mul_le_self m s]
  have hg1_lt_m : g + 1 < m := by nlinarith [Nat.div_mul_le_self m s, Nat.le_of_dvd hs hs3]
  haveI : NeZero m := ⟨by omega⟩
  haveI : Fact (1 < m) := ⟨by omega⟩
  set bd := r * (q + 1)
  let idx (p : ℕ) : ℕ :=
    if p < bd then p / (q + 1) else r + (p - bd) / q
  let off (p : ℕ) : ℕ :=
    if p < bd then p % (q + 1) else (p - bd) % q
  let c (p : ℕ) : ℕ := (idx (p % m) + off (p % m) % 2) % 3
  have hc_lt3 : ∀ p, c p < 3 := fun p => Nat.mod_lt _ (by omega)
  have hc_period : ∀ p, c (p % m) = c p := by
    intro p; simp only [c]; rw [Nat.mod_mod_of_dvd p (dvd_refl m)]
  refine ⟨fun x => ⟨c x.val, hc_lt3 _⟩, fun n k =>
    lift_coloring_witness hg1_lt_m hc_lt3 hc_period ?_⟩
  set v := n.val
  have hv_lt : v < m := ZMod.val_lt n
  -- Gap bound: idx((v+g)%m) differs from idx(v) by 1 or 2 mod s
  set j₀ := idx v with hj₀_def
  set jg := idx ((v + g) % m) with hjg_def
  have hs3_le : 3 ≤ s := Nat.le_of_dvd hs hs3
  have hgap := gap_bound_interval s g m hs hs3_le hs_le h_lb h_ub v hv_lt
  -- idx ranges
  have hidx_lt : ∀ p, p < m → idx p < s := fun p hp => (idx_in_interval' s m hs hs_le p hp).1
  have hj₀_lt : j₀ < s := hidx_lt v hv_lt
  have hjg_lt : jg < s := hidx_lt ((v + g) % m) (Nat.mod_lt _ (by omega))
  -- Phase difference: j₀ % 3 ≠ jg % 3
  have hphase : j₀ % 3 ≠ jg % 3 := phase_ne_of_gap hs3 hj₀_lt hgap
  -- Interval bounds
  obtain ⟨-, hv_lo, hv_hi⟩ := idx_in_interval' s m hs hs_le v hv_lt
  obtain ⟨-, hvg_lo, hvg_hi⟩ :=
    idx_in_interval' s m hs hs_le ((v + g) % m) (Nat.mod_lt _ (by omega))
  -- Bridge: eqp_idx step → equiEndpoint straddle condition
  open Finpartition in
  have endpoint_bridge : ∀ p : ℕ, p < m → eqp_idx q r p < s →
      eqp_idx q r (p + 1) = eqp_idx q r p + 1 →
      equiEndpoint m s (eqp_idx q r p + 1) ≤ p + 1 := by
    intro p hp hidx_p hstep_p
    by_cases hp1 : p + 1 < m
    · have hiv_p := idx_in_interval' s m hs hs_le (p + 1) hp1
      simp only at hiv_p
      change eqp_idx q r (p + 1) < s ∧ equiEndpoint m s (eqp_idx q r (p + 1)) ≤ p + 1 ∧ _ at hiv_p
      rw [hstep_p] at hiv_p
      exact hiv_p.2.1
    · have hpm : p + 1 = m := by omega
      rw [hpm]; exact (equiEndpoint_monotone (by omega)).trans (equiEndpoint_hi (by omega)).le
  -- Helper: non-straddle witness from pair 1
  have pair1_ns : ∀ kv : ℕ,
      (kv = j₀ % 3 ∨ kv = (j₀ + 1) % 3) →
      eqp_idx q r (v + 1) = eqp_idx q r v →
      ∃ a ∈ ({0, 1, g, g + 1} : Finset ℕ), c (v + a) = kv := by
    intro kv hkv h1_same
    have hv1_lt : v + 1 < m := by
      rcases eqp_idx_succ_lt_m m q r s v hq_pos hr_lt hm_eq hv_lt with h | h
      · exact h
      · rw [h1_same] at h; have : j₀ = s := h; omega
    obtain ⟨d, hd_mem, hd_eq⟩ := non_straddle_witness m q r v
      hq_pos hv_lt hv1_lt h1_same j₀ rfl kv hkv
    exact ⟨d, by simp only [Finset.mem_insert,
      Finset.mem_singleton] at hd_mem ⊢; omega, hd_eq⟩
  -- Helper: non-straddle witness from pair 2
  have pair2_ns : ∀ kv : ℕ,
      (kv = jg % 3 ∨ kv = (jg + 1) % 3) →
      eqp_idx q r (((v + g) % m) + 1) = eqp_idx q r ((v + g) % m) →
      ∃ a ∈ ({0, 1, g, g + 1} : Finset ℕ), c (v + a) = kv := by
    intro kv hkv h2_same
    have hvg_lt : (v + g) % m < m := Nat.mod_lt _ (by omega)
    have hvg1_lt : (v + g) % m + 1 < m := by
      rcases eqp_idx_succ_lt_m m q r s ((v + g) % m) hq_pos hr_lt hm_eq hvg_lt with h | h
      · exact h
      · rw [h2_same] at h; have : jg = s := h; omega
    obtain ⟨d, hd_mem, hd_eq⟩ := non_straddle_witness m q r
      ((v + g) % m) hq_pos hvg_lt hvg1_lt h2_same jg rfl kv hkv
    refine ⟨g + d, ?_, ?_⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hd_mem ⊢; omega
    · change (idx ((v + (g + d)) % m) + off ((v + (g + d)) % m) % 2) % 3 = kv
      rw [vg_mod_shift m v g d]; exact hd_eq
  -- Helper: both-straddle contradiction
  open Finpartition in
  have both_straddle_absurd :
      eqp_idx q r (v + 1) = eqp_idx q r v + 1 →
      eqp_idx q r (((v + g) % m) + 1) = eqp_idx q r ((v + g) % m) + 1 → False := by
    intro h1_step h2_step
    have hstrad1 : equiEndpoint m s (j₀ + 1) ≤ v + 1 := endpoint_bridge v hv_lt hj₀_lt h1_step
    have hstrad2 : equiEndpoint m s (jg + 1) ≤ (v + g) % m + 1 :=
      endpoint_bridge ((v + g) % m) (Nat.mod_lt _ (by omega)) hjg_lt h2_step
    have hgap2 := straddle1_gap2 s g m hs hs3_le hs_le h_lb
      h_ub v j₀ jg hv_lt hj₀_lt hjg_lt hv_hi hvg_lo hvg_hi hstrad1 hgap
    have hgap1 := straddle2_gap1 s g m hs3_le hs_le
      h_lb h_ub v j₀ jg hv_lt hj₀_lt hjg_lt hv_lo hv_hi hvg_hi hstrad2 hgap
    omega
  -- Step 1: which pair covers k?
  have : (k.val = j₀ % 3 ∨ k.val = (j₀ + 1) % 3) ∨
      (k.val = jg % 3 ∨ k.val = (jg + 1) % 3) := by omega
  rcases this with hk1 | hk2
  · -- Pair 1 covers k: k ∈ {j₀%3, (j₀+1)%3}
    rcases eqp_idx_step q r v hq_pos with h1_same | h1_step
    · exact pair1_ns k.val hk1 h1_same
    · -- Pair 1 straddles → gap = 2
      open Finpartition in
      have hgap2 : (jg + s - j₀) % s = 2 := by
        have hstrad1 : equiEndpoint m s (j₀ + 1) ≤ v + 1 := endpoint_bridge v hv_lt hj₀_lt h1_step
        exact straddle1_gap2 s g m hs hs3_le hs_le h_lb
          h_ub v j₀ jg hv_lt hj₀_lt hjg_lt hv_hi hvg_lo hvg_hi hstrad1 hgap
      have hjg1_eq : (jg + 1) % 3 = j₀ % 3 := by grind [gap_mod_cases_gen s j₀ jg 2]
      rcases hk1 with hk_eq | hk_eq
      · -- k = j₀%3 = (jg+1)%3: pair 2 must be non-straddle
        rcases eqp_idx_step q r ((v + g) % m) hq_pos with h2_same | h2_step
        · exact pair2_ns k.val (Or.inr (hk_eq ▸ hjg1_eq.symm)) h2_same
        · exact absurd h1_step (both_straddle_absurd h1_step h2_step).elim
      · -- k = (j₀+1)%3: witness a = 1
        refine ⟨1, by simp, ?_⟩
        change (eqp_idx q r ((v + 1) % m) + eqp_off q r ((v + 1) % m) % 2) % 3 = k.val
        rw [straddle_boundary_color m q r s v hq_pos hr_lt hs3 hm_eq hv_lt h1_step j₀ rfl]
        exact hk_eq.symm
  · -- Pair 2 covers k: k ∈ {jg%3, (jg+1)%3}
    rcases eqp_idx_step q r ((v + g) % m) hq_pos with h2_same | h2_step
    · exact pair2_ns k.val hk2 h2_same
    · -- Pair 2 straddles → gap = 1
      open Finpartition in
      have hgap1 : (jg + s - j₀) % s = 1 := by
        have hvg_lt : (v + g) % m < m := Nat.mod_lt _ (by omega)
        have hstrad2 : equiEndpoint m s (jg + 1) ≤ (v + g) % m + 1 :=
          endpoint_bridge ((v + g) % m) hvg_lt hjg_lt h2_step
        exact straddle2_gap1 s g m hs3_le hs_le h_lb
          h_ub v j₀ jg hv_lt hj₀_lt hjg_lt hv_lo hv_hi hvg_hi hstrad2 hgap
      have hj01_eq : (j₀ + 1) % 3 = jg % 3 := by grind [gap_mod_cases_gen s j₀ jg 1]
      rcases hk2 with hk_eq | hk_eq
      · -- k = jg%3 = (j₀+1)%3: pair 1 must be non-straddle
        rcases eqp_idx_step q r v hq_pos with h1_same | h1_step
        · exact pair1_ns k.val (Or.inr (hk_eq ▸ hj01_eq.symm)) h1_same
        · exact absurd h1_step (both_straddle_absurd h1_step h2_step).elim
      · -- k = (jg+1)%3: witness a = g+1
        have hvg_lt : (v + g) % m < m := Nat.mod_lt _ (by omega)
        refine ⟨g + 1, by simp, ?_⟩
        change (idx ((v + (g + 1)) % m) + off ((v + (g + 1)) % m) % 2) % 3 = k.val
        rw [vg_mod_shift m v g 1]
        change (eqp_idx q r (((v + g) % m + 1) % m) +
          eqp_off q r (((v + g) % m + 1) % m) % 2) % 3 = k.val
        rw [straddle_boundary_color m q r s ((v + g) % m)
          hq_pos hr_lt hs3 hm_eq hvg_lt h2_step jg rfl]
        exact hk_eq.symm
