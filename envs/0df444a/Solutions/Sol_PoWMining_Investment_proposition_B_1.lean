-- Prove2me | solution 1 for PoWMining.Investment.proposition_B_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:12:40.436656+00:00
-- url     : https://prove2.me/submissions/a8f92938-e815-4054-80b7-1cdefe7b6506

import Mathlib
import Definitions.Def_PoWMining_Investment_ClosedForm

set_option autoImplicit false
open PoWMining.Investment PoWMining.CostStatics

theorem pwm_cum_update {n : ℕ} (c : Fin n → ℝ) (k : Fin n) (t : ℝ) :
    cumCost (Function.update c k t) = cumCost c - c k + t := by
  unfold cumCost
  rw [Finset.sum_update_of_mem (Finset.mem_univ k), Finset.sdiff_singleton_eq_erase,
    ← Finset.add_sum_erase Finset.univ c (Finset.mem_univ k)]
  ring

theorem pwm_cum_pos {n : ℕ} (c : Fin n → ℝ) (hn : 2 ≤ n) (hc : ∀ k, 0 < c k) : 0 < cumCost c := by
  unfold cumCost
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  exact Finset.sum_pos (fun k _ => hc k) Finset.univ_nonempty

theorem pwm_g_pos {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hn : 2 ≤ n) (hR : 0 < R) (hγ : 0 ≤ γ)
    (hc : ∀ k, 0 < c k) : 0 < gH c γ R := by
  have hC := pwm_cum_pos c hn hc
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  unfold gH
  split_ifs with h
  · apply div_pos _ (by linarith)
    rw [sub_pos]
    apply Real.lt_sqrt_of_sq_lt
    nlinarith [mul_pos (mul_pos (by linarith : (0:ℝ) < (n:ℝ) - 1) hR) h]
  · exact div_pos (mul_pos (by linarith) hR) hC

theorem pwm_g_deriv {n : ℕ} (c : Fin n → ℝ) (k : Fin n) (γ R : ℝ) (hn : 2 ≤ n) (hR : 0 < R)
    (hγ : 0 ≤ γ) (hc : ∀ j, 0 < c j) :
    HasDerivAt (fun t => gH (Function.update c k t) γ R)
      (-(gH c γ R) / (2 * γ * gH c γ R + cumCost c)) (c k) := by
  have hC := pwm_cum_pos c hn hc
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  set K : ℝ := cumCost c - c k with hK
  have hy : HasDerivAt (fun t : ℝ => K + t) 1 (c k) := by
    simpa using (hasDerivAt_id (c k)).const_add K
  have hyc : K + c k = cumCost c := by rw [hK]; ring
  by_cases hγp : 0 < γ
  · have hfun : (fun t => gH (Function.update c k t) γ R) =
        fun t => (Real.sqrt ((K + t) ^ 2 + 4 * ((n : ℝ) - 1) * R * γ) - (K + t)) / (2 * γ) := by
      funext t
      simp only [gH, hγp, if_true, pwm_cum_update, hK]
      all_goals ring_nf
    rw [hfun]
    set A : ℝ := 4 * ((n : ℝ) - 1) * R * γ with hA
    have hApos : 0 < A := by rw [hA]; have : 0 < (n:ℝ) - 1 := by linarith
                             positivity
    have h1 : HasDerivAt (fun t : ℝ => (K + t) ^ 2 + A) (2 * (K + c k) * 1) (c k) := by
      simpa using (hy.pow 2).add_const A
    have hne : (K + c k) ^ 2 + A ≠ 0 := by positivity
    have h2 := h1.sqrt hne
    have h3 : HasDerivAt (fun t : ℝ => (Real.sqrt ((K + t) ^ 2 + A) - (K + t)) / (2 * γ))
        ((2 * (K + c k) * 1 / (2 * Real.sqrt ((K + c k) ^ 2 + A)) - 1) / (2 * γ)) (c k) :=
      (h2.sub hy).div_const (2 * γ)
    have hs : 0 < Real.sqrt ((K + c k) ^ 2 + A) := Real.sqrt_pos.mpr (by positivity)
    have hg : gH c γ R = (Real.sqrt (cumCost c ^ 2 + A) - cumCost c) / (2 * γ) := by
      simp only [gH, hγp, if_true, hA]
    refine h3.congr_deriv ?_
    rw [hg, hyc]
    have hS : 0 < Real.sqrt (cumCost c ^ 2 + A) := by rw [← hyc]; exact hs
    generalize Real.sqrt (cumCost c ^ 2 + A) = S at hS ⊢
    generalize cumCost c = C at hS hC ⊢
    have hSC : 2 * γ * ((S - C) / (2 * γ)) + C = S := by field_simp; ring
    rw [hSC]
    field_simp
    ring
  · have hγ0 : γ = 0 := le_antisymm (not_lt.mp hγp) hγ
    subst hγ0
    have hfun : (fun t => gH (Function.update c k t) 0 R) =
        fun t => ((n : ℝ) - 1) * R / (K + t) := by
      funext t
      simp only [gH, hγp, if_false, pwm_cum_update, hK]
      all_goals ring_nf
    rw [hfun]
    have hKc : K + c k ≠ 0 := by rw [hyc]; exact hC.ne'
    have h3 : HasDerivAt (fun t : ℝ => ((n : ℝ) - 1) * R / (K + t))
        ((0 * (K + c k) - ((n : ℝ) - 1) * R * 1) / (K + c k) ^ 2) (c k) :=
      (hasDerivAt_const (c k) (((n : ℝ) - 1) * R)).div hy hKc
    refine h3.congr_deriv ?_
    have hg : gH c 0 R = ((n : ℝ) - 1) * R / cumCost c := by simp [gH]
    rw [hg, hyc]
    field_simp
    ring

theorem pwm_own_main (R γ : ℝ) (hR : 0 < R) (hγ : 0 ≤ γ) (gf : ℝ → ℝ) (t0 C : ℝ)
    (hg : HasDerivAt gf (-(gf t0) / (2 * γ * gf t0 + C)) t0) (hg0 : 0 < gf t0) (hC : t0 < C)
    (ht0 : 0 < t0) (ha : 0 < R - t0 * gf t0) :
    ∃ d : ℝ, HasDerivAt (fun t => (R - t * gf t) ^ 2 * (2 * R + γ * gf t ^ 2) /
      (2 * (R + γ * gf t ^ 2) ^ 2)) d t0 ∧ d < 0 := by
  obtain ⟨s, hsdef⟩ : ∃ s, s = 2 * γ * gf t0 + C := ⟨_, rfl⟩
  rw [← hsdef] at hg
  set g := gf t0 with hgdef
  set g' := -g / s with hg'
  have hs : 0 < s := by rw [hsdef]; nlinarith [mul_nonneg hγ hg0.le]
  have hs' : s ≠ 0 := hs.ne'
  have hq : 0 < R + γ * g ^ 2 := by positivity
  have hq' : R + γ * g ^ 2 ≠ 0 := hq.ne'
  have hN1 : HasDerivAt (fun t => R - t * gf t) (0 - (1 * gf t0 + t0 * g')) t0 :=
    (hasDerivAt_const t0 R).sub ((hasDerivAt_id' t0).mul hg)
  have hN2 : HasDerivAt (fun t => 2 * R + γ * gf t ^ 2) (γ * (↑(2:ℕ) * gf t0 ^ (2 - 1) * g')) t0 :=
    ((hg.pow 2).const_mul γ).const_add (2 * R)
  have hD : HasDerivAt (fun t => R + γ * gf t ^ 2) (γ * (↑(2:ℕ) * gf t0 ^ (2 - 1) * g')) t0 :=
    ((hg.pow 2).const_mul γ).const_add R
  have hne : (fun y => 2 * ((fun t => R + γ * gf t ^ 2) ^ 2) y) t0 ≠ 0 := by
    show 2 * (R + γ * g ^ 2) ^ 2 ≠ 0
    positivity
  have hall := (((hN1.pow 2).mul hN2).div ((hD.pow 2).const_mul 2) hne)
  have ha' : 0 < R - t0 * g := ha
  refine ⟨-(g * (R - t0 * g) / (s * (R + γ * g ^ 2) ^ 3)) *
        ((s - t0) * (2 * R + γ * g ^ 2) * (R + γ * g ^ 2) -
          (R - t0 * g) * γ * g * (3 * R + γ * g ^ 2)), ?_, ?_⟩
  · refine hall.congr_deriv ?_
    simp only [Pi.pow_apply, Pi.mul_apply, Nat.cast_ofNat]
    norm_num
    rw [hg']
    field_simp
    ring
  · have hx : 0 ≤ γ * g := mul_nonneg hγ hg0.le
    have hx2 : 0 ≤ γ * g ^ 2 := by positivity
    have h2 : R - t0 * g ≤ R := by nlinarith [mul_pos ht0 hg0]
    have h3 : (R - t0 * g) * (3 * R + γ * g ^ 2) ≤ R * (3 * R + γ * g ^ 2) :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    have hk : 0 ≤ 2 * (2 * R + γ * g ^ 2) * (R + γ * g ^ 2) - (R - t0 * g) * (3 * R + γ * g ^ 2) := by
      nlinarith [mul_nonneg hR.le hx2, sq_nonneg (γ * g ^ 2), sq_nonneg R]
    have h1 : 0 < (C - t0) * (2 * R + γ * g ^ 2) * (R + γ * g ^ 2) := by
      have : 0 < C - t0 := sub_pos.mpr hC
      positivity
    have hB : 0 < (s - t0) * (2 * R + γ * g ^ 2) * (R + γ * g ^ 2) -
        (R - t0 * g) * γ * g * (3 * R + γ * g ^ 2) := by
      have e : (s - t0) * (2 * R + γ * g ^ 2) * (R + γ * g ^ 2) -
          (R - t0 * g) * γ * g * (3 * R + γ * g ^ 2) =
          (C - t0) * (2 * R + γ * g ^ 2) * (R + γ * g ^ 2) +
            (γ * g) * (2 * (2 * R + γ * g ^ 2) * (R + γ * g ^ 2) - (R - t0 * g) * (3 * R + γ * g ^ 2)) := by
        rw [hsdef]; ring
      rw [e]
      have := mul_nonneg hx hk
      linarith
    have : 0 < g * (R - t0 * g) / (s * (R + γ * g ^ 2) ^ 3) := by positivity
    nlinarith

theorem pwm_riv_main (R γ : ℝ) (hR : 0 < R) (hγ : 0 ≤ γ) (gf : ℝ → ℝ) (t0 C c : ℝ)
    (hg : HasDerivAt gf (-(gf t0) / (2 * γ * gf t0 + C)) t0) (hg0 : 0 < gf t0) (hC : 0 < C)
    (hc : 0 < c) (ha : 0 < R - c * gf t0) :
    ∃ d : ℝ, HasDerivAt (fun t => (R - c * gf t) ^ 2 * (2 * R + γ * gf t ^ 2) /
      (2 * (R + γ * gf t ^ 2) ^ 2)) d t0 ∧ 0 < d := by
  obtain ⟨s, hsdef⟩ : ∃ s, s = 2 * γ * gf t0 + C := ⟨_, rfl⟩
  rw [← hsdef] at hg
  set g := gf t0 with hgdef
  set g' := -g / s with hg'
  have hs : 0 < s := by rw [hsdef]; nlinarith [mul_nonneg hγ hg0.le]
  have hs' : s ≠ 0 := hs.ne'
  have hq : 0 < R + γ * g ^ 2 := by positivity
  have hq' : R + γ * g ^ 2 ≠ 0 := hq.ne'
  have hN1 : HasDerivAt (fun t => R - c * gf t) (0 - c * g') t0 :=
    (hasDerivAt_const t0 R).sub (hg.const_mul c)
  have hN2 : HasDerivAt (fun t => 2 * R + γ * gf t ^ 2) (γ * (↑(2:ℕ) * gf t0 ^ (2 - 1) * g')) t0 :=
    ((hg.pow 2).const_mul γ).const_add (2 * R)
  have hD : HasDerivAt (fun t => R + γ * gf t ^ 2) (γ * (↑(2:ℕ) * gf t0 ^ (2 - 1) * g')) t0 :=
    ((hg.pow 2).const_mul γ).const_add R
  have hne : (fun y => 2 * ((fun t => R + γ * gf t ^ 2) ^ 2) y) t0 ≠ 0 := by
    show 2 * (R + γ * g ^ 2) ^ 2 ≠ 0
    positivity
  have hall := (((hN1.pow 2).mul hN2).div ((hD.pow 2).const_mul 2) hne)
  refine ⟨g / s * (c * (R - c * g) * (2 * R + γ * g ^ 2) / (R + γ * g ^ 2) ^ 2 +
      γ * g * (R - c * g) ^ 2 * (3 * R + γ * g ^ 2) / (R + γ * g ^ 2) ^ 3), ?_, ?_⟩
  · refine hall.congr_deriv ?_
    simp only [Pi.pow_apply, Pi.mul_apply, Nat.cast_ofNat]
    norm_num
    rw [hg']
    field_simp
    ring
  · have hx : 0 ≤ γ * g := mul_nonneg hγ hg0.le
    positivity

theorem pwm_cum_gt {n : ℕ} (c : Fin n → ℝ) (hn : 2 ≤ n) (hc : ∀ k, 0 < c k) (k : Fin n) :
    c k < cumCost c := by
  unfold cumCost
  rw [← Finset.add_sum_erase Finset.univ c (Finset.mem_univ k)]
  have : (Finset.univ.erase k).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ k)]
    simp; omega
  have := Finset.sum_pos (fun j _ => hc j) this
  linarith

theorem pwm_profit_eq {n : ℕ} (cc : Fin n → ℝ) (γ R : ℝ) (i : Fin n) (hR : 0 < R) (hγ : 0 ≤ γ)
    (hg : 0 < gH cc γ R) :
    profitH cc γ R i = (R - cc i * gH cc γ R) ^ 2 * (2 * R + γ * gH cc γ R ^ 2) /
      (2 * (R + γ * gH cc γ R ^ 2) ^ 2) := by
  unfold profitH fH
  generalize gH cc γ R = g at hg ⊢
  have hq : 0 < R + γ * g ^ 2 := by positivity
  field_simp
  ring

theorem solution {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hn : 2 ≤ n) (hR : 0 < R)
    (hγ : 0 ≤ γ) (hc : ∀ k, 0 < c k) (hact : ∀ k, 0 < R - c k * PoWMining.CostStatics.gH c γ R) (i : Fin n) :
    (∃ d : ℝ, HasDerivAt (fun t => profitH (Function.update c i t) γ R i) d (c i) ∧ d < 0) ∧
    (∀ j : Fin n, j ≠ i →
      ∃ d : ℝ, HasDerivAt (fun t => profitH (Function.update c j t) γ R i) d (c j) ∧ 0 < d) := by
  have hg0 : 0 < gH c γ R := pwm_g_pos c γ R hn hR hγ hc
  have hC := pwm_cum_pos c hn hc
  refine ⟨?_, ?_⟩
  · have hg := pwm_g_deriv c i γ R hn hR hγ hc
    set gf : ℝ → ℝ := fun t => gH (Function.update c i t) γ R with hgf
    have e : gf (c i) = gH c γ R := by simp [hgf]
    have hg' : HasDerivAt gf (-(gf (c i)) / (2 * γ * gf (c i) + cumCost c)) (c i) := by
      rw [e]; exact hg
    obtain ⟨d, hd, hneg⟩ := pwm_own_main R γ hR hγ gf (c i) (cumCost c) hg' (by rw [e]; exact hg0)
      (pwm_cum_gt c hn hc i) (hc i) (by rw [e]; exact hact i)
    refine ⟨d, hd.congr_of_eventuallyEq ?_, hneg⟩
    have hev : ∀ᶠ t in nhds (c i), 0 < gf t :=
      hg'.continuousAt.eventually (lt_mem_nhds (by rw [e]; exact hg0))
    filter_upwards [hev] with t ht
    have := pwm_profit_eq (Function.update c i t) γ R i hR hγ ht
    simpa [hgf] using this
  · intro j hji
    have hg := pwm_g_deriv c j γ R hn hR hγ hc
    set gf : ℝ → ℝ := fun t => gH (Function.update c j t) γ R with hgf
    have e : gf (c j) = gH c γ R := by simp [hgf]
    have hg' : HasDerivAt gf (-(gf (c j)) / (2 * γ * gf (c j) + cumCost c)) (c j) := by
      rw [e]; exact hg
    obtain ⟨d, hd, hpos⟩ := pwm_riv_main R γ hR hγ gf (c j) (cumCost c) (c i) hg'
      (by rw [e]; exact hg0) hC (hc i) (by rw [e]; exact hact i)
    refine ⟨d, hd.congr_of_eventuallyEq ?_, hpos⟩
    have hev : ∀ᶠ t in nhds (c j), 0 < gf t :=
      hg'.continuousAt.eventually (lt_mem_nhds (by rw [e]; exact hg0))
    filter_upwards [hev] with t ht
    have := pwm_profit_eq (Function.update c j t) γ R i hR hγ ht
    rw [Function.update_of_ne hji.symm] at this
    simpa [hgf] using this
