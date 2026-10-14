-- Prove2me | solution 1 for ThreeSum1960614.integer_schedule
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-14T06:44:35.576965+00:00
-- url     : https://prove2.me/submissions/906cdc01-11bb-4e43-a6b5-d2ba8a25e6b0

-- Finite minimum and rounding arguments adapt the pinned upstream Switch.lean.
import Theorems.Thm_ThreeSum1960614_cleared_switch_equivalence
import Theorems.Thm_ThreeSum1960614_quartic_switch_bounds
import Theorems.Thm_ThreeSum1960614_uniform_entropy_bound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
open ThreeSum1960614 Set

private theorem hasDerivAt_phi (t : ℝ) : HasDerivAt phi (phiDeriv t) t := by
  have hd := (((((hasDerivAt_id t).const_mul 785174904).add
    (((hasDerivAt_id t).pow 2).const_mul 72447023)).add
      (((hasDerivAt_id t).pow 3).const_mul 24044466)).add
        (((hasDerivAt_id t).pow 4).const_mul 12022459)).div_const 100000000
  change HasDerivAt phi _ t at hd
  apply hd.congr_deriv
  dsimp [phiDeriv]
  ring

private theorem increment_bound {u t : ℝ}
    (hu : u ∈ Icc (0 : ℝ) (1 / 2)) (ht : t ∈ Icc (0 : ℝ) (1 / 2)) (hut : u < t) :
    phi t - phi u < 9 * (t - u) := by
  apply (convex_Icc (0 : ℝ) (1 / 2)).image_sub_lt_mul_sub_of_deriv_lt
    (fun y _ => (hasDerivAt_phi y).continuousAt.continuousWithinAt)
    (fun y _ => (hasDerivAt_phi y).differentiableAt.differentiableWithinAt)
    (fun y hy => ?_) u hu t ht hut
  rw [(hasDerivAt_phi y).deriv]
  exact (ThreeSum1960614.quartic_switch_bounds y (interior_subset hy)).2.2.1

private theorem ratio_mem_half {r q : ℕ} (hr : 0 < r) (hq : q ≤ r / 2) :
    (q : ℝ) / r ∈ Icc (0 : ℝ) (1 / 2) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have htwo : 2 * q ≤ r := by have hm := Nat.div_mul_le_self r 2; omega
  have htwoR : (2 : ℝ) * q ≤ r := by exact_mod_cast htwo
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ hrR]
  linarith only [htwoR]

private theorem threshold_room {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ tau) :
    threshold a < phi (1 / 2) := by
  have hd : 0 < 1 - a := by dsimp [tau] at ha1; linarith
  rw [threshold, div_lt_iff₀ hd]
  dsimp [v, saving, beta, phi, tau] at *
  linarith only [ha1]

private instance switch_decidable (J s j q : ℕ) : Decidable (clearedSwitch J s j q) := by
  unfold clearedSwitch
  infer_instance

theorem solution (J s j : ℕ)
    (hJ : 0 < J) (hs : 0 < s) (heven : Even s) (hj : j < J)
    (hlevel : (j : ℝ) / J ≤ tau) :
    ∃ q : ℕ, 0 < q ∧ q ≤ ((J - j) * s) / 2 ∧ clearedSwitch J s j q ∧
      (∀ k < q, ¬ clearedSwitch J s j k) ∧
      threshold ((j : ℝ) / J) ≤ phi ((q : ℝ) / ((J - j) * s)) ∧
      phi ((q : ℝ) / ((J - j) * s)) <
        threshold ((j : ℝ) / J) + 9 / ((J - j) * s) ∧
      saving ≤ 2 * beta - (j : ℝ) / J +
        (1 - (j : ℝ) / J) * gamma 232 ((q : ℝ) / ((J - j) * s)) ∧
      (1 - (j : ℝ) / J) * entropy ((q : ℝ) / ((J - j) * s)) <
        rho * (1 + v) + 9 * rho / (J * s) := by
  have hcastR : ((J : ℝ) - j) * s = (((J - j) * s : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_sub hj.le]
  rw [hcastR]
  let r : ℕ := (J - j) * s
  let a : ℝ := (j : ℝ) / J
  have hr : 0 < r := Nat.mul_pos (Nat.sub_pos_of_lt hj) hs
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a ≤ tau := hlevel
  have hden : 0 < 1 - a := by dsimp [tau] at ha1; linarith only [ha1]
  have hmu : (0 : ℝ) < (J : ℝ) * s := by exact_mod_cast Nat.mul_pos hJ hs
  have he : 2 ∣ r := by
    rcases heven with ⟨k, hk⟩
    have hds : 2 ∣ s := ⟨k, by omega⟩
    exact dvd_mul_of_dvd_right hds (J - j)
  have hhalf : ((r / 2 : ℕ) : ℝ) / r = (1 / 2 : ℝ) := by
    have hmR : ((r / 2 : ℕ) : ℝ) * 2 = r := by exact_mod_cast Nat.div_mul_cancel he
    apply (div_eq_iff hrR.ne').2
    linarith only [hmR]
  have hwitness : clearedSwitch J s j (r / 2) := by
    apply (ThreeSum1960614.cleared_switch_equivalence J s j (r / 2) hJ hs hj).mpr
    rw [hcastR]
    change threshold a ≤ phi (((r / 2 : ℕ) : ℝ) / r)
    rw [hhalf]
    exact (threshold_room ha0 ha1).le
  have hex : ∃ q, clearedSwitch J s j q := ⟨r / 2, hwitness⟩
  let q : ℕ := Nat.find hex
  have hclear : clearedSwitch J s j q := Nat.find_spec hex
  have hupper : q ≤ r / 2 := Nat.find_min' hex hwitness
  have hleast : ∀ k < q, ¬ clearedSwitch J s j k := by
    intro k hk
    exact Nat.find_min hex hk
  have hpos : 0 < q := by
    by_contra hn
    have hq0 : q = 0 := by omega
    rw [hq0] at hclear
    have hp : 0 < 100000000 * (159243801 * J + 500000000 * j) * r ^ 4 := by positivity
    change 500000000 * (J - j) *
      (785174904 * 0 * r ^ 3 + 72447023 * 0 ^ 2 * r ^ 2 +
       24044466 * 0 ^ 3 * r + 12022459 * 0 ^ 4) ≥
      100000000 * (159243801 * J + 500000000 * j) * r ^ 4 at hclear
    norm_num at hclear
    omega
  have ht : (q : ℝ) / r ∈ Icc (0 : ℝ) (1 / 2) := ratio_mem_half hr hupper
  have hlow : threshold a ≤ phi ((q : ℝ) / r) := by
    have hc := (ThreeSum1960614.cleared_switch_equivalence J s j q hJ hs hj).mp hclear
    simpa only [hcastR] using hc
  have hprev : phi (((q - 1 : ℕ) : ℝ) / r) < threshold a := by
    apply lt_of_not_ge
    intro hp
    apply hleast (q - 1) (by omega)
    apply (ThreeSum1960614.cleared_switch_equivalence J s j (q - 1) hJ hs hj).mpr
    simpa only [hcastR] using hp
  have hprev_mem : (((q - 1 : ℕ) : ℝ) / r) ∈ Icc (0 : ℝ) (1 / 2) :=
    ratio_mem_half hr (by omega : q - 1 ≤ r / 2)
  have hpR : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]
  have hstep : (q : ℝ) / r - ((q - 1 : ℕ) : ℝ) / r = 1 / r := by rw [hpR]; ring
  have hlt : ((q - 1 : ℕ) : ℝ) / r < (q : ℝ) / r := by
    have hinc : (0 : ℝ) < 1 / r := by positivity
    linarith only [hstep, hinc]
  have hinc := increment_bound hprev_mem ht hlt
  rw [hstep] at hinc
  rw [show (9 : ℝ) * (1 / (r : ℝ)) = 9 / r by ring] at hinc
  have hup : phi ((q : ℝ) / r) < threshold a + 9 / r := by
    linarith only [hinc, hprev]
  have hbox : saving ≤ 2 * beta - a + (1 - a) * gamma 232 ((q : ℝ) / r) := by
    have hc := (div_le_iff₀ hden).mp hlow
    have hg := mul_le_mul_of_nonneg_left
      (ThreeSum1960614.quartic_switch_bounds ((q : ℝ) / r) ht).1 hden.le
    dsimp [threshold, v] at hc
    nlinarith only [hc, hg]
  have hres : (r : ℝ) = (1 - a) * ((J : ℝ) * s) := by
    dsimp [r, a]
    simp only [Nat.cast_mul, Nat.cast_sub hj.le]
    field_simp [hJR.ne']
    <;> ring
  have hent : (1 - a) * entropy ((q : ℝ) / r) < rho * (1 + v) + 9 * rho / (J * s) := by
    have hρ : 0 < rho := by norm_num [rho]
    have he := mul_lt_mul_of_pos_left
      (ThreeSum1960614.uniform_entropy_bound ((q : ℝ) / r) ht) hden
    have hφ : 1 + phi ((q : ℝ) / r) < 1 + (threshold a + 9 / r) := by
      linarith only [hup]
    have hh := mul_lt_mul_of_pos_left hφ (mul_pos hden hρ)
    have hid : (1 - a) * rho * (1 + (threshold a + 9 / r)) =
        rho * (1 + v) + 9 * rho / (J * s) := by
      rw [hres]
      unfold threshold
      field_simp [hden.ne', hmu.ne']
      <;> ring
    rw [← hid]
    nlinarith only [he, hh]
  exact ⟨q, hpos, hupper, hclear, hleast, hlow, hup, hbox, hent⟩
