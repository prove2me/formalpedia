-- Prove2me | solution 1 for ShockWear.CumDamage.proof34_expSign
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:41:46.792283+00:00
-- url     : https://prove2.me/submissions/32033522-9c43-4365-aef5-93b5cbc624ce

import Mathlib
import Definitions.Def_ShockWear_CumDamage_Model

set_option autoImplicit false
open MeasureTheory ProbabilityTheory

namespace SWP
open ShockWear.CumDamage Filter Topology

lemma poisW_nonneg {lam t : ℝ} (h : 0 ≤ lam * t) (k : ℕ) : 0 ≤ poisW lam t k := by
  unfold poisW; positivity

lemma exp_hasSum (x : ℝ) : HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
  have := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) x
  rwa [← Real.exp_eq_exp_ℝ] at this

lemma poisW_hasSum (lam t : ℝ) : HasSum (poisW lam t) 1 := by
  have h := (exp_hasSum (lam * t)).mul_left (Real.exp (-(lam * t)))
  have e : Real.exp (-(lam * t)) * Real.exp (lam * t) = 1 := by
    rw [← Real.exp_add]; simp
  rw [e] at h
  have e2 : poisW lam t = fun k : ℕ => Real.exp (-(lam * t)) * ((lam * t) ^ k / (k.factorial : ℝ)) := by
    funext k; unfold poisW; ring
  rw [e2]; exact h

lemma summable_mul_poisW {lam t : ℝ} (h : 0 ≤ lam * t) {a : ℕ → ℝ} (ha : ∀ k, |a k| ≤ 1) :
    Summable (fun k => a k * poisW lam t k) := by
  refine Summable.of_norm_bounded (poisW_hasSum lam t).summable ?_
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (poisW_nonneg h k)]
  calc |a k| * poisW lam t k ≤ 1 * poisW lam t k :=
        mul_le_mul_of_nonneg_right (ha k) (poisW_nonneg h k)
    _ = poisW lam t k := one_mul _

lemma summable_norm_mul_poisW {lam t : ℝ} (h : 0 ≤ lam * t) {a : ℕ → ℝ} (ha : ∀ k, |a k| ≤ 1) :
    Summable (fun k => ‖a k * poisW lam t k‖) := by
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) (poisW_hasSum lam t).summable
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (poisW_nonneg h k)]
  calc |a k| * poisW lam t k ≤ 1 * poisW lam t k :=
        mul_le_mul_of_nonneg_right (ha k) (poisW_nonneg h k)
    _ = poisW lam t k := one_mul _

lemma surv_eq {lam : ℝ} {P : ℕ → ℝ} {t : ℝ} (ht : 0 ≤ t) :
    shockSurv lam P t = ∑' k, P k * poisW lam t k := by
  unfold shockSurv; rw [if_neg (not_lt.2 ht)]

lemma surv_zero (lam : ℝ) (P : ℕ → ℝ) : shockSurv lam P 0 = P 0 := by
  rw [surv_eq le_rfl]
  rw [tsum_eq_single 0 (fun k hk => by simp [poisW, hk])]
  simp [poisW]

lemma Pbound {P : ℕ → ℝ} (hP0 : P 0 ≤ 1) (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k) :
    ∀ k, |P k| ≤ 1 := by
  intro k
  rw [abs_of_nonneg (hnn k)]
  exact (hanti (Nat.zero_le k)).trans hP0

theorem eq26_core (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ) (hP0 : P 0 ≤ 1) (hanti : Antitone P)
    (hnn : ∀ k, 0 ≤ P k) :
    ∀ t, 0 ≤ t → shockSurv lam P 0 * Real.exp (-(lam * t)) ≤ shockSurv lam P t := by
  intro t ht
  have hlt : 0 ≤ lam * t := mul_nonneg hlam.le ht
  rw [surv_zero, surv_eq ht]
  have hs := summable_mul_poisW hlt (Pbound hP0 hanti hnn)
  have h1 : P 0 * poisW lam t 0 ≤ ∑' k, P k * poisW lam t k :=
    hs.le_tsum 0 (fun j _ => mul_nonneg (hnn j) (poisW_nonneg hlt j))
  have h2 : poisW lam t 0 = Real.exp (-(lam * t)) := by simp [poisW]
  rw [h2] at h1
  exact h1

lemma surv_bounds {lam : ℝ} (hlam : 0 < lam) {P : ℕ → ℝ} (hP0 : P 0 ≤ 1) (hanti : Antitone P)
    (hnn : ∀ k, 0 ≤ P k) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ shockSurv lam P t ∧ shockSurv lam P t ≤ 1 := by
  have hlt : 0 ≤ lam * t := mul_nonneg hlam.le ht
  rw [surv_eq ht]
  refine ⟨tsum_nonneg (fun k => mul_nonneg (hnn k) (poisW_nonneg hlt k)), ?_⟩
  have hs := summable_mul_poisW hlt (Pbound hP0 hanti hnn)
  have h1 : ∑' k, P k * poisW lam t k ≤ ∑' k, poisW lam t k := by
    refine hs.tsum_le_tsum (fun k => ?_) (poisW_hasSum lam t).summable
    calc P k * poisW lam t k ≤ 1 * poisW lam t k :=
          mul_le_mul_of_nonneg_right ((hanti (Nat.zero_le k)).trans hP0) (poisW_nonneg hlt k)
      _ = poisW lam t k := one_mul _
  rw [(poisW_hasSum lam t).tsum_eq] at h1
  exact h1

theorem transfer_eq (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ) (hP0 : P 0 ≤ 1) (hanti : Antitone P)
    (hnn : ∀ k, 0 ≤ P k) (ζ : ℝ) (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1) :
    ∀ t, 0 ≤ t → shockSurv lam P t - Real.exp (-((1 - ζ) * lam * t)) =
        ∑' k, (P k - ζ ^ k) * poisW lam t k := by
  intro t ht
  have hlt : 0 ≤ lam * t := mul_nonneg hlam.le ht
  have hs := summable_mul_poisW hlt (Pbound hP0 hanti hnn)
  have hz : HasSum (fun k => ζ ^ k * poisW lam t k) (Real.exp (-((1 - ζ) * lam * t))) := by
    have h := (exp_hasSum (ζ * (lam * t))).mul_left (Real.exp (-(lam * t)))
    have e : Real.exp (-(lam * t)) * Real.exp (ζ * (lam * t)) = Real.exp (-((1 - ζ) * lam * t)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e] at h
    have e2 : (fun k : ℕ => ζ ^ k * poisW lam t k) =
        fun k : ℕ => Real.exp (-(lam * t)) * ((ζ * (lam * t)) ^ k / (k.factorial : ℝ)) := by
      funext k; unfold poisW; rw [mul_pow]; ring
    rw [e2]; exact h
  have h2 := hs.hasSum.sub hz
  rw [surv_eq ht]
  have e3 : (fun k => (P k - ζ ^ k) * poisW lam t k) =
      fun k => P k * poisW lam t k - ζ ^ k * poisW lam t k := by
    funext k; ring
  rw [e3]
  exact h2.tsum_eq.symm

theorem sign_transfer {lam : ℝ} (hlam : 0 < lam) {a : ℕ → ℝ} (ha : ∀ k, |a k| ≤ 1)
    (hseq : SignPMSeq a) :
    SignPM (fun t => ∑' k, a k * poisW lam t k) (Set.Ici 0) := by
  intro s hs t ht hst hcon
  obtain ⟨hgs, hgt⟩ := hcon
  beta_reduce at hgs hgt
  have hs0 : 0 ≤ s := hs
  have ht0 : 0 < t := lt_of_le_of_lt hs0 hst
  have hnnt : ∀ k, 0 ≤ poisW lam t k := poisW_nonneg (mul_nonneg hlam.le ht0.le)
  have hnns : ∀ k, 0 ≤ poisW lam s k := poisW_nonneg (mul_nonneg hlam.le hs0)
  rcases hs0.eq_or_lt with h0 | hpos
  · subst h0
    have hg0 : (∑' k, a k * poisW lam 0 k) = a 0 := by
      rw [tsum_eq_single 0 (fun k hk => by simp [poisW, hk])]
      simp [poisW]
    rw [hg0] at hgs
    have hle : ∀ k, a k ≤ 0 := by
      intro k
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; exact hgs.le
      · by_contra hc
        push Not at hc
        exact hseq 0 k hk ⟨hgs, hc⟩
    have h5 : ∑' k, a k * poisW lam t k ≤ 0 :=
      tsum_nonpos (fun k => mul_nonpos_of_nonpos_of_nonneg (hle k) (hnnt k))
    linarith
  · have hex : ∃ k, a k < 0 := by
      by_contra hc
      push Not at hc
      have h5 : 0 ≤ ∑' k, a k * poisW lam s k :=
        tsum_nonneg (fun k => mul_nonneg (hc k) (hnns k))
      linarith
    classical
    set m := Nat.find hex with hmdef
    have hm : a m < 0 := Nat.find_spec hex
    have hbefore : ∀ k, k < m → 0 ≤ a k := fun k hk => not_lt.1 (Nat.find_min hex hk)
    have hafter : ∀ k, m ≤ k → a k ≤ 0 := by
      intro k hk
      rcases hk.eq_or_lt with h | h
      · rw [← h]; exact hm.le
      · by_contra hc
        push Not at hc
        exact hseq m k h ⟨hm, hc⟩
    set ρ : ℝ := t / s with hρdef
    have hρ : 1 ≤ ρ := (one_le_div hpos).2 hst.le
    have hid : ∀ k, poisW lam t k = Real.exp (-(lam * (t - s))) * ρ ^ k * poisW lam s k := by
      intro k
      unfold poisW
      have h1 : lam * t = lam * s * ρ := by rw [hρdef]; field_simp
      have h2 : Real.exp (-(lam * t)) = Real.exp (-(lam * (t - s))) * Real.exp (-(lam * s)) := by
        rw [← Real.exp_add]; congr 1; ring
      have h3 : (lam * t) ^ k = (lam * s) ^ k * ρ ^ k := by rw [h1, mul_pow]
      rw [h2, h3]; ring
    have hk : ∀ k, a k * ρ ^ k ≤ a k * ρ ^ m := by
      intro k
      by_cases hkm : k < m
      · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hρ hkm.le) (hbefore k hkm)
      · push Not at hkm
        exact mul_le_mul_of_nonpos_left (pow_le_pow_right₀ hρ hkm) (hafter k hkm)
    set C : ℝ := ρ ^ m * Real.exp (-(lam * (t - s))) with hC
    have hCpos : 0 < C := by
      have : 0 < ρ := by linarith
      positivity
    have hterm : ∀ k, a k * poisW lam t k ≤ C * (a k * poisW lam s k) := by
      intro k
      rw [hid k]
      have h1 := mul_le_mul_of_nonneg_right (hk k)
        (mul_nonneg (Real.exp_pos (-(lam * (t - s)))).le (hnns k))
      rw [hC]
      nlinarith [h1]
    have hsumt := summable_mul_poisW (mul_nonneg hlam.le ht0.le) ha
    have hsums := summable_mul_poisW (mul_nonneg hlam.le hs0) ha
    have hle := hsumt.tsum_le_tsum hterm (hsums.mul_left C)
    rw [tsum_mul_left] at hle
    nlinarith

theorem seq_sign (P : ℕ → ℝ) (hP0 : P 0 = 1) (hnn : ∀ k, 0 ≤ P k)
    (hroot : ∀ j k : ℕ, 1 ≤ j → j ≤ k → P k ^ (1 / (k : ℝ)) ≤ P j ^ (1 / (j : ℝ))) :
    ∀ ζ : ℝ, 0 ≤ ζ → ζ ≤ 1 → SignPMSeq (fun k => P k - ζ ^ k) := by
  intro ζ hζ0 hζ1 j k hjk hcon
  obtain ⟨hj, hk⟩ := hcon
  beta_reduce at hj hk
  rcases Nat.eq_zero_or_pos j with h0 | hjpos
  · subst h0; simp [hP0] at hj
  · have hjk' : 1 ≤ j := hjpos
    have hkpos : 0 < k := lt_trans hjpos hjk
    have hPj : P j < ζ ^ j := by linarith
    have h1 : P j ^ (1 / (j : ℝ)) < ζ := by
      have h2 : P j ^ (1 / (j : ℝ)) < (ζ ^ j) ^ (1 / (j : ℝ)) :=
        Real.rpow_lt_rpow (hnn j) hPj (by positivity)
      rw [one_div, Real.pow_rpow_inv_natCast hζ0 (by omega)] at h2
      rwa [one_div]
    have h3 := hroot j k hjk' hjk.le
    have h4 : P k ^ (1 / (k : ℝ)) < ζ := lt_of_le_of_lt h3 h1
    have h5 : (P k ^ (1 / (k : ℝ))) ^ k < ζ ^ k :=
      pow_lt_pow_left₀ h4 (Real.rpow_nonneg (hnn k) _) (by omega)
    rw [one_div, Real.rpow_inv_natCast_pow (hnn k) (by omega)] at h5
    linarith

theorem exp_sign (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ) (hP0 : P 0 = 1)
    (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k)
    (hroot : ∀ j k : ℕ, 1 ≤ j → j ≤ k → P k ^ (1 / (k : ℝ)) ≤ P j ^ (1 / (j : ℝ))) :
    ∀ θ : ℝ, 0 < θ → SignPM (fun t => shockSurv lam P t - Real.exp (-(θ * t))) (Set.Ici 0) := by
  intro θ hθ
  by_cases hθl : θ < lam
  · obtain ⟨ζ, hζdef⟩ : ∃ ζ : ℝ, ζ = 1 - θ / lam := ⟨_, rfl⟩
    have hq : θ / lam < 1 := (div_lt_one hlam).2 hθl
    have hq0 : 0 < θ / lam := div_pos hθ hlam
    have hζ0 : 0 ≤ ζ := by rw [hζdef]; linarith
    have hζ1 : ζ ≤ 1 := by rw [hζdef]; linarith
    have e : (1 - ζ) * lam = θ := by
      have : 1 - ζ = θ / lam := by rw [hζdef]; ring
      rw [this, div_mul_cancel₀ _ hlam.ne']
    have hab : ∀ k, |P k - ζ ^ k| ≤ 1 := by
      intro k
      have h1 : P k ≤ 1 := (hanti (Nat.zero_le k)).trans hP0.le
      have h2 : 0 ≤ P k := hnn k
      have h3 : 0 ≤ ζ ^ k := pow_nonneg hζ0 k
      have h4 : ζ ^ k ≤ 1 := pow_le_one₀ hζ0 hζ1
      rw [abs_le]; constructor <;> linarith
    have hseq := seq_sign P hP0 hnn hroot ζ hζ0 hζ1
    have h := sign_transfer hlam hab hseq
    intro s hs t ht hst hcon
    obtain ⟨hgs, hgt⟩ := hcon
    apply h s hs t ht hst
    beta_reduce at hgs hgt ⊢
    rw [← transfer_eq lam hlam P hP0.le hanti hnn ζ hζ0 hζ1 s hs,
      ← transfer_eq lam hlam P hP0.le hanti hnn ζ hζ0 hζ1 t ht]
    have e' : ∀ u : ℝ, (1 - ζ) * lam * u = θ * u := fun u => by rw [e]
    rw [e' s, e' t]
    exact ⟨hgs, hgt⟩
  · push Not at hθl
    intro s hs t ht hst hcon
    obtain ⟨hgs, hgt⟩ := hcon
    beta_reduce at hgs hgt
    have hs0 : 0 ≤ s := hs
    have h1 := eq26_core lam hlam P hP0.le hanti hnn s hs0
    rw [surv_zero, hP0, one_mul] at h1
    have h2 : Real.exp (-(θ * s)) ≤ Real.exp (-(lam * s)) := by
      apply Real.exp_le_exp.2
      nlinarith
    linarith

theorem ihra_core (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ) (hP0 : P 0 = 1)
    (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k)
    (hroot : ∀ j k : ℕ, 1 ≤ j → j ≤ k → P k ^ (1 / (k : ℝ)) ≤ P j ^ (1 / (j : ℝ))) :
    IsIHRA (shockSurv lam P) := by
  intro s hs t ht hst
  beta_reduce
  by_contra hcon
  push Not at hcon
  have hs0 : 0 < s := hs
  have ht0 : 0 < t := ht
  have hne : s < t := by
    rcases hst.eq_or_lt with h | h
    · subst h; exact absurd hcon (lt_irrefl _)
    · exact h
  obtain ⟨hHs0, hHs1⟩ := surv_bounds hlam hP0.le hanti hnn hs0.le
  obtain ⟨hHt0, hHt1⟩ := surv_bounds hlam hP0.le hanti hnn ht0.le
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = shockSurv lam P s ^ (1 / s) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = shockSurv lam P t ^ (1 / t) := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [ha]; exact Real.rpow_nonneg hHs0 _
  have hb1 : b ≤ 1 := by rw [hb]; exact Real.rpow_le_one hHt0 hHt1 (by positivity)
  have hab : a < b := by rw [ha, hb]; exact hcon
  have hHsa : a ^ s = shockSurv lam P s := by
    rw [ha, ← Real.rpow_mul hHs0, one_div_mul_cancel hs0.ne', Real.rpow_one]
  have hHtb : b ^ t = shockSurv lam P t := by
    rw [hb, ← Real.rpow_mul hHt0, one_div_mul_cancel ht0.ne', Real.rpow_one]
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (a + b) / 2 := ⟨_, rfl⟩
  have hac : a < c := by rw [hc]; linarith
  have hcb : c < b := by rw [hc]; linarith
  have hc0 : 0 < c := by linarith
  have hc1 : c < 1 := by linarith
  have hlogc : Real.log c < 0 := Real.log_neg hc0 hc1
  have hexp : ∀ u : ℝ, Real.exp (-((-Real.log c) * u)) = c ^ u := by
    intro u; rw [Real.rpow_def_of_pos hc0]; congr 1; ring
  have h1 : shockSurv lam P s < c ^ s := by
    rw [← hHsa]; exact Real.rpow_lt_rpow ha0 hac hs0
  have h2 : c ^ t < shockSurv lam P t := by
    rw [← hHtb]; exact Real.rpow_lt_rpow hc0.le hcb ht0
  have := exp_sign lam hlam P hP0 hanti hnn hroot (-Real.log c) (by linarith) s
    (Set.mem_Ici.2 hs0.le) t (Set.mem_Ici.2 ht0.le) hne
  apply this
  beta_reduce
  rw [hexp s, hexp t]
  constructor <;> linarith

end SWP

theorem solution (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ) (hP0 : P 0 = 1)
    (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k)
    (hroot : ∀ j k : ℕ, 1 ≤ j → j ≤ k → P k ^ (1 / (k : ℝ)) ≤ P j ^ (1 / (j : ℝ))) :
    ∀ θ : ℝ, 0 < θ → ShockWear.CumDamage.SignPM (fun t => ShockWear.CumDamage.shockSurv lam P t - Real.exp (-(θ * t))) (Set.Ici 0) :=
  SWP.exp_sign lam hlam P hP0 hanti hnn hroot
