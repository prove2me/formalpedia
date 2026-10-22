-- Prove2me | solution 1 for PegProtect.Equilibrium.proposition_3_2
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T18:58:27.891797+00:00
-- url     : https://prove2.me/submissions/be0d12b6-251c-4c2d-af7b-95fc80918c13

import Mathlib
import Definitions.Def_PegProtect_Equilibrium_Model

open PegProtect.Equilibrium

lemma qneg (ω : ℝ) (n : ℕ) : q ω (-((n : ℤ) + 1)) = (1 - ω) / (1 + ω) * ω * ω ^ n := by
  simp only [q]
  have : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
  rw [this, pow_succ]; ring

lemma qpos (ω : ℝ) (n : ℕ) : q ω (n : ℤ) = (1 - ω) / (1 + ω) * ω ^ n := by
  simp [q]

lemma S1 (ω : ℝ) (h0 : 0 ≤ ω) (h1 : ω < 1) : ∑' n : ℕ, q ω (-((n : ℤ) + 1)) = ω / (1 + ω) := by
  simp only [qneg]
  rw [tsum_mul_left, tsum_geometric_of_lt_one h0 h1]
  have : (1 - ω) ≠ 0 := by linarith
  field_simp

lemma S2 (ω : ℝ) (h0 : 0 ≤ ω) (h1 : ω < 1) : ∑' n : ℕ, q ω (n : ℤ) = 1 / (1 + ω) := by
  simp only [qpos]
  rw [tsum_mul_left, tsum_geometric_of_lt_one h0 h1]
  have : (1 - ω) ≠ 0 := by linarith
  field_simp

lemma S3 (ω β : ℝ) (h0 : 0 ≤ ω) (h1 : ω < 1) (hb0 : 0 < β) (hb1 : β < 1) :
    ∑' n : ℕ, q ω (n : ℤ) * β ^ (n + 1) = (1 - ω) / (1 + ω) * β / (1 - ω * β) := by
  have hωβ0 : 0 ≤ ω * β := by positivity
  have hωβ1 : ω * β < 1 := by nlinarith
  have e : ∀ n : ℕ, q ω (n : ℤ) * β ^ (n + 1) = ((1 - ω) / (1 + ω) * β) * (ω * β) ^ n := by
    intro n; rw [qpos, mul_pow, pow_succ]; ring
  simp only [e]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hωβ0 hωβ1]
  have : (1 - ω * β) ≠ 0 := by linarith
  field_simp

section
variable (P : Params) (hP : P.Standing)
include hP

lemma beta_bounds : 0 < P.beta ∧ P.beta < 1 := by
  obtain ⟨_, _, _, _, hδ, hρ, _⟩ := hP
  refine ⟨Real.exp_pos _, ?_⟩
  unfold Params.beta
  have := div_pos hδ hρ
  calc Real.exp (-(P.δ / P.ρ)) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
    _ = 1 := Real.exp_zero

/-- indifference condition, for `0 ≤ ω < 1` -/
lemma pp_eq_iff (ω : ℝ) (h0 : 0 ≤ ω) (h1 : ω < 1) :
    piP P ω = piM P ω ↔ ω = omegaHat P := by
  obtain ⟨hb0, hb1⟩ := beta_bounds P hP
  obtain ⟨_, _, hd1, _, _, _, _⟩ := hP
  have hωβ : ω * P.beta < 1 := by nlinarith
  unfold piP piM omegaHat
  rw [S1 ω h0 h1, S2 ω h0 h1, S3 ω P.beta h0 h1 hb0 hb1]
  have h1ω : (1 + ω) ≠ 0 := by linarith
  have h2 : (1 - ω * P.beta) ≠ 0 := by linarith
  have h3 : (1 - P.d) ≠ 0 := by linarith
  have hb : P.beta ≠ 0 := hb0.ne'
  constructor
  · intro h
    field_simp at h ⊢
    nlinarith [h]
  · intro h
    rw [eq_div_iff h3] at h
    field_simp
    have : ω * (1 - P.d) * P.beta = (P.phi - P.d) * P.beta - (P.phi - 1) := by
      rw [h]; field_simp
    nlinarith [this]

lemma pp_zero_iff : piP P 0 ≤ piM P 0 ↔ omegaHat P ≤ 0 := by
  obtain ⟨hb0, hb1⟩ := beta_bounds P hP
  obtain ⟨_, _, hd1, _, _, _, _⟩ := hP
  unfold piP piM omegaHat
  rw [S1 0 le_rfl (by norm_num), S2 0 le_rfl (by norm_num), S3 0 P.beta le_rfl (by norm_num) hb0 hb1]
  have h3 : 0 < 1 - P.d := by linarith
  rw [div_le_iff₀ h3, zero_mul]
  simp only [zero_div, add_zero, sub_zero, div_one, mul_zero, zero_add, one_mul]
  have key : P.phi - P.d - P.beta⁻¹ * (P.phi - 1) =
      P.beta⁻¹ * ((P.phi - P.d) * P.beta - (P.phi - 1)) := by
    field_simp
  rw [key]
  have hi : 0 < P.beta⁻¹ := inv_pos.mpr hb0
  constructor
  · intro h
    nlinarith [mul_le_mul_of_nonneg_left
      (show (P.phi - P.d) * P.beta - (P.phi - 1) ≤ 0 by linarith) hi.le]
  · intro h
    by_contra hc
    push_neg at hc
    have := mul_pos hi (by linarith : 0 < (P.phi - P.d) * P.beta - (P.phi - 1))
    linarith

lemma hat_lt_one : omegaHat P < 1 := by
  obtain ⟨hb0, hb1⟩ := beta_bounds P hP
  obtain ⟨_, _, hd1, hphi, _, _, _⟩ := hP
  unfold omegaHat
  rw [div_lt_one (by linarith)]
  have : P.phi - 1 < P.beta⁻¹ * (P.phi - 1) := by
    have : 1 < P.beta⁻¹ := one_lt_inv₀ hb0 |>.mpr hb1
    nlinarith
  linarith

/-- the zero-profit conditions pin down `Nr`, `Ns` given `ω` -/
lemma NrNs (ω Nr Ns : ℝ) (h0 : 0 ≤ ω) (h1 : ω < 1) (hS : piS P Nr Ns = 0) (hR : piR P ω Nr = 0) :
    Nr = P.ρ / P.ν * ((1 - ω) / (1 + ω)) ∧ Ns = 2 * P.ρ / P.c * ((1 - ω) / (1 + ω)) := by
  obtain ⟨hc, _, _, _, _, hρ, hν⟩ := hP
  unfold piR at hR; unfold piS at hS
  rw [S2 ω h0 h1] at hR
  have hNr : Nr ≠ 0 := by rintro rfl; simp at hR; linarith
  have hNs : Ns ≠ 0 := by rintro rfl; simp at hS; linarith
  have h1ω : (1 + ω) ≠ 0 := by linarith
  have eNr : Nr = P.ρ / P.ν * ((1 - ω) / (1 + ω)) := by
    field_simp at hR ⊢; linarith
  refine ⟨eNr, ?_⟩
  have eNs : Ns = 2 * P.ν * Nr / P.c := by field_simp at hS ⊢; linarith
  rw [eNs, eNr]; field_simp

end

theorem solution (P : Params) (hP : P.Standing) :
    IsMarketEquilibrium P (omegaStar P) (NrStar P) (NsStar P) ∧
    ∀ ω Nr Ns : ℝ, IsMarketEquilibrium P ω Nr Ns →
      ω = omegaStar P ∧ Nr = NrStar P ∧ Ns = NsStar P := by
  have hlt := hat_lt_one P hP
  have hstar : omegaStar P = max 0 (omegaHat P) := rfl
  obtain ⟨hc, hd0, hd1, hphi, hδ, hρ, hν⟩ := hP
  have hS0 : 0 ≤ omegaStar P := le_max_left _ _
  have hS1 : omegaStar P < 1 := by rw [hstar]; exact max_lt (by norm_num) hlt
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · by_cases hpos : 0 < omegaHat P
    · left
      have e : omegaStar P = omegaHat P := by rw [hstar]; exact max_eq_right hpos.le
      rw [e]
      exact ⟨hpos, hlt, (pp_eq_iff P ⟨hc, hd0, hd1, hphi, hδ, hρ, hν⟩ _ hpos.le hlt).mpr rfl⟩
    · right
      have e : omegaStar P = 0 := by rw [hstar]; exact max_eq_left (not_lt.mp hpos)
      rw [e]
      exact ⟨rfl, (pp_zero_iff P ⟨hc, hd0, hd1, hphi, hδ, hρ, hν⟩).mpr (not_lt.mp hpos)⟩
  · unfold NsStar
    have : 0 < 1 + omegaStar P := by linarith
    have : 0 ≤ 1 - omegaStar P := by linarith
    positivity
  · unfold NrStar
    have : 0 < 1 + omegaStar P := by linarith
    have : 0 ≤ 1 - omegaStar P := by linarith
    positivity
  · unfold piS NsStar NrStar
    have : 0 < 1 + omegaStar P := by linarith
    have : 0 < 1 - omegaStar P := by linarith
    field_simp; ring
  · unfold piR NrStar
    rw [S2 _ hS0 hS1]
    have : 0 < 1 + omegaStar P := by linarith
    have : 0 < 1 - omegaStar P := by linarith
    field_simp; ring
  · intro ω Nr Ns ⟨hω, _, _, hS, hR⟩
    have hP' : P.Standing := ⟨hc, hd0, hd1, hphi, hδ, hρ, hν⟩
    have hωe : ω = omegaStar P := by
      rcases hω with ⟨h0, h1, he⟩ | ⟨rfl, hle⟩
      · have := (pp_eq_iff P hP' ω h0.le h1).mp he
        rw [hstar, this, max_eq_right (this ▸ h0.le)]
      · rw [hstar, max_eq_left ((pp_zero_iff P hP').mp hle)]
    subst hωe
    obtain ⟨h1, h2⟩ := NrNs P hP' _ Nr Ns hS0 hS1 hS hR
    exact ⟨rfl, h1, h2⟩
