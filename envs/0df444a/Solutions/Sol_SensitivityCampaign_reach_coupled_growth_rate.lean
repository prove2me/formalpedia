-- Prove2me | solution 1 for SensitivityCampaign.reach_coupled_growth_rate
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-20T05:57:07.662142+00:00
-- url     : https://prove2.me/submissions/557a6028-dbb5-4e8d-bcda-61f5b8f9edaf

import Mathlib
import Definitions.Def_SensitivityCampaign
import Theorems.Thm_SensitivityCampaign_coupled_n15_periodic_seeds
import Theorems.Thm_SensitivityCampaign_finite_certificate

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
open OAI.Paper320
namespace SensitivityPeriodicLog

/-- Every exponent below the growth-rate ratio follows from genuine finite seeds. -/
theorem achieves_strict (c r g : ℕ) (β : ℝ)
    (hc : 1 < c) (hr : 1 < r) (hg : 1 < g) (hβ : 0 ≤ β)
    (hstrict : β < Real.log (g : ℝ) / Real.log (r : ℝ))
    (hseed : ∀ m : ℕ, ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      sensitivity f ≤ c * r ^ m ∧ g ^ m ≤ blockSensitivityAt f (fun _ => false)) :
    SensitivityCampaign.AchievesExponent β := by
  have hcp : (0 : ℝ) < c := by exact_mod_cast (by omega : 0 < c)
  have hr1 : (1 : ℝ) < r := by exact_mod_cast hr
  have hgp : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have hlr : 0 < Real.log (r : ℝ) := Real.log_pos hr1
  have hgap : 0 < Real.log (g : ℝ) - β * Real.log (r : ℝ) := by
    have hh := (lt_div_iff₀ hlr).mp hstrict
    linarith
  let δ := Real.log (g : ℝ) - β * Real.log (r : ℝ)
  obtain ⟨m, hm⟩ := exists_nat_gt (max 0 (β * Real.log (c : ℝ) / δ))
  have hmposr : (0 : ℝ) < m := (le_max_left _ _).trans_lt hm
  have hmpos : 0 < m := by exact_mod_cast hmposr
  have hmul : β * Real.log (c : ℝ) < (m : ℝ) * δ :=
    (div_lt_iff₀ hgap).mp ((le_max_right _ _).trans_lt hm)
  obtain ⟨n, f, hs, hb⟩ := hseed m
  have hA : 1 < c * r ^ m :=
    hc.trans_le (Nat.le_mul_of_pos_right c (pow_pos (by omega : 0 < r) m))
  have hB : 1 < g ^ m := one_lt_pow₀ hg (Nat.ne_of_gt hmpos)
  apply SensitivityCampaign.finite_certificate f (fun _ => false)
    (c * r ^ m) (g ^ m) β hA hB hβ hs hb
  have hrp : (0 : ℝ) < r := by linarith
  have hp : (0 : ℝ) < (c * r ^ m : ℕ) := by exact_mod_cast (by omega : 0 < c * r ^ m)
  have hbp : (0 : ℝ) < (g ^ m : ℕ) := by exact_mod_cast (by omega : 0 < g ^ m)
  apply (Real.rpow_le_iff_le_log hp hbp).2
  push_cast
  rw [Real.log_mul (ne_of_gt hcp) (ne_of_gt (pow_pos hrp m)),
    Real.log_pow, Real.log_pow]
  dsimp only [δ] at hmul
  nlinarith

/-- The campaign endpoint includes arbitrary positive exponent loss, so the
exact logarithmic growth-rate ratio itself is attained in that sense. -/
theorem achieves_limit (c r g : ℕ)
    (hc : 1 < c) (hr : 1 < r) (hg : 1 < g)
    (hseed : ∀ m : ℕ, ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      sensitivity f ≤ c * r ^ m ∧ g ^ m ≤ blockSensitivityAt f (fun _ => false)) :
    SensitivityCampaign.AchievesExponent (Real.log (g : ℝ) / Real.log (r : ℝ)) := by
  let a := Real.log (g : ℝ) / Real.log (r : ℝ)
  have ha : 0 < a := div_pos (Real.log_pos (by exact_mod_cast hg))
    (Real.log_pos (by exact_mod_cast hr))
  intro ε hε S hS
  let β := max 0 (a - ε / 2)
  have hβ : 0 ≤ β := le_max_left _ _
  have hb : β < a := max_lt ha (by linarith)
  have hres := achieves_strict c r g β hc hr hg hβ hb hseed
  obtain ⟨n, f, hs, hp⟩ := hres (ε / 2) (by linarith) S hS
  refine ⟨n, f, hs, ?_⟩
  have hbase : (1 : ℝ) ≤ sensitivity f := by
    exact_mod_cast (show 1 ≤ sensitivity f by omega)
  have he : a - ε ≤ β - ε / 2 := by
    have hh := le_max_right 0 (a - ε / 2)
    dsimp only [β]
    linarith
  exact (Real.rpow_le_rpow_of_exponent_le hbase he).trans hp
end SensitivityPeriodicLog

theorem solution : SensitivityCampaign.AchievesExponent
    (Real.log (201838849 : ℝ) / Real.log (7922 : ℝ)) := by
  exact SensitivityPeriodicLog.achieves_limit
    32057676379612508934192581 7922 201838849
    (by decide) (by decide) (by decide)
    SensitivityCampaign.coupled_n15_periodic_seeds
#print axioms solution
