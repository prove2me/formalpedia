-- Prove2me | solution 1 for ThreeBoundEndpoint.achieves_strict_from_seeds
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:37:50.364976+00:00
-- url     : https://prove2.me/submissions/31205d68-617e-448d-ae4c-6f69b4778a75

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

namespace OAI.Paper320
end OAI.Paper320
section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option Elab.async false
namespace ThreeBoundEndpoint
end ThreeBoundEndpoint
open ThreeBoundEndpoint
open OAI.Paper320

/-- A concrete Boolean seed family is sufficient for an asymptotic exponent.
    The seed family is a hypothesis, not proved by this lemma. -/
theorem solution (c r g t : ℕ) (β : ℝ)
    (hc : 1 < c) (hr : 1 < r) (hg : 1 < g) (ht : 1 < t)
    (hβ : 0 ≤ β)
    (hstrict : β < Real.log (g : ℝ) / Real.log (r : ℝ))
    (hseed : ∀ m : ℕ, ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      t^m ≤ sensitivity f ∧ sensitivity f ≤ c*r^m ∧ g^m ≤ blockSensitivity f) :
    SensitivityCampaign.AchievesExponent β := by
  have hcp : (0 : ℝ) < c := by exact_mod_cast (by omega : 0 < c)
  have hr1 : (1 : ℝ) < r := by exact_mod_cast hr
  have hrp : (0 : ℝ) < r := by linarith
  have hgp : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have hlr : 0 < Real.log (r : ℝ) := Real.log_pos hr1
  let δ := Real.log (g : ℝ) - β * Real.log (r : ℝ)
  have hgap : 0 < δ := by
    have hh := (lt_div_iff₀ hlr).mp hstrict
    dsimp only [δ]
    linarith
  intro ε hε S hS
  obtain ⟨m, hm⟩ := exists_nat_gt (max (S : ℝ) (β * Real.log (c : ℝ) / δ))
  have hmS : S < m := by exact_mod_cast ((le_max_left _ _).trans_lt hm)
  have hmul : β * Real.log (c : ℝ) < (m : ℝ) * δ :=
    (div_lt_iff₀ hgap).mp ((le_max_right _ _).trans_lt hm)
  obtain ⟨n, f, hlower, hs, hb⟩ := hseed m
  have hSle : S ≤ sensitivity f :=
    (Nat.le_of_lt hmS).trans ((Nat.le_of_lt (Nat.lt_pow_self ht)).trans hlower)
  refine ⟨n, f, hSle, ?_⟩
  have hbase : (1 : ℝ) ≤ sensitivity f := by
    exact_mod_cast (show 1 ≤ sensitivity f by omega)
  have hApos : (0 : ℝ) < (c*r^m : ℕ) := by
    exact_mod_cast (Nat.mul_pos (by omega : 0 < c) (Nat.pow_pos (by omega : 0 < r)))
  have hBpos : (0 : ℝ) < (g^m : ℕ) := by
    exact_mod_cast (Nat.pow_pos (by omega : 0 < g) : 0 < g^m)
  have hpow : ((c*r^m : ℕ) : ℝ)^β ≤ ((g^m : ℕ) : ℝ) := by
    apply (Real.rpow_le_iff_le_log hApos hBpos).2
    push_cast
    rw [Real.log_mul (ne_of_gt hcp) (ne_of_gt (pow_pos hrp m)),
      Real.log_pow, Real.log_pow]
    dsimp only [δ] at hmul
    nlinarith
  calc
    (sensitivity f : ℝ)^(β-ε) ≤ (sensitivity f : ℝ)^β :=
      Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
    _ ≤ ((c*r^m : ℕ) : ℝ)^β :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hs) hβ
    _ ≤ ((g^m : ℕ) : ℝ) := hpow
    _ ≤ (blockSensitivity f : ℝ) := by exact_mod_cast hb
end
