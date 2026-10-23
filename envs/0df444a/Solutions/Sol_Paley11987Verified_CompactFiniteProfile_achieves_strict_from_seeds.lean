-- Prove2me | solution 1 for Paley11987Verified.CompactFiniteProfile.achieves_strict_from_seeds
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-23T05:16:19.527968+00:00
-- url     : https://prove2.me/submissions/b04cd290-40bc-4809-a2e0-ffb0e70acd04

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Paley11987Support_036
import Definitions.Def_Paley11987Support_055

set_option autoImplicit false
set_option Elab.async false
section z82

namespace CompactFiniteProfile
open OAI.Paper320

theorem _root_.solution (c r g t : ℕ) (β : ℝ)
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



end CompactFiniteProfile
end z82
