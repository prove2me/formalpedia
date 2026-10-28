-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint.achieves_strict_from_seeds
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T18:25:39.030986+00:00
-- url     : https://prove2.me/submissions/dca388a7-4662-4c53-8bae-29404068c49b

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring


namespace Sensitivity213981Formal
section
/-
Conditional endpoint reductions for the three requested bounds.

This file does NOT prove the recursive seed construction. Its `hseed`
hypotheses are explicit, and none is asserted as an axiom or hidden import.
The logarithmic inequalities and asymptotic conversion are proved here.

The conversion proof adapts the accepted Apache-2.0 proof by @yousofy:
https://prove2.me/submissions/b04cd290-40bc-4809-a2e0-ffb0e70acd04
The shared definitions are the campaign's Definitions.Def_SensitivityCampaign
and Definitions.Def_SensitivitySeparation, with unchanged definition bodies.
-/


set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option Elab.async false

namespace ThreeBoundEndpoint
open OAI.Paper320











/-- A concrete Boolean seed family is sufficient for an asymptotic exponent.
    The seed family is a hypothesis, not proved by this lemma. -/
theorem achieves_strict_from_seeds (c r g t : ℕ) (β : ℝ)
    (hc : 1 <  c) (hr : 1 <  r) (hg : 1 <  g) (ht : 1 <  t)
    (hβ : 0 ≤  β)
    (hstrict : β <  Real.log (g : ℝ) / Real.log (r : ℝ))
    (hseed : ∀ m : ℕ, ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      t^m ≤  sensitivity f ∧ sensitivity f ≤  c*r^m ∧ g^m ≤  blockSensitivity f) :
    SensitivityCampaign.AchievesExponent β := by
  have hcp : (0 : ℝ) <  c := by exact_mod_cast (by omega : 0 <  c)
  have hr1 : (1 : ℝ) <  r := by exact_mod_cast hr
  have hrp : (0 : ℝ) <  r := by linarith
  have hgp : (0 : ℝ) <  g := by exact_mod_cast (by omega : 0 <  g)
  have hlr : 0 <  Real.log (r : ℝ) := Real.log_pos hr1
  let δ := Real.log (g : ℝ) - β * Real.log (r : ℝ)
  have hgap : 0 <  δ := by
    have hh := (lt_div_iff₀ hlr).mp hstrict
    dsimp only [δ]
    linarith
  intro ε hε S hS
  obtain ⟨m, hm⟩ := exists_nat_gt (max (S : ℝ) (β * Real.log (c : ℝ) / δ))
  have hmS : S <  m := by exact_mod_cast ((le_max_left _ _).trans_lt hm)
  have hmul : β * Real.log (c : ℝ) <  (m : ℝ) * δ :=
    (div_lt_iff₀ hgap).mp ((le_max_right _ _).trans_lt hm)
  obtain ⟨n, f, hlower, hs, hb⟩ := hseed m
  have hSle : S ≤  sensitivity f :=
    (Nat.le_of_lt hmS).trans ((Nat.le_of_lt (Nat.lt_pow_self ht)).trans hlower)
  refine ⟨n, f, hSle, ?_⟩
  have hbase : (1 : ℝ) ≤  sensitivity f := by
    exact_mod_cast (show 1 ≤  sensitivity f by omega)
  have hApos : (0 : ℝ) <  (c*r^m : ℕ) := by
    exact_mod_cast (Nat.mul_pos (by omega : 0 <  c) (Nat.pow_pos (by omega : 0 <  r)))
  have hBpos : (0 : ℝ) <  (g^m : ℕ) := by
    exact_mod_cast (Nat.pow_pos (by omega : 0 <  g) : 0 <  g^m)
  have hpow : ((c*r^m : ℕ) : ℝ)^β ≤  ((g^m : ℕ) : ℝ) := by
    apply (Real.rpow_le_iff_le_log hApos hBpos).2
    push_cast
    rw [Real.log_mul (ne_of_gt hcp) (ne_of_gt (pow_pos hrp m)),
      Real.log_pow, Real.log_pow]
    dsimp only [δ] at hmul
    nlinarith
  calc
    (sensitivity f : ℝ)^(β-ε) ≤  (sensitivity f : ℝ)^β :=
      Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
    _ ≤  ((c*r^m : ℕ) : ℝ)^β :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hs) hβ
    _ ≤  ((g^m : ℕ) : ℝ) := hpow
    _ ≤  (blockSensitivity f : ℝ) := by exact_mod_cast hb









end ThreeBoundEndpoint










end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ (c r g t : Nat) (β : Real)
  (hc : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) c)
  (hr : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) r)
  (hg : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) g)
  (ht : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) t)
  (hβ : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) β)
  (hstrict :
    @LT.lt.{0} Real Real.instLT β
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (Real.log (@Nat.cast.{0} Real Real.instNatCast g)) (Real.log (@Nat.cast.{0} Real Real.instNatCast r))))
  (hseed :
    ∀ (m : Nat),
      @Exists.{1} Nat fun (n : Nat) =>
        @Exists.{1} ((Fin n → Bool) → Bool) fun (f : (Fin n → Bool) → Bool) =>
          And
            (@LE.le.{0} Nat instLENat
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) t m)
              (@OAI.Paper320.sensitivity (Fin n) (Fin.fintype n) f))
            (And
              (@LE.le.{0} Nat instLENat (@OAI.Paper320.sensitivity (Fin n) (Fin.fintype n) f)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) c
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) r m)))
              (@LE.le.{0} Nat instLENat
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) g m)
                (@OAI.Paper320.blockSensitivity (Fin n) (Fin.fintype n) f)))),
  SensitivityCampaign.AchievesExponent β := @Sensitivity213981Formal.ThreeBoundEndpoint.achieves_strict_from_seeds
