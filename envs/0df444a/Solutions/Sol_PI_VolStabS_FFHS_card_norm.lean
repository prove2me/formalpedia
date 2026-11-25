-- Prove2me | solution 1 for PI.VolStabS.FFHS.card_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:09:13.644977+00:00
-- url     : https://prove2.me/submissions/35c7d7e3-c59a-4dd7-bce6-f3e68ba287ad

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFHS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFCnt
import Theorems.Thm_PI_VolStabS_FFHS_card_decomp
import Theorems.Thm_PI_VolStabS_FFHS_IsSq_self_fixed
import Theorems.Thm_PI_VolStabS_FFHS_IsSq_zero_left
import Theorems.Thm_PI_VolStabS_FFHS_exists_aniso
import Theorems.Thm_PI_VolStabS_FFHS_finrank_perp
import Theorems.Thm_PI_VolStabS_FFHS_perp_isHS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.VolStabS.FFHS
open Module
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {σ : K →+* K}
private theorem natCard_subtype_eq_card_filter {α : Type} [Fintype α] (p : α → Prop)
    [DecidablePred p] : Nat.card {x // p x} = (Finset.univ.filter p).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
end PI.VolStabS.FFHS
end
end

set_option autoImplicit false
noncomputable section
open PI PI.VolStabS PI.VolStabS.FFHS
open Module
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {σ : K →+* K}
namespace PI.VolStabS.FFHS
theorem _root_.solution (q : ℕ) (hq0 : 0 < q) (hK : Fintype.card K = q ^ 2) (hσ : ∀ x, σ (σ x) = x)
    (h2 : (2 : K) ≠ 0)
    (hN : ∀ d, σ d = d → Nat.card {t : K // t * σ t = d} = if d = 0 then 1 else q + 1) :
    ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (h : V → V → K), IsHS σ h → finrank K V = m → ∀ c, σ c = c →
      (Nat.card {x : V // h x x = c} : ℝ) = (q : ℝ) ^ (2 * (m : ℤ) - 1) +
        (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1) * ((if c = 0 then (q : ℝ) else 0) - 1) := by
  have hQ : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hq0.ne'
  have z1 : ∀ n : ℕ, (q : ℝ) ^ (2 * (n : ℤ) - 1) = (q : ℝ) ^ (2 * n) * (q : ℝ)⁻¹ := by
    intro n
    rw [zpow_sub₀ hQ, zpow_one, div_eq_mul_inv,
      show (2 * (n : ℤ)) = ((2 * n : ℕ) : ℤ) by omega, zpow_natCast]
  have z2 : ∀ n : ℕ, (q : ℝ) ^ ((n : ℤ) - 1) = (q : ℝ) ^ n * (q : ℝ)⁻¹ := by
    intro n
    rw [zpow_sub₀ hQ, zpow_one, div_eq_mul_inv, zpow_natCast]
  intro m
  induction m with
  | zero =>
    intro V i1 i2 i3 h hh hm c hc
    have : Subsingleton V := by
      rcases subsingleton_or_nontrivial V with hV | hV
      · exact hV
      · exfalso
        have hpos : 0 < finrank K V := Module.finrank_pos
        omega
    have h00 : h 0 0 = 0 := hh.toIsSq.zero_left 0
    simp only [z1, z2]
    by_cases hc0 : c = 0
    · subst hc0
      have hcard : Nat.card {x : V // h x x = 0} = 1 := by
        have : Unique {x : V // h x x = 0} :=
          ⟨⟨⟨0, h00⟩⟩, fun y => Subtype.ext (Subsingleton.elim _ _)⟩
        exact Nat.card_unique
      rw [hcard, if_pos rfl, Nat.cast_one]
      have hqq : (q : ℝ) * (q : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hQ
      linear_combination -hqq
    · have hcard : Nat.card {x : V // h x x = c} = 0 := by
        have : IsEmpty {x : V // h x x = c} :=
          ⟨fun y => hc0 (by
            have hy := y.2
            rw [Subsingleton.elim y.1 0, h00] at hy
            exact hy.symm)⟩
        exact Nat.card_of_isEmpty
      rw [hcard, if_neg hc0, Nat.cast_zero]
      ring
  | succ m ih =>
    intro V i1 i2 i3 h hh hm c hc
    have hs := hh.toIsSq
    haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    obtain ⟨e, he⟩ := exists_aniso h2 hh x hx
    have hW := perp_isHS hh e he
    have hWr : finrank K (perp hs e) = m := by
      have := finrank_perp hs e he
      omega
    have : Finite V := Module.finite_of_finite K
    have hterm : ∀ t : K, (Nat.card {w : perp hs e // h w w = c - σ t * t * h e e} : ℝ) =
        (q : ℝ) ^ (2 * (m : ℤ) - 1) + (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1) *
          ((if c - σ t * t * h e e = 0 then (q : ℝ) else 0) - 1) := by
      intro t
      refine ih (perp hs e) (fun w w' : perp hs e => h w w') hW hWr _ ?_
      simp only [map_sub, map_mul, hσ, hc, hs.self_fixed]
      ring
    have hfix : σ (c * (h e e)⁻¹) = c * (h e e)⁻¹ := by
      rw [map_mul, map_inv₀, hc, hs.self_fixed]
    have hiff : ∀ t : K, c - σ t * t * h e e = 0 ↔ t * σ t = c * (h e e)⁻¹ := by
      intro t
      constructor
      · intro H
        have H' : σ t * t * h e e = c := (sub_eq_zero.1 H).symm
        rw [← H', mul_inv_cancel_right₀ he, mul_comm]
      · intro H
        rw [mul_comm (σ t) t, H, mul_assoc, inv_mul_cancel₀ he, mul_one, sub_self]
    have hcount : ((Finset.univ.filter (fun t : K => c - σ t * t * h e e = 0)).card : ℝ) =
        if c = 0 then 1 else (q : ℝ) + 1 := by
      rw [← natCard_subtype_eq_card_filter, Nat.card_congr (Equiv.subtypeEquivRight hiff),
        hN _ hfix]
      by_cases hc0 : c = 0
      · simp [hc0]
      · simp [hc0, he]
    have hsum : ∑ t : K, ((q : ℝ) ^ (2 * (m : ℤ) - 1) + (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1) *
          ((if c - σ t * t * h e e = 0 then (q : ℝ) else 0) - 1)) =
        (q : ℝ) ^ 2 * ((q : ℝ) ^ (2 * (m : ℤ) - 1) - (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1)) +
          (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1) * (q : ℝ) *
            ((Finset.univ.filter (fun t : K => c - σ t * t * h e e = 0)).card : ℝ) := by
      have hpt : ∀ t : K, ((q : ℝ) ^ (2 * (m : ℤ) - 1) + (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1) *
          ((if c - σ t * t * h e e = 0 then (q : ℝ) else 0) - 1)) =
          ((q : ℝ) ^ (2 * (m : ℤ) - 1) - (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1)) +
            (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1) * (q : ℝ) *
              (if c - σ t * t * h e e = 0 then (1 : ℝ) else 0) := by
        intro t
        split_ifs <;> ring
      rw [Finset.sum_congr rfl (fun t _ => hpt t), Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_boole, Finset.sum_const, Finset.card_univ, hK, nsmul_eq_mul, Nat.cast_pow]
    rw [card_decomp hs e he c, Nat.cast_sum, Finset.sum_congr rfl (fun t _ => hterm t),
      hsum, hcount]
    simp only [z1, z2]
    split_ifs <;> ring
end PI.VolStabS.FFHS
