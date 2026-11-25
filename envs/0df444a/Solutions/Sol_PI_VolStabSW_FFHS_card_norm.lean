-- Prove2me | solution 1 for PI.VolStabSW.FFHS.card_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:14:46.697741+00:00
-- url     : https://prove2.me/submissions/259b1c89-c666-4f60-821b-88189e580727

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFHS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFCnt
import Theorems.Thm_PI_VolStabSW_FFHS_card_decomp
import Theorems.Thm_PI_VolStabSW_FFHS_IsSq_self_fixed
import Theorems.Thm_PI_VolStabSW_FFHS_IsSq_zero_left
import Theorems.Thm_PI_VolStabSW_FFHS_exists_aniso
import Theorems.Thm_PI_VolStabSW_FFHS_finrank_perp
import Theorems.Thm_PI_VolStabSW_FFHS_perp_isHS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.FFHS
open Module
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {σ : K →+* K}
namespace PI.VolStabSW.FFHS
theorem _root_.solution (q : ℕ) (hq0 : 0 < q) (hK : Fintype.card K = q ^ 2) (hσ : ∀ x, σ (σ x) = x)
    (h2 : (2 : K) ≠ 0)
    (hN : ∀ d, σ d = d → Nat.card {t : K // t * σ t = d} = if d = 0 then 1 else q + 1) :
    ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (h : V → V → K), IsHS σ h → finrank K V = m → ∀ c, σ c = c →
      (Nat.card {x : V // h x x = c} : ℝ) = (q : ℝ) ^ (2 * (m : ℤ) - 1) +
        (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1) * ((if c = 0 then (q : ℝ) else 0) - 1) := by
  intro m
  induction m with
  | zero =>
    intro V _ _ _ h hh hm c hc
    haveI : Subsingleton V := Module.finrank_zero_iff.1 hm
    have hr : (q:ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
    have hcard : Nat.card {x : V // h x x = c} = if c = 0 then 1 else 0 := by
      split_ifs with hc0
      · rw [Nat.card_eq_one_iff_exists]
        refine ⟨⟨0, by rw [hh.toIsSq.zero_left, hc0]⟩, fun y => Subtype.ext (Subsingleton.elim _ _)⟩
      · rw [Nat.card_eq_zero]
        left
        constructor
        intro x
        apply hc0
        rw [← x.2, Subsingleton.elim x.1 0, hh.toIsSq.zero_left]
    rw [hcard]
    split_ifs with hc0
    · push_cast
      field_simp
      ring
    · push_cast
      ring
  | succ m ih =>
    intro V _ _ _ h hh hm c hc
    haveI : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hm
    haveI : Finite V := Module.finite_of_finite K
    obtain ⟨x0, hx0⟩ := exists_ne (0 : V)
    obtain ⟨e, he⟩ := exists_aniso h2 hh x0 hx0
    have hdec := card_decomp hh.toIsSq e he c
    have haσ : σ (h e e) = h e e := hh.toIsSq.self_fixed e
    have hperp := perp_isHS hh e he
    have hfr : finrank K (perp hh.toIsSq e) = m := by
      have := finrank_perp hh.toIsSq e he
      omega
    have hterm : ∀ t : K, (Nat.card {w : perp hh.toIsSq e // h w w = c - σ t * t * h e e} : ℝ) =
        (q:ℝ) ^ (2 * (m:ℤ) - 1) + (-1) ^ m * (q:ℝ) ^ ((m:ℤ) - 1) *
          ((if c - σ t * t * h e e = 0 then (q:ℝ) else 0) - 1) := by
      intro t
      have hfix : σ (c - σ t * t * h e e) = c - σ t * t * h e e := by
        rw [map_sub, map_mul, map_mul, hσ, hc, haσ]
        ring
      exact ih (perp hh.toIsSq e) (fun w w' => h w w') hperp hfr _ hfix
    have hP : ∀ t : K, (c - σ t * t * h e e = 0) ↔ t * σ t = c / h e e := by
      intro t
      rw [sub_eq_zero, eq_div_iff he]
      exact ⟨fun h' => by rw [h']; ring, fun h' => by rw [← h']; ring⟩
    have hcnt : ((Finset.univ.filter (fun t : K => c - σ t * t * h e e = 0)).card : ℝ) =
        if c = 0 then 1 else (q:ℝ) + 1 := by
      have hfixd : σ (c / h e e) = c / h e e := by rw [map_div₀, hc, haσ]
      have h3 := hN (c / h e e) hfixd
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h3
      have h4 : (Finset.univ.filter (fun t : K => c - σ t * t * h e e = 0)) =
          Finset.univ.filter (fun t => t * σ t = c / h e e) := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hP t
      rw [h4, h3]
      have h5 : c / h e e = 0 ↔ c = 0 := div_eq_zero_iff.trans (or_iff_left he)
      by_cases hc0 : c = 0
      · simp [hc0]
      · simp [hc0, h5]
    have hsum : ∑ t : K, ((q:ℝ) ^ (2 * (m:ℤ) - 1) + (-1) ^ m * (q:ℝ) ^ ((m:ℤ) - 1) *
          ((if c - σ t * t * h e e = 0 then (q:ℝ) else 0) - 1)) =
        (q:ℝ) * (q:ℝ) * ((q:ℝ) ^ (2 * (m:ℤ) - 1) - (-1) ^ m * (q:ℝ) ^ ((m:ℤ) - 1)) +
          (-1) ^ m * (q:ℝ) ^ ((m:ℤ) - 1) * (q:ℝ) *
            (Finset.univ.filter (fun t : K => c - σ t * t * h e e = 0)).card := by
      have e1 : ∀ t : K, ((q:ℝ) ^ (2 * (m:ℤ) - 1) + (-1) ^ m * (q:ℝ) ^ ((m:ℤ) - 1) *
          ((if c - σ t * t * h e e = 0 then (q:ℝ) else 0) - 1)) =
          ((q:ℝ) ^ (2 * (m:ℤ) - 1) - (-1) ^ m * (q:ℝ) ^ ((m:ℤ) - 1)) +
            (-1) ^ m * (q:ℝ) ^ ((m:ℤ) - 1) * (if c - σ t * t * h e e = 0 then (q:ℝ) else 0) :=
        fun t => by ring
      rw [Finset.sum_congr rfl (fun t _ => e1 t), Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, hK, ← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero,
        Finset.sum_const]
      simp only [nsmul_eq_mul]
      push_cast
      ring
    rw [hdec, Nat.cast_sum, Finset.sum_congr rfl (fun t _ => hterm t), hsum, hcnt]
    have hr : (q:ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
    have e2 : (q:ℝ) ^ (2 * ((m + 1 : ℕ) : ℤ) - 1) = (q:ℝ) * (q:ℝ) * (q:ℝ) ^ (2 * (m:ℤ) - 1) := by
      rw [show (2 * ((m + 1 : ℕ) : ℤ) - 1) = 1 + 1 + (2 * (m:ℤ) - 1) by push_cast; ring,
        zpow_add₀ hr, zpow_add₀ hr, zpow_one]
    have e3 : (q:ℝ) ^ (((m + 1 : ℕ) : ℤ) - 1) = (q:ℝ) * (q:ℝ) ^ ((m:ℤ) - 1) := by
      rw [show (((m + 1 : ℕ) : ℤ) - 1) = 1 + ((m:ℤ) - 1) by push_cast; ring, zpow_add₀ hr, zpow_one]
    rw [e2, e3, pow_succ]
    split_ifs <;> ring
end PI.VolStabSW.FFHS
