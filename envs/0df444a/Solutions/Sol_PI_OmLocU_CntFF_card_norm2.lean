-- Prove2me | solution 1 for PI.OmLocU.CntFF.card_norm2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:18:34.7322+00:00
-- url     : https://prove2.me/submissions/207751bf-477d-4dc1-bea7-3d8e31e36657

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFIn
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnitaryOrbits_FFInert2Holds
import Theorems.Thm_PI_OmLocU_CntFF_exists_aniso2
import Theorems.Thm_PI_VolStabSW_FFHS_card_decomp
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
open PI PI.OmLocU PI.OmLocU.CntFF
open Module PI.VolStabSW PI.VolStabSW.FFHS
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {σ : K →+* K}
namespace PI.OmLocU.CntFF
theorem _root_.solution (q : ℕ) (hq0 : 0 < q) (hK : Fintype.card K = q ^ 2) (hσ : ∀ x, σ (σ x) = x)
    (h2 : ∃ z : K, z + σ z ≠ 0)
    (hN : ∀ d, σ d = d → Nat.card {t : K // t * σ t = d} = if d = 0 then 1 else q + 1) :
    ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (h : V → V → K), IsHS σ h → finrank K V = m → ∀ c, σ c = c →
      (Nat.card {x : V // h x x = c} : ℝ) = (q : ℝ) ^ (2 * (m : ℤ) - 1) +
        (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1) * ((if c = 0 then (q : ℝ) else 0) - 1) := by
  intro m
  induction m with
  | zero =>
    intro V _ _ _ h hs hm c hc
    have hV : ∀ x : V, x = 0 := finrank_zero_iff_forall_zero.mp hm
    have h00 : h 0 0 = 0 := by
      have h0 := hs.smul_right 0 0 0
      rwa [zero_smul, zero_mul] at h0
    have hq : (q : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
    by_cases hc0 : c = 0
    · have h1 : Nat.card {x : V // h x x = c} = 1 :=
        Nat.card_eq_one_iff_exists.mpr ⟨⟨0, by rw [h00, hc0]⟩, fun y => Subtype.ext (hV y.1)⟩
      rw [h1, if_pos hc0]
      simp only [Nat.cast_zero, mul_zero, zero_sub, zpow_neg_one, pow_zero, one_mul, Nat.cast_one]
      field_simp
      try ring
    · haveI : IsEmpty {x : V // h x x = c} :=
        ⟨fun y => hc0 (by rw [← y.2, hV y.1, h00])⟩
      rw [Nat.card_of_isEmpty, if_neg hc0]
      simp only [Nat.cast_zero, mul_zero, zero_sub, zpow_neg_one, pow_zero, one_mul]
      ring
  | succ m ih =>
    intro V _ _ _ h hs hm c hc
    haveI : Finite V := Module.finite_of_finite K
    have hpos : 0 < finrank K V := by omega
    obtain ⟨x, hx⟩ : ∃ x : V, x ≠ 0 := finrank_pos_iff_exists_ne_zero.mp hpos
    obtain ⟨e, he⟩ := exists_aniso2 h2 hs x hx
    have hσa : σ (h e e) = h e e := (hs.herm e e).symm
    have hW : finrank K (perp hs.toIsSq e) = m := by
      have := finrank_perp hs.toIsSq e he
      omega
    have hfib : ∀ t : K, (Nat.card {w : perp hs.toIsSq e // h w w = c - σ t * t * h e e} : ℝ) =
        (q : ℝ) ^ (2 * (m : ℤ) - 1) + (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1) *
          ((if c - σ t * t * h e e = 0 then (q : ℝ) else 0) - 1) := fun t =>
      ih (perp hs.toIsSq e) (fun w w' => h w w') (perp_isHS hs e he) hW _
        (by rw [map_sub, map_mul, map_mul, hσ, hσa, hc]; ring)
    have hq : (q : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
    have hsum : ∑ t : K, ((q : ℝ) ^ (2 * (m : ℤ) - 1) + (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1) *
          ((if c - σ t * t * h e e = 0 then (q : ℝ) else 0) - 1)) =
        (Fintype.card K : ℝ) * ((q : ℝ) ^ (2 * (m : ℤ) - 1) - (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1)) +
          (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1) * q *
            ((Finset.univ.filter (fun t : K => c - σ t * t * h e e = 0)).card : ℝ) := by
      rw [Finset.card_filter]
      push_cast
      rw [Finset.mul_sum, show (Fintype.card K : ℝ) *
          ((q : ℝ) ^ (2 * (m : ℤ) - 1) - (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1)) =
          ∑ _t : K, ((q : ℝ) ^ (2 * (m : ℤ) - 1) - (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1)) by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul], ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      split_ifs <;> ring
    have hN0 : ((Finset.univ.filter (fun t : K => c - σ t * t * h e e = 0)).card : ℝ) =
        if c = 0 then 1 else (q : ℝ) + 1 := by
      have e1 : Finset.univ.filter (fun t : K => c - σ t * t * h e e = 0) =
          Finset.univ.filter (fun t : K => t * σ t = c * (h e e)⁻¹) := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h0
          rw [eq_mul_inv_iff_mul_eq₀ he]
          linear_combination -h0
        · intro h0
          rw [eq_mul_inv_iff_mul_eq₀ he] at h0
          linear_combination -h0
      rw [e1, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
        hN _ (by rw [map_mul, map_inv₀, hc, hσa])]
      by_cases hc0 : c = 0 <;> simp [hc0, he]
    have hKr : (Fintype.card K : ℝ) = (q : ℝ) ^ 2 := by rw [hK]; push_cast; ring
    have e2 : (2 * ((m + 1 : ℕ) : ℤ) - 1) = (2 * (m : ℤ) - 1) + 2 := by push_cast; ring
    have e3 : (((m + 1 : ℕ) : ℤ) - 1) = ((m : ℤ) - 1) + 1 := by push_cast; ring
    rw [card_decomp hs.toIsSq e he c, Nat.cast_sum]
    simp_rw [hfib]
    rw [hsum, hN0, hKr, e2, e3, zpow_add₀ hq, zpow_add₀ hq, zpow_two, zpow_one]
    by_cases hc0 : c = 0
    · rw [if_pos hc0, if_pos hc0]
      ring
    · rw [if_neg hc0, if_neg hc0]
      ring
end PI.OmLocU.CntFF
