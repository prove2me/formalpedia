-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_count_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:46:40.673541+00:00
-- url     : https://prove2.me/submissions/584bb5bf-9ff2-4281-9828-37cb567c34b9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_count
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_sep_diff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open Matrix Topology Filter
open scoped Matrix ComplexOrder ENNReal
noncomputable section
variable {p q : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
theorem _root_.solution {f : ℕ} {ι : Type*} (x : ι → Fin f → Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
    (hU : ∀ a k, IsUpq (x a k)) {c : ℝ} (hc : 0 < c)
    (hsep : ∀ a b, a ≠ b → ∃ k i j,
      c ≤ ‖(x b k * (x a k)⁻¹) i j - (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖)
    {R : ℝ} (hR : 1 ≤ R) :
    (({a | ∀ k i j, ‖x a k i j‖ ≤ R} : Set ι).encard : ℝ≥0∞) ≤
      ENNReal.ofReal (((4 * (((p + q : ℕ) : ℝ) + 1) / c + 3) * R ^ 2) ^ (f * ((p + q) * ((p + q) * 2)))) := by
  have hpq : (0 : ℝ) < ((p + q : ℕ) : ℝ) + 1 := by positivity
  have hR0 : (0 : ℝ) < R := by linarith
  set η : ℝ := c / (((p + q : ℕ) : ℝ) + 1) / R / 2 with hη_def
  have hη : 0 < η := by positivity
  have hsep2 : ∀ a, (∀ k i j, ‖x a k i j‖ ≤ R) → ∀ b, (∀ k i j, ‖x b k i j‖ ≤ R) → a ≠ b →
      ∃ k i j, 2 * η ≤ ‖x b k i j - x a k i j‖ := by
    intro a ha b _ hab
    obtain ⟨k, i, j, hk⟩ := hsep a b hab
    obtain ⟨l, hl⟩ := sumBd_sep_diff (hU a k) hR0 hc (ha k) hk
    refine ⟨k, i, l, ?_⟩
    have h2η : 2 * η = c / (((p + q : ℕ) : ℝ) + 1) / R := by rw [hη_def]; ring
    rw [h2η]
    exact hl
  have hE : Fintype.card (Fin f × (Fin p ⊕ Fin q) × (Fin p ⊕ Fin q) × Bool) = f * ((p + q) * ((p + q) * 2)) := by
    simp [Fintype.card_prod, Fintype.card_sum]
  have hcount := sumBd_count x hη hsep2
  rw [Fintype.card_piFinset, Finset.prod_const, Int.card_Icc, Finset.card_univ, hE] at hcount
  have hm0 : (0 : ℤ) ≤ ⌈R / η⌉ := Int.ceil_nonneg (by positivity)
  have hbase : (((⌈R / η⌉ + 1 - -⌈R / η⌉).toNat : ℕ) : ℝ) ≤ (4 * (((p + q : ℕ) : ℝ) + 1) / c + 3) * R ^ 2 := by
    have h1 : (((⌈R / η⌉ + 1 - -⌈R / η⌉).toNat : ℕ) : ℝ) = 2 * (⌈R / η⌉ : ℝ) + 1 := by
      have h0 : (((⌈R / η⌉ + 1 - -⌈R / η⌉).toNat : ℕ) : ℤ) = ⌈R / η⌉ + 1 - -⌈R / η⌉ :=
        Int.toNat_of_nonneg (by omega)
      have h0' : (((⌈R / η⌉ + 1 - -⌈R / η⌉).toNat : ℕ) : ℝ) = ((⌈R / η⌉ + 1 - -⌈R / η⌉ : ℤ) : ℝ) := by
        exact_mod_cast h0
      rw [h0']
      push_cast
      ring
    have h2 : (⌈R / η⌉ : ℝ) < R / η + 1 := Int.ceil_lt_add_one _
    have h3 : R / η = 2 * (((p + q : ℕ) : ℝ) + 1) * R ^ 2 / c := by
      rw [hη_def]
      field_simp
    have hR2 : 1 ≤ R ^ 2 := by nlinarith
    have h5 : (4 * (((p + q : ℕ) : ℝ) + 1) / c + 3) * R ^ 2 = 2 * (R / η) + 3 * R ^ 2 := by
      rw [h3]
      ring
    rw [h1, h5]
    linarith
  calc ((({a | ∀ k i j, ‖x a k i j‖ ≤ R} : Set ι).encard : ℝ≥0∞))
      ≤ ((((⌈R / η⌉ + 1 - -⌈R / η⌉).toNat ^ (f * ((p + q) * ((p + q) * 2))) : ℕ) : ℕ∞) : ℝ≥0∞) :=
        ENat.toENNReal_le.2 hcount
    _ = ENNReal.ofReal ((((⌈R / η⌉ + 1 - -⌈R / η⌉).toNat : ℕ) : ℝ) ^ (f * ((p + q) * ((p + q) * 2)))) := by
        rw [ENat.toENNReal_coe, ← Nat.cast_pow, ENNReal.ofReal_natCast]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (Nat.cast_nonneg _) hbase _)
end ReciprocityTheory.ChartRestriction.G.AR.Up
