-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.ValUFD.factor_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:38:04.136961+00:00
-- url     : https://prove2.me/submissions/7b73c909-4d50-4f99-8a96-57480baecc0b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValUFD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValUFD_height_span_prime
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValUFD_gen_prime
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValUFD_mult_prime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.ValUFD
variable {R F : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [Field F]
  [Algebra R F] [IsFractionRing R F]
variable {gen : Ideal R → R}
namespace ReciprocityTheory.ChartRestriction.G.T0.ValUFD
theorem _root_.solution (hgen : ∀ p : Ideal R, p.IsPrime → p.height = 1 → p = Ideal.span {gen p})
    (r : R) (hr : r ≠ 0) :
    ({p : Ideal R | p.IsPrime ∧ p.height = 1} ∩ {p | multiplicity (gen p) r ≠ 0}).Finite ∧
      ∃ κ : R, IsUnit κ ∧ algebraMap R F r = algebraMap R F κ *
        ∏ᶠ (p : Ideal R) (_ : p ∈ {p : Ideal R | p.IsPrime ∧ p.height = 1}),
          algebraMap R F (gen p) ^ (multiplicity (gen p) r : ℤ) := by
  classical
  set H := {p : Ideal R | p.IsPrime ∧ p.height = 1} with hH
  revert hr
  refine UniqueFactorizationMonoid.induction_on_prime (P := fun r : R => r ≠ 0 →
    (H ∩ {p | multiplicity (gen p) r ≠ 0}).Finite ∧
      ∃ κ : R, IsUnit κ ∧ algebraMap R F r = algebraMap R F κ *
        ∏ᶠ (p : Ideal R) (_ : p ∈ H), algebraMap R F (gen p) ^ (multiplicity (gen p) r : ℤ))
    r ?_ ?_ ?_
  · intro h; exact absurd rfl h
  · intro x hx _
    have h0 : ∀ p ∈ H, multiplicity (gen p) x = 0 := fun p hp =>
      multiplicity_of_isUnit_right (gen_prime hgen hp).not_isUnit hx
    refine ⟨Set.finite_empty.subset fun p ⟨hp, hs⟩ => hs (h0 p hp), x, hx, ?_⟩
    rw [finprod_mem_of_eqOn_one (fun p hp => by simp [h0 p hp]), mul_one]
  · intro a q ha hq ih _
    obtain ⟨hfin, κ, hκ, heq⟩ := ih ha
    set p₀ := Ideal.span {q} with hp₀def
    have hp₀ : p₀ ∈ H :=
      ⟨(Ideal.span_singleton_prime hq.ne_zero).mpr hq, height_span_prime hq⟩
    have hmul : ∀ p ∈ H, multiplicity (gen p) (q * a) =
        (if p = p₀ then 1 else 0) + multiplicity (gen p) a := by
      intro p hp
      rw [multiplicity_mul (gen_prime hgen hp) (FiniteMultiplicity.of_prime_left (gen_prime hgen hp)
        (mul_ne_zero hq.ne_zero ha)), mult_prime hgen hp hq]
    have hGne : ∀ p ∈ H, algebraMap R F (gen p) ≠ 0 := fun p hp => by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective R F)]; exact (gen_prime hgen hp).ne_zero
    have hsplit : ∀ p ∈ H, algebraMap R F (gen p) ^ (multiplicity (gen p) (q * a) : ℤ) =
        (if p = p₀ then algebraMap R F (gen p₀) else 1) *
          algebraMap R F (gen p) ^ (multiplicity (gen p) a : ℤ) := by
      intro p hp
      rw [hmul p hp, Nat.cast_add, zpow_add₀ (hGne p hp)]
      split_ifs with h
      · rw [h, Nat.cast_one, zpow_one]
      · rw [Nat.cast_zero, zpow_zero]
    have hfin1 : (H ∩ Function.mulSupport
        (fun p => if p = p₀ then algebraMap R F (gen p₀) else 1)).Finite :=
      (Set.finite_singleton p₀).subset fun p ⟨_, hs⟩ => by
        by_contra h; exact hs (if_neg h)
    have hfin2 : (H ∩ Function.mulSupport
        (fun p => algebraMap R F (gen p) ^ (multiplicity (gen p) a : ℤ))).Finite :=
      hfin.subset fun p ⟨hp, hs⟩ => ⟨hp, fun h0 => hs (by simp only [h0]; simp)⟩
    have hsingle : ∏ᶠ (p : Ideal R) (_ : p ∈ H),
        (if p = p₀ then algebraMap R F (gen p₀) else 1) = algebraMap R F (gen p₀) := by
      rw [finprod_eq_single _ p₀ (fun p hp => by simp [hp]), finprod_eq_if, if_pos hp₀, if_pos rfl]
    have hprod : ∏ᶠ (p : Ideal R) (_ : p ∈ H),
        algebraMap R F (gen p) ^ (multiplicity (gen p) (q * a) : ℤ) =
        algebraMap R F (gen p₀) * ∏ᶠ (p : Ideal R) (_ : p ∈ H),
          algebraMap R F (gen p) ^ (multiplicity (gen p) a : ℤ) := by
      rw [finprod_mem_congr rfl hsplit, finprod_mem_mul_distrib' hfin1 hfin2, hsingle]
    refine ⟨((Set.finite_singleton p₀).union hfin).subset ?_, ?_⟩
    · rintro p ⟨hp, hs⟩
      by_cases h : p = p₀
      · exact Or.inl h
      · refine Or.inr ⟨hp, ?_⟩
        have := hmul p hp
        rw [if_neg h, zero_add] at this
        rw [Set.mem_ofPred_eq, ← this]; exact hs
    · have hass : Associated q (gen p₀) := by
        rw [← Ideal.span_singleton_eq_span_singleton]; exact hgen p₀ hp₀.1 hp₀.2
      obtain ⟨u, hu⟩ := hass
      refine ⟨↑u⁻¹ * κ, (Units.isUnit _).mul hκ, ?_⟩
      rw [hprod, ← hu, map_mul, heq, map_mul, map_mul]
      have hu1 : algebraMap R F ↑u⁻¹ * algebraMap R F ↑u = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      linear_combination (-(algebraMap R F q * algebraMap R F κ *
        ∏ᶠ (p : Ideal R) (_ : p ∈ H), algebraMap R F (gen p) ^ (multiplicity (gen p) a : ℤ))) * hu1
end ReciprocityTheory.ChartRestriction.G.T0.ValUFD
