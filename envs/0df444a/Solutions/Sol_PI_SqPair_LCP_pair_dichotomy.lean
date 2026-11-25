-- Prove2me | solution 1 for PI.SqPair.LCP.pair_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:26:33.052852+00:00
-- url     : https://prove2.me/submissions/e284c2db-0516-4b37-81b2-87161e03d186

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PiNonunit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PairDichotomy

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.SqPair PI.SqPair.LCP
open Polynomial IsLocalRing
namespace PI.SqPair.LCP
theorem _root_.solution : Dichotomy := by
  intro R _ _ R₀ hfix _ _ _ _ hunr ϖ hϖ
  obtain ⟨θ, hθ⟩ := hunr
  have hst : ∀ r : R₀, star (r : R) = r := fun r => (hfix _).mp r.2
  have unit_of : ∀ {M : Type} [CommMonoid M] (a b : M), a * b = 1 → IsUnit a :=
    fun a b h => ⟨⟨a, b, h, (mul_comm b a).trans h⟩, rfl⟩
  obtain ⟨Di, hDi⟩ : ∃ Di : R, (θ - star θ) * Di = 1 := hθ.exists_right_inv
  have hDis : star Di = -Di := by
    have h2 := congrArg star hDi
    simp only [star_mul', star_sub, star_star, star_one] at h2
    linear_combination (-star Di) * hDi + (-Di) * h2
  have coord : ∀ x : R, ∃ a b : R₀, x = a + b * θ := by
    intro x
    have hb : (x - star x) * Di ∈ R₀ := by
      rw [hfix]
      simp only [star_mul', star_sub, star_star, hDis]
      ring
    have ha : x - (x - star x) * Di * θ ∈ R₀ := by
      rw [hfix]
      simp only [star_mul', star_sub, star_star, hDis]
      linear_combination (x - star x) * hDi
    exact ⟨⟨_, ha⟩, ⟨_, hb⟩, by simp⟩
  have hT : θ + star θ ∈ R₀ := by rw [hfix, star_add, star_star, add_comm]
  have hN : θ * star θ ∈ R₀ := by rw [hfix, star_mul', star_star, mul_comm]
  obtain ⟨T, hTc⟩ : ∃ T : R₀, (T : R) = θ + star θ := ⟨⟨_, hT⟩, rfl⟩
  obtain ⟨Nn, hNc⟩ : ∃ Nn : R₀, (Nn : R) = θ * star θ := ⟨⟨_, hN⟩, rfl⟩
  obtain ⟨E, hEc⟩ : ∃ E : R₀, (E : R) = Di ^ 2 :=
    ⟨⟨Di ^ 2, by rw [hfix, star_pow, hDis, neg_sq]⟩, rfl⟩
  have h4 : ((4 : R₀) : R) = 4 := map_ofNat R₀.subtype 4
  have hd : IsUnit (T ^ 2 - 4 * Nn) :=
    unit_of _ E (Subtype.ext (by
      push_cast [hTc, hNc, hEc, h4]
      linear_combination (θ * Di - star θ * Di + 1) * hDi))
  by_cases hs : ∃ c : R₀, ¬ IsUnit (c ^ 2 + T * c + Nn)
  · left
    obtain ⟨c, hc⟩ := hs
    have hu : IsUnit (2 * c + T) := by
      by_contra hn
      have h1 : (2 * c + T) ^ 2 ∈ maximalIdeal R₀ :=
        Ideal.pow_mem_of_mem _ ((mem_maximalIdeal _).mpr hn) 2 two_pos
      have h2 : 4 * (c ^ 2 + T * c + Nn) ∈ maximalIdeal R₀ :=
        Ideal.mul_mem_left _ _ ((mem_maximalIdeal _).mpr hc)
      have h3 := Ideal.sub_mem _ h1 h2
      rw [show (2 * c + T) ^ 2 - 4 * (c ^ 2 + T * c + Nn) = T ^ 2 - 4 * Nn by ring] at h3
      exact (mem_maximalIdeal _).mp h3 hd
    obtain ⟨r, hr, -⟩ := HenselianLocalRing.is_henselian (X ^ 2 + C T * X + C Nn) (by monicity!) c
      (by simpa [mem_maximalIdeal, mem_nonunits_iff] using hc)
      (by rw [show (derivative (X ^ 2 + C T * X + C Nn)).eval c = 2 * c + T by
        simp only [derivative_add, derivative_X_pow, derivative_C_mul_X, derivative_C, eval_add,
          eval_mul, eval_C, eval_pow, eval_X, add_zero] <;> norm_num]; exact hu)
    have hr' : r ^ 2 + T * r + Nn = 0 := by simpa using hr
    have hrR : (r : R) ^ 2 + (θ + star θ) * r + θ * star θ = 0 := by
      have h4 := congrArg (fun z : R₀ => (z : R)) hr'
      push_cast [hTc, hNc] at h4
      exact h4
    refine ⟨(r + θ) * Di, ?_, ?_⟩
    · linear_combination Di ^ 2 * hrR + (r + θ) * Di * hDi
    · simp only [star_mul', star_add, hst, hDis]
      linear_combination hDi
  · right
    push_neg at hs
    have hcoe : ∀ z : R₀, IsUnit z → IsUnit (z : R) := fun z hz => hz.map R₀.subtype
    have key : ∀ a b : R₀, IsUnit a ∨ IsUnit b → IsUnit ((a : R) + b * θ) := by
      intro a b hab
      have hNab : IsUnit (a ^ 2 + T * a * b + Nn * b ^ 2) := by
        rcases em (IsUnit b) with hb | hb
        · obtain ⟨bu, rfl⟩ := hb
          have hbb : (bu : R₀) * ↑bu⁻¹ = 1 := bu.mul_inv
          have e : a ^ 2 + T * a * bu + Nn * (bu : R₀) ^ 2 =
              (bu : R₀) ^ 2 * ((a * ↑bu⁻¹) ^ 2 + T * (a * ↑bu⁻¹) + Nn) := by
            linear_combination (-(a ^ 2) * ((bu : R₀) * ↑bu⁻¹ + 1) - T * a * bu) * hbb
          rw [e]
          exact (bu.isUnit.pow 2).mul (hs _)
        · have ha := hab.resolve_right hb
          by_contra hn
          have h1 : a ^ 2 + T * a * b + Nn * b ^ 2 ∈ maximalIdeal R₀ := (mem_maximalIdeal _).mpr hn
          have h2 : b * (T * a + Nn * b) ∈ maximalIdeal R₀ :=
            Ideal.mul_mem_right _ _ ((mem_maximalIdeal _).mpr hb)
          have h3 := Ideal.sub_mem _ h1 h2
          rw [show a ^ 2 + T * a * b + Nn * b ^ 2 - b * (T * a + Nn * b) = a ^ 2 by ring] at h3
          exact (mem_maximalIdeal _).mp h3 (ha.pow 2)
      have e : ((a : R) + b * θ) * (a + b * star θ) = ((a ^ 2 + T * a * b + Nn * b ^ 2 : R₀) : R) := by
        push_cast
        rw [hTc, hNc]
        ring
      exact isUnit_of_mul_isUnit_left (x := (a : R) + b * θ) (y := (a : R) + b * star θ)
        (by rw [e]; exact hcoe _ hNab)
    have hne : (ϖ : R) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
    have hnu : ¬ IsUnit (ϖ : R) := by
      intro h
      obtain ⟨w, hw⟩ := h.exists_right_inv
      have hw' : (ϖ : R) * star w = 1 := by
        have h5 := congrArg star hw
        rwa [star_mul', hst, star_one] at h5
      have hws : star w = w := by linear_combination w * hw' - star w * hw
      exact hϖ.not_isUnit (unit_of ϖ ⟨w, (hfix w).mpr hws⟩ (Subtype.ext hw))
    have hval : ∀ x : R, x ≠ 0 → ∃ n : ℕ, ∃ u : R, IsUnit u ∧ x = ϖ ^ n * u := by
      intro x hx
      obtain ⟨a, b, rfl⟩ := coord x
      by_cases ha : a = 0
      · subst ha
        have hb : b ≠ 0 := by
          rintro rfl
          simp at hx
        obtain ⟨j, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
        refine ⟨j, ((v : R₀) : R) * θ, ?_, ?_⟩
        · simpa using key 0 v (Or.inr v.isUnit)
        · push_cast
          ring
      by_cases hb : b = 0
      · subst hb
        obtain ⟨i, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
        refine ⟨i, ((u : R₀) : R), hcoe _ u.isUnit, ?_⟩
        push_cast
        ring
      obtain ⟨i, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
      obtain ⟨j, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
      rcases le_total i j with hij | hij
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
        refine ⟨i, ((u : R₀) : R) + ((v * ϖ ^ k : R₀) : R) * θ, key _ _ (Or.inl u.isUnit), ?_⟩
        push_cast
        ring
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
        refine ⟨j, ((u * ϖ ^ k : R₀) : R) + ((v : R₀) : R) * θ, key _ _ (Or.inr v.isUnit), ?_⟩
        push_cast
        ring
    have hdom : IsDomain R := by
      haveI : Nontrivial R := nontrivial_of_ne _ _ hne
      haveI : NoZeroDivisors R := by
        refine ⟨fun {x y} hxy => ?_⟩
        by_contra hc
        push_neg at hc
        obtain ⟨m, u, hu, rfl⟩ := hval x hc.1
        obtain ⟨n, v, hv, rfl⟩ := hval y hc.2
        have h1 : (ϖ : R) ^ (m + n) * (u * v) = 0 := by
          rw [← hxy]
          ring
        have h2 := (hu.mul hv).mul_left_eq_zero.mp h1
        exact pow_ne_zero (m + n) hϖ.ne_zero (Subtype.ext (by push_cast; exact h2))
      exact NoZeroDivisors.to_isDomain R
    exact ⟨hfix, ⟨θ, hθ⟩, ϖ.2, hne, hnu, hdom, hval⟩
end PI.SqPair.LCP
