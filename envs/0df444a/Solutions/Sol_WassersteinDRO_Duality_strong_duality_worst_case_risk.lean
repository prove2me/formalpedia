-- Prove2me | solution 1 for WassersteinDRO.Duality.strong_duality_worst_case_risk
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T04:41:25.669516+00:00
-- url     : https://prove2.me/submissions/a1649d92-caba-4e78-971e-96063eeae6a4

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_worstCaseRisk
import Definitions.Def_WassersteinDRO_Duality_moreauYosida
import Definitions.Def_WassersteinDRO_Duality_nominalRisk

set_option autoImplicit false

open MeasureTheory

namespace Cex48a9

/-- `ℝ` equipped with the trivial σ-algebra `⊥` (the target allows any `MeasurableSpace E`). -/
def R0 : Type := ℝ

noncomputable instance : NormedAddCommGroup R0 := inferInstanceAs (NormedAddCommGroup ℝ)

instance : MeasurableSpace R0 := ⊥

/-- The bounded continuous loss `ℓ = sin`. -/
noncomputable def ell : BoundedContinuousFunction R0 ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x : R0 => Real.sin (x : ℝ), Real.continuous_sin⟩ 2 (fun x y => by
      show dist (Real.sin (x : ℝ)) (Real.sin (y : ℝ)) ≤ 2
      rw [Real.dist_eq, abs_le]
      have h1 := Real.sin_le_one (x : ℝ)
      have h2 := Real.neg_one_le_sin (x : ℝ)
      have h3 := Real.sin_le_one (y : ℝ)
      have h4 := Real.neg_one_le_sin (y : ℝ)
      constructor <;> linarith)

theorem ell_apply (x : R0) : ell x = Real.sin (x : ℝ) := rfl

/-- On the trivial σ-algebra, a nonzero measure has no nonempty null set. -/
theorem null_empty (Q : Measure R0) (hQ : Q Set.univ = 1) (s : Set R0) (hs : Q s = 0) :
    s = ∅ := by
  obtain ⟨t, hst, ht, ht0⟩ := exists_measurable_superset_of_null hs
  rcases (MeasurableSpace.measurableSet_bot_iff (s := t)).1 ht with h | h
  · exact Set.subset_eq_empty hst h
  · rw [h, hQ] at ht0
    exact absurd ht0 one_ne_zero

/-- `sin` is not integrable for any probability measure on the trivial σ-algebra. -/
theorem not_integrable (Q : Measure R0) (hQ : Q Set.univ = 1) :
    ¬ Integrable (ell : R0 → ℝ) Q := by
  intro hI
  obtain ⟨g, hg, hfg⟩ := hI.aestronglyMeasurable
  obtain ⟨c, hc⟩ := (stronglyMeasurable_bot_iff (f := g)).1 hg
  have hnull : Q {x | (ell : R0 → ℝ) x ≠ g x} = 0 := ae_iff.1 hfg
  have hempty := null_empty Q hQ _ hnull
  have hall : ∀ x : R0, ell x = c := by
    intro x
    by_contra hx
    have hmem : x ∈ {x | (ell : R0 → ℝ) x ≠ g x} := by
      show ell x ≠ g x
      rw [hc]
      exact hx
    rw [hempty] at hmem
    exact hmem
  have a0 := hall (0 : ℝ)
  have a1 := hall (Real.pi / 2 : ℝ)
  have e0 : ell ((0 : ℝ) : R0) = 0 := Real.sin_zero
  have e1 : ell ((Real.pi / 2 : ℝ) : R0) = 1 := Real.sin_pi_div_two
  linarith

open WassersteinDRO.Duality in
theorem my_bound (γ : ℝ) (hγ : 0 ≤ γ) (x : R0) :
    |moreauYosida Set.univ ell 1 γ x| ≤ 1 := by
  unfold moreauYosida
  have hne : ((fun z => ell z - γ * ‖z - x‖ ^ (1 : ℝ)) '' (Set.univ : Set R0)).Nonempty :=
    ⟨_, x, trivial, rfl⟩
  have hub : ∀ y ∈ ((fun z => ell z - γ * ‖z - x‖ ^ (1 : ℝ)) '' (Set.univ : Set R0)), y ≤ 1 := by
    rintro _ ⟨z, -, rfl⟩
    have h1 : ell z ≤ 1 := by rw [ell_apply]; exact Real.sin_le_one _
    have h2 : 0 ≤ γ * ‖z - x‖ ^ (1 : ℝ) := mul_nonneg hγ (Real.rpow_nonneg (norm_nonneg _) _)
    show ell z - γ * ‖z - x‖ ^ (1 : ℝ) ≤ 1
    linarith
  rw [abs_le]
  constructor
  · apply le_csSup_of_le ⟨1, hub⟩ ⟨x, trivial, rfl⟩
    show -1 ≤ ell x - γ * ‖x - x‖ ^ (1 : ℝ)
    rw [sub_self, norm_zero, Real.rpow_one, mul_zero, sub_zero, ell_apply]
    exact Real.neg_one_le_sin _
  · exact csSup_le hne hub

open WassersteinDRO.Duality in
theorem lhs_bot :
    worstCaseRisk 1 1 (Set.univ : Set R0) (Measure.dirac (0 : R0)) (ell : R0 → ℝ) = ⊥ := by
  unfold worstCaseRisk
  refine iSup_eq_bot.2 fun Q => iSup_eq_bot.2 fun hQ => iSup_eq_bot.2 fun hI => ?_
  exact absurd hI (not_integrable Q hQ.1)

open WassersteinDRO.Duality in
theorem rhs_ge :
    (((-1 : ℝ)) : EReal) ≤ ⨅ (γ : ℝ) (_ : 0 ≤ γ),
        ((∫ x, moreauYosida (Set.univ : Set R0) ell 1 γ x ∂(Measure.dirac (0 : R0)) : ℝ) : EReal) +
          ((ENNReal.ofReal (γ * (1 : ℝ) ^ (1 : ℝ)) : ENNReal) : EReal) := by
  refine le_iInf₂ fun γ hγ => ?_
  have hI : ‖∫ x, moreauYosida (Set.univ : Set R0) ell 1 γ x ∂(Measure.dirac (0 : R0))‖ ≤
      1 * (Measure.dirac (0 : R0)).real Set.univ :=
    norm_integral_le_of_norm_le_const (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact my_bound γ hγ x)
  rw [probReal_univ, mul_one, Real.norm_eq_abs, abs_le] at hI
  have h1 : (((-1 : ℝ)) : EReal) ≤
      ((∫ x, moreauYosida (Set.univ : Set R0) ell 1 γ x ∂(Measure.dirac (0 : R0)) : ℝ) : EReal) :=
    EReal.coe_le_coe_iff.2 hI.1
  exact le_add_of_le_of_nonneg h1 (EReal.coe_ennreal_nonneg _)

end Cex48a9

open MeasureTheory WassersteinDRO.Duality in
theorem solution : ¬ (∀ {E : Type} [MeasurableSpace E] [NormedAddCommGroup E]
    (ε p : ℝ) (hε : 0 ≤ ε) (hp : 1 ≤ p) (Ξ : Set E) (hΞne : Ξ.Nonempty) (hΞcl : IsClosed Ξ)
    (PN : Measure E) [IsProbabilityMeasure PN] (hPNΞ : PN Ξᶜ = 0)
    (ℓ : BoundedContinuousFunction E ℝ),
    worstCaseRisk ε p Ξ PN (ℓ : E → ℝ) =
      ⨅ (γ : ℝ) (_ : 0 ≤ γ),
        ((∫ x, moreauYosida Ξ ℓ p γ x ∂PN : ℝ) : EReal) +
          ((ENNReal.ofReal (γ * ε ^ p) : ENNReal) : EReal)) := by
  intro h
  have key := h (E := Cex48a9.R0) 1 1 zero_le_one le_rfl Set.univ Set.univ_nonempty isClosed_univ
    (Measure.dirac (0 : Cex48a9.R0)) (by simp) Cex48a9.ell
  rw [Cex48a9.lhs_bot] at key
  have hge := Cex48a9.rhs_ge
  rw [← key] at hge
  exact EReal.coe_ne_bot (-1) (le_bot_iff.1 hge)
