-- Prove2me | solution 1 for PDSmooth.Framework.eq_3_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T03:09:11.45964+00:00
-- url     : https://prove2.me/submissions/5325af21-c1fe-4ffc-9a65-14ab8b8fe9f9

import Mathlib
import Definitions.Def_PDSmooth_Framework_Setting

open Filter Topology

namespace PDSmoothSol
open PDSmooth.Framework

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- For `x ∈ X`, the integrand `y ↦ Φ x y - g y - ρ ωY y` is bounded on `Y`. -/
lemma integrand_bound {X : Set E} {Y : Set F} {Φ : E → F → ℝ} {g : F → ℝ} {r : E → ℝ}
    {ωX : E → ℝ} {ωY : F → ℝ} {γ βX : ℝ} (hA : StandingAssumptions X Y Φ g r ωX ωY γ βX)
    (ρ : ℝ) {x : E} (hx : x ∈ X) :
    ∃ M, ∀ y ∈ Y, |Φ x y - g y - ρ * ωY y| ≤ M := by
  have hc : ContinuousOn (fun y => Φ x y - g y - ρ * ωY y) Y := by
    have h1 : ContinuousOn (fun y => Φ x y) Y := by
      have := hA.Φ_cont.comp (Continuous.continuousOn (continuous_const.prodMk continuous_id))
        (fun y hy => ⟨hx, hy⟩)
      exact this
    exact (h1.sub hA.g_cont).sub (continuousOn_const.mul hA.ωY_cont)
  obtain ⟨M, hM⟩ := hA.Y_compact.exists_bound_of_continuousOn hc
  exact ⟨M, fun y hy => by simpa [Real.norm_eq_abs] using hM y hy⟩

lemma bddAbove_integrand {X : Set E} {Y : Set F} {Φ : E → F → ℝ} {g : F → ℝ} {r : E → ℝ}
    {ωX : E → ℝ} {ωY : F → ℝ} {γ βX : ℝ} (hA : StandingAssumptions X Y Φ g r ωX ωY γ βX)
    (ρ : ℝ) {x : E} (hx : x ∈ X) :
    BddAbove (Set.range fun y : Y => Φ x y - g y - ρ * ωY y) := by
  obtain ⟨M, hM⟩ := integrand_bound hA ρ hx
  refine ⟨M, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact (le_abs_self _).trans (hM y y.2)

lemma bddAbove_integrand0 {X : Set E} {Y : Set F} {Φ : E → F → ℝ} {g : F → ℝ} {r : E → ℝ}
    {ωX : E → ℝ} {ωY : F → ℝ} {γ βX : ℝ} (hA : StandingAssumptions X Y Φ g r ωX ωY γ βX)
    {x : E} (hx : x ∈ X) :
    BddAbove (Set.range fun y : Y => Φ x y - g y) := by
  have := bddAbove_integrand hA 0 hx
  simpa using this

lemma bddAbove_absωY {X : Set E} {Y : Set F} {Φ : E → F → ℝ} {g : F → ℝ} {r : E → ℝ}
    {ωX : E → ℝ} {ωY : F → ℝ} {γ βX : ℝ} (hA : StandingAssumptions X Y Φ g r ωX ωY γ βX) :
    BddAbove (Set.range fun y : Y => |ωY y|) := by
  obtain ⟨M, hM⟩ := hA.Y_compact.exists_bound_of_continuousOn hA.ωY_cont
  refine ⟨M, ?_⟩
  rintro _ ⟨y, rfl⟩
  simpa [Real.norm_eq_abs] using hM y y.2

lemma abs_le_rangeY {X : Set E} {Y : Set F} {Φ : E → F → ℝ} {g : F → ℝ} {r : E → ℝ}
    {ωX : E → ℝ} {ωY : F → ℝ} {γ βX : ℝ} (hA : StandingAssumptions X Y Φ g r ωX ωY γ βX)
    {y : F} (hy : y ∈ Y) : |ωY y| ≤ rangeY ωY Y :=
  le_ciSup (f := fun y : Y => |ωY y|) (bddAbove_absωY hA) ⟨y, hy⟩

/-- Eq. (3.7). -/
theorem eq_3_7 {X : Set E} {Y : Set F} {Φ : E → F → ℝ} {g : F → ℝ} {r : E → ℝ}
    {ωX : E → ℝ} {ωY : F → ℝ} {γ βX : ℝ} (hA : StandingAssumptions X Y Φ g r ωX ωY γ βX)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (x : E) (hx : x ∈ X) :
    |fSmooth Φ g ωY Y ρ x - fMax Φ g Y x| ≤ ρ * rangeY ωY Y := by
  have : Nonempty Y := hA.Y_nonempty.to_subtype
  have hb := bddAbove_integrand hA ρ hx
  have hb0 := bddAbove_integrand0 hA hx
  unfold fSmooth fMax
  rw [abs_le]
  constructor
  · -- fMax ≤ fSmooth + ρ R
    have : (⨆ y : Y, (Φ x y - g y)) ≤ (⨆ y : Y, (Φ x y - g y - ρ * ωY y)) + ρ * rangeY ωY Y := by
      apply ciSup_le
      intro y
      have h1 : Φ x y - g y - ρ * ωY y ≤ ⨆ y : Y, (Φ x y - g y - ρ * ωY y) :=
        le_ciSup (f := fun y : Y => Φ x y - g y - ρ * ωY y) hb y
      have h2 := abs_le_rangeY hA y.2
      have h3 : ρ * ωY y ≤ ρ * rangeY ωY Y :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans h2) hρ
      linarith
    linarith
  · have : (⨆ y : Y, (Φ x y - g y - ρ * ωY y)) ≤ (⨆ y : Y, (Φ x y - g y)) + ρ * rangeY ωY Y := by
      apply ciSup_le
      intro y
      have h1 : Φ x y - g y ≤ ⨆ y : Y, (Φ x y - g y) :=
        le_ciSup (f := fun y : Y => Φ x y - g y) hb0 y
      have h2 := abs_le_rangeY hA y.2
      have h3 : -(ρ * ωY y) ≤ ρ * rangeY ωY Y := by
        rw [← mul_neg]
        exact mul_le_mul_of_nonneg_left ((neg_le_abs _).trans h2) hρ
      linarith
    linarith

end PDSmoothSol

open PDSmooth.Framework PDSmoothSol

theorem solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {X : Set E} {Y : Set F} {Φ : E → F → ℝ} {g : F → ℝ} {r : E → ℝ} {ωX : E → ℝ} {ωY : F → ℝ}
    {γ βX : ℝ} (hA : StandingAssumptions X Y Φ g r ωX ωY γ βX)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (x : E) (hx : x ∈ X) :
    |fSmooth Φ g ωY Y ρ x - fMax Φ g Y x| ≤ ρ * rangeY ωY Y :=
  PDSmoothSol.eq_3_7 hA ρ hρ x hx
