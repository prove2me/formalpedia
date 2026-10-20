-- Prove2me | solution 1 for PDSmooth.Framework.strongConvex_Q
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T03:09:20.493833+00:00
-- url     : https://prove2.me/submissions/a8863fed-59c3-4707-a992-4410c7ec4bcb

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

/-- Jensen-form weak convexity derived from the gradient form (1.4). -/
lemma weak_jensen {X : Set E} {Y : Set F} {Φ : E → F → ℝ} {g : F → ℝ} {r : E → ℝ}
    {ωX : E → ℝ} {ωY : F → ℝ} {γ βX : ℝ} (hA : StandingAssumptions X Y Φ g r ωX ωY γ βX)
    {y : F} (hy : y ∈ Y) {u v : E} (hu : u ∈ X) (hv : v ∈ X) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    Φ (a • u + b • v) y ≤ a * Φ u y + b * Φ v y + a * b * (γ / 2) * ‖u - v‖ ^ 2 := by
  set z := a • u + b • v with hz
  have hzX : z ∈ X := hA.X_convex hu hv ha hb hab
  have h1 := hA.weakConvex y hy z hzX u hu
  have h2 := hA.weakConvex y hy z hzX v hv
  set L := fderiv ℝ (fun w => Φ w y) z
  have hb' : b = 1 - a := by linarith
  have hu' : u - z = b • (u - v) := by rw [hz, hb']; module
  have hv' : v - z = (-a) • (u - v) := by rw [hz, hb']; module
  rw [hu', map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb] at h1
  rw [hv', map_smul, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg ha] at h2
  simp only [smul_eq_mul] at h1 h2
  have e : a * (Φ u y) + b * (Φ v y) ≥ Φ z y + a * b * (L (u - v)) - a * b * (L (u - v))
      - (γ / 2) * (a * b ^ 2 + b * a ^ 2) * ‖u - v‖ ^ 2 := by
    have k1 := mul_le_mul_of_nonneg_left h1 ha
    have k2 := mul_le_mul_of_nonneg_left h2 hb
    have k3 : (a + b) * Φ z y = Φ z y := by rw [hab, one_mul]
    nlinarith [k1, k2, k3]
  have : a * b ^ 2 + b * a ^ 2 = a * b := by
    have : a * b ^ 2 + b * a ^ 2 = a * b * (a + b) := by ring
    rw [this, hab, mul_one]
  rw [this] at e
  linarith

lemma fSmooth_jensen {X : Set E} {Y : Set F} {Φ : E → F → ℝ} {g : F → ℝ} {r : E → ℝ}
    {ωX : E → ℝ} {ωY : F → ℝ} {γ βX : ℝ} (hA : StandingAssumptions X Y Φ g r ωX ωY γ βX)
    (ρ : ℝ) {u v : E} (hu : u ∈ X) (hv : v ∈ X) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    fSmooth Φ g ωY Y ρ (a • u + b • v) ≤ a * fSmooth Φ g ωY Y ρ u + b * fSmooth Φ g ωY Y ρ v
      + a * b * (γ / 2) * ‖u - v‖ ^ 2 := by
  have : Nonempty Y := hA.Y_nonempty.to_subtype
  unfold fSmooth
  apply ciSup_le
  intro y
  have h1 := weak_jensen hA y.2 hu hv ha hb hab
  have hu1 : Φ u y - g y - ρ * ωY y ≤ ⨆ y : Y, (Φ u y - g y - ρ * ωY y) :=
    le_ciSup (f := fun y : Y => Φ u y - g y - ρ * ωY y) (bddAbove_integrand hA ρ hu) y
  have hv1 : Φ v y - g y - ρ * ωY y ≤ ⨆ y : Y, (Φ v y - g y - ρ * ωY y) :=
    le_ciSup (f := fun y : Y => Φ v y - g y - ρ * ωY y) (bddAbove_integrand hA ρ hv) y
  have k1 := mul_le_mul_of_nonneg_left hu1 ha
  have k2 := mul_le_mul_of_nonneg_left hv1 hb
  have k3 : (a + b) * (g y + ρ * ωY y) = g y + ρ * ωY y := by rw [hab, one_mul]
  nlinarith [k1, k2, k3, h1]

/-- Strong convexity of `Q^λ_ρ(·;x)` (any `ρ`). -/
theorem strongConvex_Qrho_gen {X : Set E} {Y : Set F} {Φ : E → F → ℝ} {g : F → ℝ} {r : E → ℝ}
    {ωX : E → ℝ} {ωY : F → ℝ} {γ βX : ℝ} (hA : StandingAssumptions X Y Φ g r ωX ωY γ βX)
    (lam ρ : ℝ) (hlam0 : 0 < lam) (x : E) :
    StrongConvexOn X (lam⁻¹ - γ) (Qprox (qSmooth Φ g r ωY Y ρ) ωX lam x) := by
  refine ⟨hA.X_convex, ?_⟩
  intro u hu v hv a b ha hb hab
  have h1 := fSmooth_jensen hA ρ hu hv ha hb hab
  have h2 := hA.r_convex.2 hu hv ha hb hab
  have h3 := hA.ωX_strong.2 hu hv ha hb hab
  simp only [smul_eq_mul] at h2 h3
  set L := fderiv ℝ ωX x
  have hb' : b = 1 - a := by linarith
  have e4 : L (a • u + b • v - x) = a * L (u - x) + b * L (v - x) := by
    have : a • u + b • v - x = a • (u - x) + b • (v - x) := by rw [hb']; module
    rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hli : 0 ≤ lam⁻¹ := inv_nonneg.mpr hlam0.le
  have h3' := mul_le_mul_of_nonneg_left h3 hli
  have e4' := congrArg (fun t => lam⁻¹ * t) e4
  have ec : lam⁻¹ * ωX x = lam⁻¹ * (a * ωX x) + lam⁻¹ * (b * ωX x) := by
    rw [← mul_add, ← add_mul, hab, one_mul]

  unfold Qprox bregman qSmooth
  simp only [smul_eq_mul]
  nlinarith [h1, h2, h3', e4', ec]

lemma qObj_eq_qSmooth_zero (Φ : E → F → ℝ) (g : F → ℝ) (r : E → ℝ) (ωY : F → ℝ) (Y : Set F) :
    qObj Φ g r Y = qSmooth Φ g r ωY Y 0 := by
  funext x; simp [qObj, qSmooth, fSmooth, fMax]

theorem strongConvex_Q_gen {X : Set E} {Y : Set F} {Φ : E → F → ℝ} {g : F → ℝ} {r : E → ℝ}
    {ωX : E → ℝ} {ωY : F → ℝ} {γ βX : ℝ} (hA : StandingAssumptions X Y Φ g r ωX ωY γ βX)
    (lam : ℝ) (hlam0 : 0 < lam) (x : E) :
    StrongConvexOn X (lam⁻¹ - γ) (Qprox (qObj Φ g r Y) ωX lam x) := by
  rw [qObj_eq_qSmooth_zero Φ g r ωY Y]
  exact strongConvex_Qrho_gen hA lam 0 hlam0 x

end PDSmoothSol

open PDSmooth.Framework PDSmoothSol

theorem solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {X : Set E} {Y : Set F} {Φ : E → F → ℝ} {g : F → ℝ} {r : E → ℝ} {ωX : E → ℝ} {ωY : F → ℝ}
    {γ βX : ℝ} (hA : StandingAssumptions X Y Φ g r ωX ωY γ βX)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < γ⁻¹) (x : E) (hx : x ∈ X) :
    StrongConvexOn X (lam⁻¹ - γ) (Qprox (qObj Φ g r Y) ωX lam x) :=
  PDSmoothSol.strongConvex_Q_gen hA lam hlam0 x
