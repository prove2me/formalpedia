-- Prove2me | solution 1 for PDSmooth.Framework.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T03:11:25.864347+00:00
-- url     : https://prove2.me/submissions/cbc12f8d-e0e0-4e31-b18b-86d06e87573f

import Mathlib
import Definitions.Def_PDSmooth_Framework_Setting
import Theorems.Thm_PDSmooth_Framework_strongConvex_Q
import Theorems.Thm_PDSmooth_Framework_eq_3_7

open Filter Topology

namespace PDSmoothSol
open PDSmooth.Framework

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma bddAbove_absωY {X : Set E} {Y : Set F} {Φ : E → F → ℝ} {g : F → ℝ} {r : E → ℝ}
    {ωX : E → ℝ} {ωY : F → ℝ} {γ βX : ℝ} (hA : StandingAssumptions X Y Φ g r ωX ωY γ βX) :
    BddAbove (Set.range fun y : Y => |ωY y|) := by
  obtain ⟨M, hM⟩ := hA.Y_compact.exists_bound_of_continuousOn hA.ωY_cont
  refine ⟨M, ?_⟩
  rintro _ ⟨y, rfl⟩
  simpa [Real.norm_eq_abs] using hM y y.2

lemma rangeY_nonneg {X : Set E} {Y : Set F} {Φ : E → F → ℝ} {g : F → ℝ} {r : E → ℝ}
    {ωX : E → ℝ} {ωY : F → ℝ} {γ βX : ℝ} (hA : StandingAssumptions X Y Φ g r ωX ωY γ βX) :
    0 ≤ rangeY ωY Y := by
  obtain ⟨y0, hy0⟩ := hA.Y_nonempty
  exact (abs_nonneg _).trans (le_ciSup (bddAbove_absωY hA) (⟨y0, hy0⟩ : Y))

/-- Quadratic growth at a minimizer of an `m`-strongly convex function. -/
lemma quad_growth {X : Set E} {Q : E → ℝ} {m : ℝ} (hsc : StrongConvexOn X m Q) {p z : E}
    (hp : p ∈ X) (hmin : ∀ w ∈ X, Q p ≤ Q w) (hz : z ∈ X) :
    m / 2 * ‖z - p‖ ^ 2 ≤ Q z - Q p := by
  have hlim : Tendsto (fun t : ℝ => (1 - t) * (m / 2 * ‖p - z‖ ^ 2)) (𝓝[>] 0)
      (𝓝 (m / 2 * ‖p - z‖ ^ 2)) := by
    have : Tendsto (fun t : ℝ => (1 - t) * (m / 2 * ‖p - z‖ ^ 2)) (𝓝 0)
        (𝓝 ((1 - 0) * (m / 2 * ‖p - z‖ ^ 2))) :=
      ((continuous_const.sub continuous_id).mul continuous_const).tendsto 0
    rw [sub_zero, one_mul] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), (1 - t) * (m / 2 * ‖p - z‖ ^ 2) ≤ Q z - Q p := by
    have hlt : ∀ᶠ t in 𝓝[>] (0:ℝ), t < 1 :=
      nhdsWithin_le_nhds (eventually_lt_nhds zero_lt_one)
    filter_upwards [hlt, self_mem_nhdsWithin] with t ht1 ht0
    have ht0' : (0:ℝ) < t := ht0
    have key := hsc.2 hp hz (show (0:ℝ) ≤ 1 - t by linarith) ht0'.le
      (show (1 - t) + t = 1 by ring)
    have hm := hmin _ (hsc.1 hp hz (show (0:ℝ) ≤ 1 - t by linarith) ht0'.le
      (show (1 - t) + t = 1 by ring))
    simp only [smul_eq_mul] at key
    have : t * ((1 - t) * (m / 2 * ‖p - z‖ ^ 2)) ≤ t * (Q z - Q p) := by nlinarith
    exact le_of_mul_le_mul_left this ht0'
  have := le_of_tendsto hlim hev
  rw [norm_sub_rev z p]
  exact this

lemma lam_gap {γ lam : ℝ} (hγ : 0 < γ) (hlam0 : 0 < lam) (hlam1 : lam < γ⁻¹) :
    0 < lam⁻¹ - γ := by
  have : γ < lam⁻¹ := by
    rw [lt_inv_comm₀ hlam0 hγ] at hlam1; exact hlam1
  linarith

/-- `|Q^λ_ρ(z;x) − Q^λ(z;x)| ≤ ρ R_Y(ω_Y)` on `X`. -/
lemma Qprox_close [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {X : Set E} {Y : Set F} {Φ : E → F → ℝ} {g : F → ℝ} {r : E → ℝ}
    {ωX : E → ℝ} {ωY : F → ℝ} {γ βX : ℝ} (hA : StandingAssumptions X Y Φ g r ωX ωY γ βX)
    (ρ lam : ℝ) (hρ : 0 ≤ ρ) (x z : E) (hz : z ∈ X) :
    |Qprox (qSmooth Φ g r ωY Y ρ) ωX lam x z - Qprox (qObj Φ g r Y) ωX lam x z|
      ≤ ρ * rangeY ωY Y := by
  have := PDSmooth.Framework.eq_3_7 hA ρ hρ z hz
  unfold Qprox qSmooth qObj
  have e : fSmooth Φ g ωY Y ρ z + r z + lam⁻¹ * bregman ωX z x -
      (fMax Φ g Y z + r z + lam⁻¹ * bregman ωX z x) = fSmooth Φ g ωY Y ρ z - fMax Φ g Y z := by
    ring
  rw [e]; exact this

lemma norm_le_two_sqrt {v a : ℝ} (hv : 0 ≤ v) (ha : 0 ≤ a) (h : v ^ 2 ≤ 4 * a) :
    v ≤ 2 * Real.sqrt a := by
  nlinarith [Real.sq_sqrt ha, Real.sqrt_nonneg a]

end PDSmoothSol

open PDSmooth.Framework PDSmoothSol

theorem solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {X : Set E} {Y : Set F} {Φ : E → F → ℝ} {g : F → ℝ} {r : E → ℝ} {ωX : E → ℝ} {ωY : F → ℝ}
    {γ βX : ℝ} (hA : StandingAssumptions X Y Φ g r ωX ωY γ βX)
    (lam ρ : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < γ⁻¹) (hρ : 0 ≤ ρ) (x : E) (hx : x ∈ X)
    (p pρ : E) (hp : IsProx (qObj Φ g r Y) ωX X lam x p)
    (hpρ : IsProx (qSmooth Φ g r ωY Y ρ) ωX X lam x pρ) :
    ‖pρ - p‖ ≤ 2 * Real.sqrt (ρ * rangeY ωY Y / (lam⁻¹ - γ)) := by
  have hμ := lam_gap hA.γ_pos hlam0 hlam1
  have hsc := PDSmooth.Framework.strongConvex_Q hA lam hlam0 hlam1 x hx
  have hg := quad_growth hsc hp.1 hp.2 hpρ.1
  have c1 := abs_le.mp (Qprox_close hA ρ lam hρ x pρ hpρ.1)
  have c2 := abs_le.mp (Qprox_close hA ρ lam hρ x p hp.1)
  have m := hpρ.2 p hp.1
  have hR := rangeY_nonneg hA
  apply norm_le_two_sqrt (norm_nonneg _) (by positivity)
  rw [mul_div_assoc', le_div_iff₀ hμ]
  nlinarith
