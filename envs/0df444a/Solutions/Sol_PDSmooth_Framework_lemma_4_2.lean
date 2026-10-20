-- Prove2me | solution 1 for PDSmooth.Framework.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T03:11:24.945094+00:00
-- url     : https://prove2.me/submissions/1bafaaad-535a-4bf3-8ef4-63c76cf81eba

import Mathlib
import Definitions.Def_PDSmooth_Framework_Setting
import Theorems.Thm_PDSmooth_Framework_strongConvex_Qrho

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

lemma run_mem {X : Set E} {Y : Set F} {Φ : E → F → ℝ} {g : F → ℝ} {r : E → ℝ}
    {ωX : E → ℝ} {ωY : F → ℝ} {γ lam η : ℝ} {x : ℕ → E}
    (hx : IsAlg1Run X Y Φ g r ωX ωY γ lam η x) :
    ∀ k : ℕ, 1 ≤ k → (∀ j : ℕ, 1 ≤ j → j < k → ¬ Stops γ lam η x j) → x k ∈ X := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ n ih =>
    intro _ hpre
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; exact hx.1
    · exact (hx.2 n hn (fun j hj1 hj2 => hpre j hj1 (by omega))).1

lemma rho_nonneg {R η : ℝ} (hR : 0 ≤ R) (hη : 0 < η) : 0 ≤ 2 * η / R := by positivity

lemma lam_gap {γ lam : ℝ} (hγ : 0 < γ) (hlam0 : 0 < lam) (hlam1 : lam < γ⁻¹) :
    0 < lam⁻¹ - γ := by
  have : γ < lam⁻¹ := by
    rw [lt_inv_comm₀ hlam0 hγ] at hlam1; exact hlam1
  linarith

end PDSmoothSol

open PDSmooth.Framework PDSmoothSol

theorem solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {X : Set E} {Y : Set F} {Φ : E → F → ℝ} {g : F → ℝ} {r : E → ℝ} {ωX : E → ℝ} {ωY : F → ℝ}
    {γ βX : ℝ} (hA : StandingAssumptions X Y Φ g r ωX ωY γ βX)
    (lam η : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < γ⁻¹) (hη : 0 < η)
    (x : ℕ → E) (hx : IsAlg1Run X Y Φ g r ωX ωY γ lam η x)
    (K : ℕ) (hK1 : 1 ≤ K) (hKstop : Stops γ lam η x K)
    (hKfirst : ∀ j : ℕ, 1 ≤ j → j < K → ¬ Stops γ lam η x j)
    (p : E) (hp : IsProx (qSmooth Φ g r ωY Y (2 * η / rangeY ωY Y)) ωX X lam (x K) p) :
    ‖x K - p‖ ≤ 2 * Real.sqrt (2 * η / (lam⁻¹ - γ)) := by
  have hμ := lam_gap hA.γ_pos hlam0 hlam1
  set ρ := 2 * η / rangeY ωY Y
  obtain ⟨hK1X, hrun⟩ := hx.2 K hK1 hKfirst
  have hsc := PDSmooth.Framework.strongConvex_Qrho hA lam ρ hlam0 hlam1
    (rho_nonneg (rangeY_nonneg hA) hη) (x K) (run_mem hx K hK1 hKfirst)
  have hg := quad_growth hsc hp.1 hp.2 hK1X
  have h1 := hrun p hp.1
  have hs : 0 ≤ 2 * η / (lam⁻¹ - γ) := by positivity
  have hd1 : ‖x (K + 1) - p‖ ≤ Real.sqrt (2 * η / (lam⁻¹ - γ)) := by
    apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ hμ]
    nlinarith
  have htri : ‖x K - p‖ ≤ ‖x (K + 1) - x K‖ + ‖x (K + 1) - p‖ := by
    calc ‖x K - p‖ = ‖-(x (K + 1) - x K) + (x (K + 1) - p)‖ := by congr 1; abel
      _ ≤ ‖-(x (K + 1) - x K)‖ + ‖x (K + 1) - p‖ := norm_add_le _ _
      _ = _ := by rw [norm_neg]
  unfold Stops at hKstop
  linarith
