-- Prove2me | solution 1 for ProgHedging.Nonconvex.eq_6_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T07:22:21.95324+00:00
-- url     : https://prove2.me/submissions/15e0b1b9-a467-4a84-8247-655a4d1a5a5c

import Mathlib
import Definitions.Def_ProgHedging_Convex_Problem
import Definitions.Def_ProgHedging_Nonconvex_Algorithm
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_ClarkeGradients_FlowInvariance_normalCone

open scoped Pointwise
open Filter Topology

namespace Aux_PH62


lemma hasGradientAt_quad {n : ℕ} (r : ℝ) (c y : EuclideanSpace ℝ (Fin n)) :
    HasGradientAt (fun x : EuclideanSpace ℝ (Fin n) => r / 2 * ‖x - c‖ ^ 2) (r • (y - c)) y := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h1 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin n) => ‖x - c‖ ^ 2) (2 • innerSL ℝ (y - c)) y := by
    have := (hasStrictFDerivAt_norm_sq (y - c)).hasFDerivAt
    exact this.comp y ((hasFDerivAt_id y).sub_const c)
  have h2 := h1.const_mul (r / 2)
  have heq : (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))) (r • (y - c)) = (r / 2) • 2 • innerSL ℝ (y - c) := by
    ext v
    rw [InnerProductSpace.toDual_apply_apply]
    simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, inner_smul_left, smul_eq_mul,
      RCLike.conj_to_real]
    ring
  rw [heq]
  exact h2

lemma diff_iff {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (r : ℝ) (c y : EuclideanSpace ℝ (Fin n)) :
    DifferentiableAt ℝ (fun x => f x + r / 2 * ‖x - c‖ ^ 2) y ↔ DifferentiableAt ℝ f y := by
  have hq : DifferentiableAt ℝ (fun x : EuclideanSpace ℝ (Fin n) => r / 2 * ‖x - c‖ ^ 2) y :=
    (hasGradientAt_quad r c y).differentiableAt
  constructor
  · intro h
    have heq : f = (fun x => f x + r / 2 * ‖x - c‖ ^ 2) - (fun x => r / 2 * ‖x - c‖ ^ 2) := by
      funext x; simp
    rw [heq]; exact h.sub hq
  · intro h; exact h.add hq

lemma gradient_eq {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (r : ℝ) (c y : EuclideanSpace ℝ (Fin n)) (h : DifferentiableAt ℝ f y) :
    gradient (fun x => f x + r / 2 * ‖x - c‖ ^ 2) y = gradient f y + r • (y - c) := by
  have h1 : HasGradientAt f (gradient f y) y := h.hasGradientAt
  have h2 := hasGradientAt_quad r c y
  have h3 : HasGradientAt (fun x => f x + r / 2 * ‖x - c‖ ^ 2) (gradient f y + r • (y - c)) y := by
    rw [hasGradientAt_iff_hasFDerivAt] at *
    have := h1.add h2
    rw [map_add]
    exact this
  exact h3.gradient

lemma gradientLimits_eq {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (r : ℝ) (c x : EuclideanSpace ℝ (Fin n)) :
    ClarkeGradients.Shared.gradientLimits (fun x => f x + r / 2 * ‖x - c‖ ^ 2) x =
      ClarkeGradients.Shared.gradientLimits f x + {r • (x - c)} := by
  ext ζ
  rw [Set.add_singleton, Set.mem_image]
  have hcont : ∀ h : ℕ → EuclideanSpace ℝ (Fin n), Tendsto h atTop (𝓝 0) →
      Tendsto (fun i => r • (x + h i - c)) atTop (𝓝 (r • (x - c))) := by
    intro h hh
    have : Tendsto (fun i => r • (x + h i - c)) atTop (𝓝 (r • (x + 0 - c))) :=
      ((tendsto_const_nhds.add hh).sub tendsto_const_nhds).const_smul r
    simpa using this
  constructor
  · rintro ⟨h, hh, hd, hg⟩
    have hd' : ∀ i, DifferentiableAt ℝ f (x + h i) := fun i => (diff_iff f r c _).mp (hd i)
    refine ⟨ζ - r • (x - c), ⟨h, hh, hd', ?_⟩, by abel⟩
    have := hg.sub (hcont h hh)
    refine this.congr (fun i => ?_)
    rw [gradient_eq f r c _ (hd' i)]
    abel
  · rintro ⟨η, ⟨h, hh, hd, hg⟩, rfl⟩
    refine ⟨h, hh, fun i => (diff_iff f r c _).mpr (hd i), ?_⟩
    have := hg.add (hcont h hh)
    refine this.congr (fun i => ?_)
    rw [gradient_eq f r c _ (hd i)]

end Aux_PH62

open ProgHedging.Nonconvex in
theorem solution {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) (r : ℝ)
    (Xs : ProgHedging.Convex.Policy S n) (s : S) :
    (∀ x : EuclideanSpace ℝ (Fin n),
      ClarkeGradients.Shared.generalizedGradient (pr.fTilde r Xs s) x =
        ClarkeGradients.Shared.generalizedGradient (pr.f s) x + {r • (x - Xs s)}) ∧
    ClarkeGradients.Shared.generalizedGradient (pr.fTilde r Xs s) (Xs s) =
      ClarkeGradients.Shared.generalizedGradient (pr.f s) (Xs s) := by
  have key : ∀ x : EuclideanSpace ℝ (Fin n),
      ClarkeGradients.Shared.generalizedGradient (pr.fTilde r Xs s) x =
        ClarkeGradients.Shared.generalizedGradient (pr.f s) x + {r • (x - Xs s)} := by
    intro x
    have hft : pr.fTilde r Xs s = fun y => pr.f s y + r / 2 * ‖y - Xs s‖ ^ 2 := rfl
    unfold ClarkeGradients.Shared.generalizedGradient
    rw [hft, Aux_PH62.gradientLimits_eq, convexHull_add, convexHull_singleton]
  refine ⟨key, ?_⟩
  rw [key, sub_self, smul_zero, Set.add_singleton]
  simp
