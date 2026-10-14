-- Prove2me | solution 1 for SmaleDiffS4.continuous_of_smoothIsotopy
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-12T04:29:08.961971+00:00
-- url     : https://prove2.me/submissions/8e292892-cbd3-4890-a3f1-e105075d24bf

import Mathlib
import Definitions.Def_SmaleDiffS4_Basic

set_option autoImplicit false

open SmaleDiffS4
open scoped ContDiff Manifold
open Filter Topology

namespace SmaleDiffS4.S4_B

variable {n : ℕ}

lemma nat_le_infty (k : ℕ) : ((k : ℕ) : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
  exact_mod_cast le_top

lemma iteratedFDeriv_slice_eq (F : ℝ × E n → E n) (hF : ContDiff ℝ ∞ F) (k : ℕ) (t : ℝ)
    (x : E n) :
    iteratedFDeriv ℝ k (fun y => F (t, y)) x =
      (iteratedFDeriv ℝ k F (t, x)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ ℝ (E n)) := by
  have h1 : (fun y => F (t, y)) =
      (fun z => F ((t, 0) + z)) ∘ (ContinuousLinearMap.inr ℝ ℝ (E n)) := by
    funext y; simp
  rw [h1, ContinuousLinearMap.iteratedFDeriv_comp_right _ ?_ _ (nat_le_infty k)]
  · rw [iteratedFDeriv_comp_add_left]; simp
  · exact hF.comp (contDiff_const.add contDiff_id)

lemma continuous_slice (F : ℝ × E n → E n) (hF : ContDiff ℝ ∞ F) (k : ℕ) :
    Continuous (fun p : ℝ × E n => iteratedFDeriv ℝ k (fun y => F (p.1, y)) p.2) := by
  have : (fun p : ℝ × E n => iteratedFDeriv ℝ k (fun y => F (p.1, y)) p.2) =
      fun p => (ContinuousMultilinearMap.compContinuousLinearMapL
        (fun _ : Fin k => ContinuousLinearMap.inr ℝ ℝ (E n)))
          (iteratedFDeriv ℝ k F p) := by
    funext p
    rw [iteratedFDeriv_slice_eq F hF k p.1 p.2]
    rfl
  rw [this]
  exact (ContinuousLinearMap.continuous _).comp (hF.continuous_iteratedFDeriv (nat_le_infty k))

lemma iteratedFDeriv_eq_id (f : DiffDisk n) (k : ℕ) (x : E n) (hx : 1 < ‖x‖) :
    iteratedFDeriv ℝ k (f.1 : E n → E n) x = iteratedFDeriv ℝ k id x := by
  have hU : {y : E n | 1 < ‖y‖} ∈ 𝓝 x :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hx
  have h : (f.1 : E n → E n) =ᶠ[𝓝 x] id := by
    filter_upwards [hU] with y hy
    exact f.2 y (le_of_lt hy)
  exact (h.iteratedFDeriv ℝ k).eq_of_nhds

lemma tendstoUniformly_jet (F : ℝ × E n → E n) (hF : ContDiff ℝ ∞ F)
    (g : Set.Icc (0 : ℝ) 1 → DiffDisk n) (hg : ∀ t x, (g t).1 x = F ((t : ℝ), x)) (k : ℕ)
    (t₀ : Set.Icc (0 : ℝ) 1) :
    TendstoUniformly (fun t x => iteratedFDeriv ℝ k ((g t).1 : E n → E n) x)
      (iteratedFDeriv ℝ k ((g t₀).1 : E n → E n)) (𝓝 t₀) := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨v, hv, hvε⟩ := (isCompact_closedBall (0 : E n) 1).mem_uniformity_of_prod
    (f := fun (t : ℝ) (x : E n) => iteratedFDeriv ℝ k (fun y => F (t, y)) x)
    (s := Set.Icc (0 : ℝ) 1) (continuous_slice F hF k).continuousOn t₀.2
    (Metric.dist_mem_uniformity hε)
  have hv' : Subtype.val ⁻¹' v ∈ 𝓝 t₀ := preimage_coe_mem_nhds_subtype.2 hv
  filter_upwards [hv'] with t ht x
  by_cases hx : ‖x‖ ≤ 1
  · have e1 : ((g t).1 : E n → E n) = fun y => F ((t : ℝ), y) := funext (hg t)
    have e0 : ((g t₀).1 : E n → E n) = fun y => F ((t₀ : ℝ), y) := funext (hg t₀)
    rw [e1, e0, dist_comm]
    exact hvε t ht x (mem_closedBall_zero_iff.2 hx)
  · have hx' : 1 < ‖x‖ := not_le.1 hx
    rw [iteratedFDeriv_eq_id _ k x hx', iteratedFDeriv_eq_id _ k x hx', dist_self]
    exact hε

end SmaleDiffS4.S4_B

theorem solution (n : ℕ) (F : ℝ × E n → E n) (hF : ContDiff ℝ ∞ F)
    (g : Set.Icc (0 : ℝ) 1 → DiffDisk n) (hg : ∀ t x, (g t).1 x = F ((t : ℝ), x)) :
    Continuous g := by
  apply continuous_induced_rng.2
  apply continuous_pi
  intro k
  apply continuous_iff_continuousAt.2
  intro t₀
  change Tendsto (fun t => diskJet n (g t) k) (𝓝 t₀) (𝓝 (diskJet n (g t₀) k))
  rw [UniformFun.tendsto_iff_tendstoUniformly]
  exact SmaleDiffS4.S4_B.tendstoUniformly_jet F hF g hg k t₀
