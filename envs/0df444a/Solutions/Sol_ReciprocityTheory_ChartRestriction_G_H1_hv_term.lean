-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.hv_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:07:53.466923+00:00
-- url     : https://prove2.me/submissions/a986e14f-f540-4fba-b194-7ec91f428226

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPowAlg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_cub_rot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}
private lemma prod_range_theta_mul_pow_eq_of_isCub (h : IsCub θ) (k : ℕ) (a M b x : A) :
    ∏ i ∈ Finset.range k, θ (a * M * b ^ i) b x =
      (∏ i ∈ Finset.range k, θ (M * b ^ i) b x) * θ a (M * b ^ k) x * (θ a M x)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, ih]
    have e := h.coc a (M * b ^ k) b x
    rw [← mul_assoc a M (b ^ k), mul_assoc M (b ^ k) b, ← pow_succ b k] at e
    have hA : θ (a * M * b ^ k) b x =
        θ a (M * b ^ (k + 1)) x * θ (M * b ^ k) b x * (θ a (M * b ^ k) x)⁻¹ := by
      rw [← e, mul_inv_cancel_right]
    rw [hA]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
private lemma mul_inv_rearrange_of_two_relations (Q G' G0 P R S T V W : U) (c1 : P * R = T * V) (c2 : T * G0 = W * S) :
    Q * G' * G0⁻¹ * P⁻¹ * R⁻¹ * S = Q * V⁻¹ * (G' * W⁻¹) := by
  have hS : S = W⁻¹ * (T * G0) := by rw [c2, inv_mul_cancel_left]
  have hP : P = T * V * R⁻¹ := by rw [← c1, mul_inv_cancel_right]
  subst hS hP
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, inv_inv]
  abel
end ReciprocityTheory.ChartRestriction.G.H1
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}
namespace ReciprocityTheory.ChartRestriction.G.H1
theorem _root_.solution (h : IsCub θ) (k : ℕ) (a M b x : A) :
    hv θ k (a * M) b x * (θ a M b)⁻¹ * θ a x b = hv θ k M b x * (θ a (M * b ^ k) x * (θ a M (x * b))⁻¹) := by
  have c1 := h.coc a M x b
  have c2 : θ a (M * x) b * θ a M x = θ a M (x * b) * θ a x b := by
    have e := h.coc M x b a
    rw [← cub_rot h a (M * x) b, ← cub_rot h a M x, ← cub_rot h a M (x * b), ← cub_rot h a x b] at e
    exact e
  simp only [hv, cubN]
  rw [prod_range_theta_mul_pow_eq_of_isCub h]
  exact mul_inv_rearrange_of_two_relations _ _ _ _ _ _ _ _ _ c1 c2
end ReciprocityTheory.ChartRestriction.G.H1
