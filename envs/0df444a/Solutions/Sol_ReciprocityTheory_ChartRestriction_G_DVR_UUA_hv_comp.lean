-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.UUA.hv_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:27:54.949515+00:00
-- url     : https://prove2.me/submissions/e610733f-6232-45d1-86de-4cbbf56e9807

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPowAlg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CubicNormMulIdentity
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_UUA_cubN_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_N_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.UUA
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}
namespace ReciprocityTheory.ChartRestriction.G.DVR.UUA
theorem _root_.solution (h : IsCub θ) (k : ℕ) (a B b x : A) :
    hv θ k a B (x * b) * hv θ k (a * B ^ k) b x = hv θ k a (B * b) x * hv θ k a B b := by
  have n := h.N_add k a B x b
  have m := cubN_mul h k a B b x
  have t : ∀ u v, θ a u v = θ u v a := fun u v => (h.s01 a u v).trans (h.s12 u a v)
  have key : θ a x b * θ a (x * b) B = θ a x (B * b) * θ a b B := by
    have c := h.coc x b B a
    rw [t x b, t (x * b) B, t x (B * b), t b B, mul_comm B b, mul_comm (θ x b a)]
    exact c
  simp only [hv]
  apply mul_right_cancel (b := θ a x b * θ a (x * b) B * θ (a * B ^ k) x b * θ B x b ^ k)
  rw [← m]
  calc _ = (cubN θ k a B (x * b) * θ a x b * θ B x b ^ k) * cubN θ k (a * B ^ k) b x *
        ((θ a (x * b) B)⁻¹ * θ a (x * b) B) * ((θ (a * B ^ k) x b)⁻¹ * θ (a * B ^ k) x b) := by ac_rfl
    _ = θ (a * B ^ k) x b * cubN θ k a B x * cubN θ k a B b * cubN θ k (a * B ^ k) b x := by
        rw [n, inv_mul_cancel, inv_mul_cancel, mul_one, mul_one]
    _ = (cubN θ k a B x * cubN θ k (a * B ^ k) b x * cubN θ k a B b * θ (a * B ^ k) x b) *
        ((θ B x b ^ k)⁻¹ * θ B x b ^ k) * ((θ a x (B * b))⁻¹ * θ a x (B * b)) * ((θ a b B)⁻¹ * θ a b B) := by
        rw [inv_mul_cancel, inv_mul_cancel, inv_mul_cancel, mul_one, mul_one, mul_one]; ac_rfl
    _ = _ := by rw [key]; ac_rfl
end ReciprocityTheory.ChartRestriction.G.DVR.UUA
