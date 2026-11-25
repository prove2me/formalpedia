-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.UUA.cubic_norm_mul_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:47:32.072327+00:00
-- url     : https://prove2.me/submissions/9c537f6b-0990-4d49-9efa-b41bf1f4662e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPowAlg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CubicNormMulIdentity
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_UUA_four

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
theorem _root_.solution (h : IsCub θ) (k : ℕ) (B b x : A) :
    θ (B ^ k) (b ^ k) x * cubN θ k 1 B x * cubN θ k 1 b x = cubN θ k 1 (B * b) x * θ B b x ^ k := by
  induction k with
  | zero => simp [cubN, h.face]
  | succ k ih =>
    have f := four h (B ^ k) (b ^ k) B b x
    simp only [cubN, one_mul] at ih ⊢
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, pow_succ B, pow_succ b,
      pow_succ (θ B b x), mul_pow]
    apply mul_right_cancel (b := θ (B ^ k) (b ^ k) x)
    calc _ = (θ (B ^ k * B) (b ^ k * b) x * θ (B ^ k) B x * θ (b ^ k) b x) *
          (θ (B ^ k) (b ^ k) x * (∏ i ∈ Finset.range k, θ (B ^ i) B x) *
            ∏ i ∈ Finset.range k, θ (b ^ i) b x) := by ac_rfl
      _ = _ := by rw [f, ih]; ac_rfl
end ReciprocityTheory.ChartRestriction.G.DVR.UUA
