-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.UUA.cubN_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:11:18.662808+00:00
-- url     : https://prove2.me/submissions/1be7569b-f830-40d9-bdef-a8d017528278

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPowAlg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CubicNormMulIdentity
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_UUA_cubic_norm_mul_identity
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_N_split


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
    cubN θ k a B x * cubN θ k (a * B ^ k) b x * (θ B x b ^ k)⁻¹ = cubN θ k a (B * b) x := by
  have e1 := cubic_norm_mul_identity h k B b x
  have c := h.coc a (B ^ k) (b ^ k) x
  rw [h.N_split k a B x, h.N_split k (a * B ^ k) b x, h.N_split k a (B * b) x, mul_pow, h.s12 B x b]
  apply mul_right_cancel (b := θ (B ^ k) (b ^ k) x * θ B b x ^ k)
  calc _ = (θ (a * B ^ k) (b ^ k) x * θ a (B ^ k) x) *
        (θ (B ^ k) (b ^ k) x * cubN θ k 1 B x * cubN θ k 1 b x) * ((θ B b x ^ k)⁻¹ * θ B b x ^ k) := by
        ac_rfl
    _ = (θ a (B ^ k * b ^ k) x * θ (B ^ k) (b ^ k) x) * (cubN θ k 1 (B * b) x * θ B b x ^ k) := by
        rw [c, e1, inv_mul_cancel, mul_one]
    _ = _ := by ac_rfl
end ReciprocityTheory.ChartRestriction.G.DVR.UUA
