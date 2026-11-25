-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.length_loc_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:45:22.953388+00:00
-- url     : https://prove2.me/submissions/d2294913-8905-44cf-b2cb-2bcc6bfb7a86

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_LengthLocQuotEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
variable {R : Type*} [CommRing R]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {M₀ M₁ M₂ : Type*} [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup M₂]
    [Module R M₀] [Module R M₁] [Module R M₂] (g : M₀ →ₗ[R] M₁) (h : M₁ →ₗ[R] M₂)
    (hg : Function.Injective g) (hh : Function.Surjective h) (ex : Function.Exact g h)
    (P : Ideal R) [P.IsPrime] :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M₁) =
      Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M₀) +
        Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M₂) := by
  exact Module.length_eq_add_of_exact _ _ (LocalizedModule.map_injective _ g hg)
    (LocalizedModule.map_surjective _ h hh) (LocalizedModule.map_exact _ g h ex)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
