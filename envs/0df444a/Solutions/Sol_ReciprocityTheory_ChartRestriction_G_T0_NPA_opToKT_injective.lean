-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.NPA.opToKT_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:12:38.194553+00:00
-- url     : https://prove2.me/submissions/4b4af760-529e-4313-a5a9-ec39af02b769

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OpIsDVR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValNorm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormPtsA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPA_oTtoKT_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.T0.NPA
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable {K : Type} [Field K] [NumberField K] (D N : ℕ)
  (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
namespace ReciprocityTheory.ChartRestriction.G.T0.NPA
theorem _root_.solution : Function.Injective (OpToKT D N la) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (laT D N la).primeCompl x
  unfold OpToKT at hx
  rw [IsLocalization.lift_mk'_spec, mul_zero, RingHom.comp_apply] at hx
  have h2 : OTtoKT K D N a = 0 :=
    (injective_iff_map_eq_zero _).mp (IsFractionRing.injective (KTp K D N) (KTf K D N)) _ hx
  have h3 : a = 0 := (injective_iff_map_eq_zero _).mp (oTtoKT_injective D N) _ h2
  subst h3
  exact IsLocalization.mk'_zero _
end ReciprocityTheory.ChartRestriction.G.T0.NPA
