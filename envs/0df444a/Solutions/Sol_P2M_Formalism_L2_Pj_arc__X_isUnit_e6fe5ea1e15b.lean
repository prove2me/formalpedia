-- Prove2me | solution 1 for P2M_Formalism_L2_Pj_arc__X_isUnit_e6fe5ea1e15b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:45:27.767323+00:00
-- url     : https://prove2.me/submissions/b879abf2-a8e7-454a-9e55-7040f7d27baf

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArcPtX

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
namespace Formalism.L2.Pj
theorem _root_.solution (Dw : Datum H) (K₁ : Type) [Field K₁] : IsUnit (arcι Dw K₁ PowerSeries.X) := by
  have h : IsUnit (HahnSeries.ofPowerSeries ℤ K₁ PowerSeries.X) := by
    rw [isUnit_iff_ne_zero]
    first
      | (rw [HahnSeries.ofPowerSeries_X]; exact HahnSeries.single_ne_zero one_ne_zero)
      | (intro h0
         exact PowerSeries.X_ne_zero ((map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective).mp h0))
      | (simp; done)
  exact (h.map (MvPolynomial.C (σ := ArcLt Dw))).map
    (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) (ArcS Dw K₁))
end Formalism.L2.Pj
