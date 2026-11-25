-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.evNat_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:28:05.660919+00:00
-- url     : https://prove2.me/submissions/4e699389-138d-4b6c-861d-53b7819c6b33

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_IndepPts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_EvNatPf
import Theorems.Thm_Formalism_L2_Pj_frMap_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_evalAt_eq_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z))
    (hA : AllTest Xo c) : EvNat Xo c := by
  intro f hf S T _ _ _ _ _ φ y z hz
  obtain ⟨p, ψ, y', hy'⟩ := hA S y
  have h1 : evR Xo c f y = ψ (f p y') :=
    evalAt_eq_of (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) hWD f hf p ψ y' y hy'
  have h2 : evR Xo c f z = (φ.comp ψ) (f p y') :=
    evalAt_eq_of (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) hWD f hf p (φ.comp ψ) y' z
      (frMap_trans (Xo := Xo) (c := c) _ _ _ ψ φ y' y z hy' hz)
  rw [h2, h1, AlgHom.comp_apply]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
