-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.gm_wgen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:54:37.917302+00:00
-- url     : https://prove2.me/submissions/b955101c-a157-44e8-8a43-66223d45fe4a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FlatBCSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


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
open TensorProduct
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.FlatBC
variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
open AlgebraicGeometry CategoryTheory TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {Y : Scheme.{0}} {L M : LB Y}
namespace ReciprocityTheory.ChartRestriction.G.DVR.FlatBC
theorem _root_.solution {w : LB.Iso L M} (hw : w.IsGen) (i i' : M.ι) (k k' : L.ι) (y : Y) (hi : y ∈ M.U i) (hi' : y ∈ M.U i')
    (hk : y ∈ L.U k) (hk' : y ∈ L.U k') :
    gm (𝟙 Y) y ((LB.div M L).U (i, k)) (w.s (i, k)) =
      gm (𝟙 Y) y (M.U i ⊓ M.U i') (M.g i i') * (gm (𝟙 Y) y (L.U k ⊓ L.U k') (L.g k k'))⁻¹ *
        gm (𝟙 Y) y ((LB.div M L).U (i', k')) (w.s (i', k')) := by
  have hy : y ∈ (LB.div M L).U (i, k) ⊓ (LB.div M L).U (i', k') := ⟨⟨hi, hk⟩, ⟨hi', hk'⟩⟩
  have e := congrArg (gm (𝟙 Y) y _) (hw (i, k) (i', k'))
  rw [gm_res _ y _ hy, map_mul, gm_res _ y _ hy] at e
  rw [e]
  congr 1
  show gm (𝟙 Y) y _ (res _ (M.g i i') * (res _ (L.g k k'))⁻¹) = _
  erw [map_mul, map_inv, gm_res _ y _ hy, gm_res _ y _ hy]
end ReciprocityTheory.ChartRestriction.G.DVR.FlatBC
