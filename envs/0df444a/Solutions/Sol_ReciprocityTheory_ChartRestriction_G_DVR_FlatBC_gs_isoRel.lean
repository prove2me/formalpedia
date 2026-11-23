-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.gs_isoRel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:28.012799+00:00
-- url     : https://prove2.me/submissions/0d08b8e2-1309-49ea-97a9-2d0269922291

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FlatBCSec

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
theorem _root_.solution {w : LB.Iso L M} {s : LB.Sec L} {s' : LB.Sec M} (h : IsoRel w s s') (i : M.ι) (k : L.ι) (y : Y)
    (hi : y ∈ M.U i) (hk : y ∈ L.U k) :
    gs (𝟙 Y) y (M.U i) (s'.f i) = (gm (𝟙 Y) y ((LB.div M L).U (i, k)) (w.s (i, k))).val * gs (𝟙 Y) y (L.U k) (s.f k) := by
  have hy : y ∈ M.U i ⊓ L.U k := ⟨hi, hk⟩
  have e := congrArg (gs (𝟙 Y) y (M.U i ⊓ L.U k)) (h i k)
  rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy] at e
  rw [e]
  congr 1
  exact gs_unit _ y _ hy _
end ReciprocityTheory.ChartRestriction.G.DVR.FlatBC
