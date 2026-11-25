-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.gs_dfun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:48:14.46104+00:00
-- url     : https://prove2.me/submissions/97e26363-7348-44e8-a0a0-a310c5339564

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
open AlgebraicGeometry CategoryTheory TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR
variable {Y : Scheme.{0}} (L : LB Y) {n : ℕ} (V : Fin n → Y.Opens) (c : Fin n → L.ι) (hVc : ∀ k, V k ≤ L.U (c k))
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace ReciprocityTheory.ChartRestriction.G.DVR.FlatBC
theorem _root_.solution {f : ∀ k, Γ(Y, V k)} (hf : dfun L V c hVc f = 0) (k l : Fin n) (y : Y) (hk : y ∈ V k) (hl : y ∈ V l) :
    gs (𝟙 Y) y (V k) (f k) = (gm (𝟙 Y) y (L.U (c k) ⊓ L.U (c l)) (L.g (c k) (c l))).val * gs (𝟙 Y) y (V l) (f l) := by
  have e := sub_eq_zero.1 (congrFun (congrFun hf k) l)
  have hy : y ∈ V k ⊓ V l := ⟨hk, hl⟩
  have e2 := congrArg (gs (𝟙 Y) y (V k ⊓ V l)) e
  rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_unit _ y _ hy, gm_res _ y _ hy] at e2
  exact e2
end ReciprocityTheory.ChartRestriction.G.DVR.FlatBC
