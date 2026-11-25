-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.ev_smulSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:46:36.736336+00:00
-- url     : https://prove2.me/submissions/04a5afad-eb5b-45f4-9530-b211ab709422

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FlatBCSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_mul


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
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {X X' : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of R)) (p' : X' ⟶ Spec (CommRingCat.of S)) (φ : X' ⟶ X)
  (H : IsPullback φ p' p (Spec.map (CommRingCat.ofHom (algebraMap R S))))
omit [Algebra R S]
namespace ReciprocityTheory.ChartRestriction.G.DVR.FlatBC
theorem _root_.solution (L : LB X) {n : ℕ} (V : Fin n → X.Opens) (c : Fin n → L.ι) (hVc : ∀ k, V k ≤ L.U (c k))
    (a : R) (θ : LB.Sec L) (k : Fin n) :
    ev L V c hVc (smulSec p L a θ) k = algX p (V k) a * ev L V c hVc θ k := by
  simp only [ev, smulSec, rs_mul, rs_algX]
end ReciprocityTheory.ChartRestriction.G.DVR.FlatBC
