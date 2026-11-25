-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.isoRel_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:48:25.55339+00:00
-- url     : https://prove2.me/submissions/05a92216-dbdb-4a12-8ddb-b471f7c1069c

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
theorem _root_.solution {L M : LB X} {w : LB.Iso L M} {s : LB.Sec L} {s' : LB.Sec M} (h : IsoRel w s s') (a : R) :
    IsoRel w (smulSec p L a s) (smulSec p M a s') := fun i k => by
  have e := h i k
  show rs _ (_ * _) = _ * rs _ (_ * _)
  rw [rs_mul, rs_mul, rs_algX, rs_algX]
  simp only [rs] at e ⊢
  rw [e]
  exact mul_left_comm _ _ _
end ReciprocityTheory.ChartRestriction.G.DVR.FlatBC
