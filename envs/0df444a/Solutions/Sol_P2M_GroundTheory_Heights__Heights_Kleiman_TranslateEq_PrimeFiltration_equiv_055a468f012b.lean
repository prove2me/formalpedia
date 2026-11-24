-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_PrimeFiltration_equiv_055a468f012b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:34.941289+00:00
-- url     : https://prove2.me/submissions/52375e8c-2ab3-44fe-b722-59c924bba661

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealIsMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_EqZeroOrIsHomogeneousOfMemPolyPiece

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
noncomputable section
variable (S : Type) [CommRing S] (N : ℕ)
variable {M : Type} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
namespace PrimeFiltration
theorem _root_.solution (G : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M) (F : IndefiniteRowSideFullHecke.Kleiman.PrimeFiltration S N G) :
    (primeFiltEquiv S N G F).n = F.n ∧ HEq (primeFiltEquiv S N G F).step F.step ∧
      HEq (primeFiltEquiv S N G F).gen F.gen ∧ HEq (primeFiltEquiv S N G F).deg F.deg ∧
      HEq (primeFiltEquiv S N G F).prime F.prime :=
  ⟨rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩
end PrimeFiltration
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
