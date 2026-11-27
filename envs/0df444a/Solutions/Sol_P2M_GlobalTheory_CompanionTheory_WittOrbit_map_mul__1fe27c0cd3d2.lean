-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_WittOrbit_map_mul__1fe27c0cd3d2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:51:02.417811+00:00
-- url     : https://prove2.me/submissions/f26b7a37-e22f-4bef-a08d-1b5646a9b6a8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_OrderOKOneInert
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_CharacterAugmentationSubspaceQuotientActionTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix ValuativeRel NumberField IsDedekindDomain
open scoped TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WittOrbit
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E} {A : Subring E}
namespace GlobalTheory.CompanionTheory.WittOrbit
theorem _root_.solution {l m n : Type} [Fintype m] (X : Matrix l m E) (Y : Matrix m n E) :
    (X * Y).map c = X.map c * Y.map c :=
  Matrix.map_mul
end GlobalTheory.CompanionTheory.WittOrbit
