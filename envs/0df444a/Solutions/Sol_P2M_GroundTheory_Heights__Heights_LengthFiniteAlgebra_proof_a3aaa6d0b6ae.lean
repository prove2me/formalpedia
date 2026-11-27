-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_proof_a3aaa6d0b6ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:03:19.531035+00:00
-- url     : https://prove2.me/submissions/44788de0-efa1-44d2-a4d6-22814b4156c1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PLengthFiniteAlgebra
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_length_eq_finsum_localization_30845086f09f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_ord_mul_length_4198e6736b99
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_finsum_reindex_9a25be9a211b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open IsLocalRing
noncomputable section
open LengthFiniteAlgebra
namespace GroundTheory.Heights₂.Heights
namespace LengthFiniteAlgebra
theorem _root_.solution : LengthFiniteAlgebra.Statement := by
  intro O B _ _ _ _ _ _ θ
  have hr : LinearMap.range (LinearMap.mulLeft O θ) = (Ideal.span {θ}).restrictScalars O := by
    ext x
    simp [Ideal.mem_span_singleton', mul_comm]
  have : Module.Finite O (B ⧸ Ideal.span {θ}) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ O _).toLinearMap Ideal.Quotient.mk_surjective
  rw [(Submodule.quotEquivOfEq _ _ hr ≪≫ₗ
      Submodule.Quotient.restrictScalarsEquiv O (Ideal.span {θ})).length_eq,
    length_eq_finsum_localization, finsum_reindex]
  congr 1
  funext P
  exact (ord_mul_length P.asIdeal θ).symm
end LengthFiniteAlgebra
end GroundTheory.Heights₂.Heights
