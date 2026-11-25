-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_exists_ne_zero_smul_mem_of_span_eq_top_cc22f24e7b75
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:05:19.395158+00:00
-- url     : https://prove2.me/submissions/dcb45d10-a59b-429d-8a6e-84fec5bf6bad

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmulMemOfSpanEqTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PLatticesAgree
import Theorems.Thm_UpperTheory_Reformulated_B_SmulMemOfSpanEqTop_exists_ne_zero_smul_mem_of_span_eq_top


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
variable {A : Type} [CommRing A] [IsDomain A]
  {K : Type} [Field K] [Algebra A K] [IsFractionRing A K]
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution (M : Submodule A V)
    (hM : Submodule.span K (M : Set V) = ⊤) (v : V) : ∃ d : A, d ≠ 0 ∧ d • v ∈ M :=
  _root_.UpperTheory.Reformulated.B.SmulMemOfSpanEqTop.exists_ne_zero_smul_mem_of_span_eq_top M hM v
end GroundTheory.Heights₂.Heights.Model
