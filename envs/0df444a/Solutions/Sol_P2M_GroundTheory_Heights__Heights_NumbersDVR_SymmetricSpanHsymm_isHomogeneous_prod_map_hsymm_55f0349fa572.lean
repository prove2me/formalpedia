-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_SymmetricSpanHsymm_isHomogeneous_prod_map_hsymm_55f0349fa572
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:15:35.095843+00:00
-- url     : https://prove2.me/submissions/86ae54b5-7a85-4c99-8199-900f76c8c206

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Capelli_CompleteHomogeneous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSymmetricSpanHsymm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SymmetricSpanHsymm_isHomogeneous_hsymm_int_5d930b32fefa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial Finset
open GroundTheory.Heights₂.Heights.NumbersDVR.SymmetricSpanHsymm
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.SymmetricSpanHsymm
theorem _root_.solution (t : Multiset ℕ) :
    ((t.map (hsymm σ ℤ)).prod).IsHomogeneous t.sum := by
  induction t using Multiset.induction_on with
  | empty => simpa using isHomogeneous_one σ ℤ
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    exact (isHomogeneous_hsymm_int a).mul ih
end GroundTheory.Heights₂.Heights.NumbersDVR.SymmetricSpanHsymm
