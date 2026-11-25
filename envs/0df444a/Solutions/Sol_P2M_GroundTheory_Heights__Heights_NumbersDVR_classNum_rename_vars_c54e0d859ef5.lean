-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_classNum_rename_vars_c54e0d859ef5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:26:49.260316+00:00
-- url     : https://prove2.me/submissions/59061248-baa7-45bc-8989-e04c25f6a593

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_classNum_monomial_eq_0ee7393f4501
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_classList_mapDomain_596b3c63997b

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
open MvPolynomial
noncomputable section
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {σ τ : Type*} [DecidableEq σ] [DecidableEq τ] (cls : τ → K → ℤ) (φ : σ → τ) (H : MvPolynomial σ ℤ)
    (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    classNum cls (rename φ H) Q W = classNum (cls ∘ φ) H Q W := by
  induction H using MvPolynomial.induction_on' with
  | monomial μ c => rw [rename_monomial, classNum_monomial_eq, classNum_monomial_eq, classList_mapDomain]
  | add p q hp hq => rw [map_add, classNum_add_poly, classNum_add_poly, hp, hq]
end GroundTheory.Heights₂.Heights.NumbersDVR
