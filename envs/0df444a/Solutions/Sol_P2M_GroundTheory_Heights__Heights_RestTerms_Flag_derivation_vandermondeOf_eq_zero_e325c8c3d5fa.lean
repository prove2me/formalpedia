-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Flag_derivation_vandermondeOf_eq_zero_e325c8c3d5fa
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:34.575807+00:00
-- url     : https://prove2.me/submissions/2619130e-e59c-412e-bd24-c4e689539144

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_derivation_prod_eq_zero_f8221cfdebfa

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
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Flag
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Flag
theorem _root_.solution {R A M : Type*} [CommSemiring R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M] [Module R M] (D : Derivation R A M) {m : ℕ} (v : Fin m → A) (hv : ∀ i j, D (v i) = D (v j)) :
    D (vandermondeOf v) = 0 := by
  unfold vandermondeOf
  refine derivation_prod_eq_zero D _ _ (fun i _ => derivation_prod_eq_zero D _ _ (fun j _ => ?_))
  rw [map_sub, hv i j, sub_self]
end GroundTheory.Heights₂.Heights.RestTerms.Flag
