-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_intNum_perm_42358017be47
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:40.847857+00:00
-- url     : https://prove2.me/submissions/cf05452a-73c8-45f6-b798-29bc5bc7a980

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMixedNumberPolynomial
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_mixedDiff_eq_3099f1494d11

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.HilbertSamuel.MixedNumberPolynomial
variable {K : Type*}
variable [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.MixedNumberPolynomial
theorem _root_.solution (F : Type*) [Field F] {ι : K → Type*} (q : Ideal (MRing ι F)) {d : ℕ}
    (σ : Equiv.Perm (Fin d)) (bs : Fin d → K → ℤ) : intNum F q (bs ∘ σ) = intNum F q bs := by
  unfold intNum
  rw [mixedDiff_eq, mixedDiff_eq, (σ.ofFn_comp_perm bs).foldr_eq]
end GroundTheory.Heights₂.Heights.HilbertSamuel.MixedNumberPolynomial
