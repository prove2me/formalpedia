-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_low_dPoly_22ca28e4b827
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:53:14.659689+00:00
-- url     : https://prove2.me/submissions/6295f795-871f-4497-8886-52fdbc97b9fa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMixedNumberPolynomial
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_low_add_ba467e24cca8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_low_mono_bed7d4e772fa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_low_dPoly_monomial_0e1b8897bee7

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
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.MixedNumberPolynomial
theorem _root_.solution (b : K → ℤ) (p : MvPolynomial K ℚ) : Low (dPoly b p) p.totalDegree := by
  have hsum : dPoly b p = ∑ s ∈ p.support, dPoly b (monomial s (coeff s p)) := by
    simp only [dPoly]
    conv_lhs => rw [p.as_sum]
    rw [map_sum, ← Finset.sum_sub_distrib]
  rw [hsum]
  refine Finset.sum_induction _ (fun A => Low A p.totalDegree) (fun _ _ => low_add)
    (Or.inl rfl) (fun s hs => low_mono (low_dPoly_monomial b s _) ?_)
  exact (totalDegree_monomial_le s _).trans (le_totalDegree hs)
end GroundTheory.Heights₂.Heights.HilbertSamuel.MixedNumberPolynomial
