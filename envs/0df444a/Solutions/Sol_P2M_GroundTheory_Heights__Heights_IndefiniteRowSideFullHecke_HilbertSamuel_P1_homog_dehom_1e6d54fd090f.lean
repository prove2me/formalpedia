-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_P1_homog_dehom_1e6d54fd090f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:29:46.712288+00:00
-- url     : https://prove2.me/submissions/74868182-8aa4-46e9-b8c2-1014b9f61f17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_FderivFderivLogRho
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_FirstPointNeSecondPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_P1_sum_twoPoint_84780d96d978
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_P1_dehom_monomial_9b7f944b9b7a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_P1_homog_add_f1425c4829bc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_P1_homog_zero_fd50f88d740d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_P1_homog_C_mul_X_pow_8f857c843697
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_P1_finsupp_twoPoint_eq_ea2dce68b528

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.P1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.P1
theorem _root_.solution {f : MvPolynomial J2 ℤ} {d : ℕ} (hf : f.IsHomogeneous d) :
    homog (dehom f) d = f := by
  let H : Polynomial ℤ →+ MvPolynomial J2 ℤ :=
    { toFun := fun p ↦ homog p d, map_zero' := homog_zero d, map_add' := fun p q ↦ homog_add p q d }
  have key : ∀ m ∈ f.support, H (dehom (monomial m (f.coeff m))) = monomial m (f.coeff m) := by
    intro m hm
    have hdeg : m p0 + m p1 = d := by
      have := hf (mem_support_iff.mp hm)
      simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one] at this
      rw [Finsupp.sum_fintype _ _ (by simp), sum_twoPoint] at this
      exact this
    conv_lhs => rw [finsupp_twoPoint_eq m]
    rw [dehom_monomial]
    change homog _ d = _
    rw [homog_C_mul_X_pow _ (by omega), show d - m p1 = m p0 by omega, ← finsupp_twoPoint_eq m]
  conv_lhs => rw [f.as_sum]
  change H (dehom (∑ m ∈ f.support, monomial m (f.coeff m))) = _
  rw [map_sum, map_sum]
  conv_rhs => rw [f.as_sum]
  exact Finset.sum_congr rfl key
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.P1
