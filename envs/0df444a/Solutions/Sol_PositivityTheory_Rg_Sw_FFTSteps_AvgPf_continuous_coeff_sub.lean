-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.AvgPf.continuous_coeff_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:39:27.896833+00:00
-- url     : https://prove2.me/submissions/8b35b2c0-aa25-48c2-9161-153bf02595ae

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Formalism_RealPlaceAnalysis_InstMeasurableSpaceUJ
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TotalDegreeLinear
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_ContinuousCoeffSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps
open PositivityTheory.Rg.Sw.FFTSteps.AvgPf
variable {ι A B : Type} [Fintype ι]
namespace PositivityTheory.Rg.Sw.FFTSteps.AvgPf
theorem _root_.solution {K : Type} [TopologicalSpace K] (g h : K → Matrix ι ι ℂ) (hg : Continuous g)
    (hh : Continuous h) (p : PV ι A B) : ∀ m, Continuous fun k => coeff m (sub (g k) (h k) p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => intro m; simp only [sub, aeval_C, algebraMap_eq]; exact continuous_const
  | add p q hp hq => intro m; simp only [map_add, coeff_add]; exact (hp m).add (hq m)
  | mul_X p s hp =>
    intro m
    rcases s with x | y
    · have e : ∀ k, coeff m (sub (g k) (h k) (p * X (Sum.inl x))) =
          ∑ j, g k x.1 j * coeff m (sub (g k) (h k) p * X (Sum.inl (j, x.2))) := by
        intro k
        simp only [map_mul, sub, aeval_X, Sum.elim_inl, Finset.mul_sum, coeff_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_left_comm, coeff_C_mul]
      simp only [e, coeff_mul_X']
      refine continuous_finsetSum _ fun j _ => ?_
      refine (((continuous_apply j).comp ((continuous_apply x.1).comp hg))).mul ?_
      split_ifs
      · exact hp _
      · exact continuous_const
    · have e : ∀ k, coeff m (sub (g k) (h k) (p * X (Sum.inr y))) =
          ∑ j, h k y.1 j * coeff m (sub (g k) (h k) p * X (Sum.inr (j, y.2))) := by
        intro k
        simp only [map_mul, sub, aeval_X, Sum.elim_inr, Finset.mul_sum, coeff_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_left_comm, coeff_C_mul]
      simp only [e, coeff_mul_X']
      refine continuous_finsetSum _ fun j _ => ?_
      refine (((continuous_apply j).comp ((continuous_apply y.1).comp hh))).mul ?_
      split_ifs
      · exact hp _
      · exact continuous_const
end PositivityTheory.Rg.Sw.FFTSteps.AvgPf
