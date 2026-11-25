-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartResidueDegree_aeval_mul_of_isHomogeneous_ae2da675df58
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:51:57.357091+00:00
-- url     : https://prove2.me/submissions/834c15ac-ec7f-4e82-8806-0455cdbab946

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartResidueDegree

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartResidueDegree
namespace GroundTheory.Heights₂.Heights.ChartResidueDegree
theorem _root_.solution {F : Type} [Field F] {n : ℕ} {A : Type*} [CommRing A] [Algebra F A]
    {g : MvPolynomial (Fin n) F} {d : ℕ} (hg : g.IsHomogeneous d) (a : A) (x : Fin n → A) :
    aeval (fun m => a * x m) g = a ^ d * aeval x g := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hd := hg (mem_support_iff.mp hs)
  simp only [aeval_monomial, mul_pow]
  rw [Finsupp.prod_mul, Finsupp.prod_pow, Finsupp.prod_pow, Finset.prod_pow_eq_pow_sum, ← hd,
    Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [smul_eq_mul, Pi.one_apply, mul_one]
  ring
end GroundTheory.Heights₂.Heights.ChartResidueDegree
