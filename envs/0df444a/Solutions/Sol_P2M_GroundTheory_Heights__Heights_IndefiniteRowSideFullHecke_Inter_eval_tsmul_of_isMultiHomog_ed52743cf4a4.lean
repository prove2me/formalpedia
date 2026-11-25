-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_eval_tsmul_of_isMultiHomog_ed52743cf4a4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:11:40.228181+00:00
-- url     : https://prove2.me/submissions/e452ed8d-24fe-4ac4-8874-3b385533bcb4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AnalyticResolutionHypothesesProjectiveLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeN
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FourierIntegralBound
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial MeasureTheory Topology Filter Set
open scoped ContDiff
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiHomog)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential MIntegrable locDens)
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution {s : MRing ι ℂ} {a : K → ℕ} (hs : IsMultiHomog s a)
    (c : K → ℂ) (z : MCone ι) :
    eval (tsmul c z) s = (∏ k, c k ^ a k) * eval z s := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw := hs (mem_support_iff.mp hd)
  have hk : ∀ k, ∑ i, d ⟨k, i⟩ = a k := by
    intro k
    rw [← hw]
    simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fintype.sum_sigma,
      GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight, Pi.single_apply]
    rw [Finset.sum_eq_single k (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp
  have hprod : ∏ v, tsmul c z v ^ d v = (∏ k, c k ^ a k) * ∏ v, z v ^ d v := by
    simp only [tsmul, mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, c k ^ d ⟨k, i⟩ = c k ^ a k
    rw [Finset.prod_pow_eq_pow_sum, hk k]
  rw [hprod]
  ring
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
