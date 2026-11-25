-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_P1_isMultiHomog_homog_869c5d02b014
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:33:24.366678+00:00
-- url     : https://prove2.me/submissions/4cf9579d-4dd7-46df-a988-34d1115466c7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_FderivFderivLogRho
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_FirstPointNeSecondPoint

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
theorem _root_.solution (p : Polynomial ℤ) (d : ℕ) :
    IsMultiHomog (ι := GlobalTheory (Fin 2)) (homog p d) fun _ ↦ d := by
  intro m hm k
  obtain ⟨i, hi, hmi⟩ := Finset.mem_biUnion.mp (support_sum hm)
  have hm' : m = Finsupp.single p1 i + Finsupp.single p0 (d - i) := by
    by_contra hne
    rw [support_monomial] at hmi
    split_ifs at hmi with hc
    · simp at hmi
    · exact hne (Finset.mem_singleton.mp hmi)
  subst hm'
  obtain ⟨⟩ := k
  have hi' : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [Fin.sum_univ_two]
  simp [Finsupp.single_apply, p0, p1]
  omega
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.P1
