-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationTransgression.inflD_of_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:01:49.117607+00:00
-- url     : https://prove2.me/submissions/955cedda-3a1c-4fcf-8986-e1d724c14fd5

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_Section
import Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionA
import Theorems.Thm_ReciprocityTheory_Coh_InflationTransgression_cj_coe
import Theorems.Thm_ReciprocityTheory_Coh_InflationTransgression_inflD_mul_right
import Theorems.Thm_ReciprocityTheory_Coh_InflationTransgression_inflD_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.Coh.InflationTransgression.cj_coe

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationTransgression
open ReciprocityTheory.Gal ReciprocityTheory.Coh
universe u
noncomputable section
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (M : TRep R G) (N : Subgroup G) [N.Normal] (y : G → M.V) (hy1 : y 1 = 0)
  (hD : InflD M N (D1 M y))
include hy1 hD
namespace ReciprocityTheory.Coh.InflationTransgression
theorem _root_.solution (hz : ∀ n : N, y n = 0) :
    (∀ a (n : N), y (a * n) = y a) ∧ ∀ a (n : N), M.rho n (y a) = y a := by
  refine ⟨fun a n => ?_, fun a n => ?_⟩
  · rw [inflD_mul_right M N y hy1 hD a n, hz, map_zero, add_zero]
  · have h := inflD_conj M N y hy1 hD a n
    simp only [hz, map_zero, sub_zero] at h
    exact sub_eq_zero.mp h.symm
end ReciprocityTheory.Coh.InflationTransgression
