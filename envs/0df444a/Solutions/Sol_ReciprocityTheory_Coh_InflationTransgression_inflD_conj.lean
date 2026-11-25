-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationTransgression.inflD_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:54:19.902095+00:00
-- url     : https://prove2.me/submissions/53896c8d-6561-4ac0-be8b-cee4ea94ba2a

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_Section
import Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionA
import Theorems.Thm_ReciprocityTheory_Coh_InflationTransgression_cj_coe
import Theorems.Thm_ReciprocityTheory_Coh_InflationTransgression_inflD_mul_right
import Theorems.Thm_ReciprocityTheory_Coh_InflationTransgression_inflD_mul_left
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
theorem _root_.solution (s : G) (n : N) : M.rho s (y (cj N s n)) - y n = M.rho n (y s) - y s := by
  have h1 := inflD_mul_right M N y hy1 hD s (cj N s n)
  have h2 := inflD_mul_left M N y hy1 hD n s
  have he : s * (cj N s n : G) = (n : G) * s := by rw [cj_coe]; group
  rw [he, h2] at h1
  exact sub_eq_zero.mp (Eq.trans (by abel) (sub_eq_zero.mpr h1.symm))
end ReciprocityTheory.Coh.InflationTransgression
