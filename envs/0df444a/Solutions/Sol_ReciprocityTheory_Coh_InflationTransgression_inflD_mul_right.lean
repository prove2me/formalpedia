-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationTransgression.inflD_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:22:31.404898+00:00
-- url     : https://prove2.me/submissions/bf4cfb75-69c9-4f04-b181-a97e2f830d0a

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_Section
import Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionA
import Theorems.Thm_ReciprocityTheory_Coh_InflationTransgression_cj_coe
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
theorem _root_.solution (a : G) (n : N) : y (a * n) = y a + M.rho a (y n) := by
  have h := hD.right a 1 n
  simp only [D1, one_mul, mul_one, hy1, map_zero] at h
  exact sub_eq_zero.mp (Eq.trans (by abel) (sub_eq_zero.mpr h.symm))
end ReciprocityTheory.Coh.InflationTransgression
