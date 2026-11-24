-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowFormExtend_sum_coordPoly_903079f12110
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:15.527354+00:00
-- url     : https://prove2.me/submissions/2404d6d1-a454-493d-9e02-d408e1b469e2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormExtend
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_coeff_coordPoly_539797cde10d

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
open GroundTheory.Heights₂.Heights.ChowFormExtend
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {Y : Type*}
variable {β : Type*} [DecidableEq β]
namespace GroundTheory.Heights₂.Heights.ChowFormExtend
theorem _root_.solution (b : Module.Basis β K L) (p : MvPolynomial Y L) :
    ∑ c ∈ coordSupport b p, C (b c) * map (algebraMap K L) (coordPoly (b.coord c) p) = p := by
  ext m
  rw [coeff_sum]
  simp_rw [coeff_C_mul, coeff_map, coeff_coordPoly, Module.Basis.coord_apply, mul_comm (b _),
    ← Algebra.smul_def]
  conv_rhs => rw [← b.linearCombination_repr (coeff m p)]
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  symm
  apply Finset.sum_subset
  · intro c hc
    have hm : m ∈ p.support := by
      rw [mem_support_iff]
      intro h0
      rw [h0, map_zero] at hc
      simp at hc
    exact Finset.mem_biUnion.2 ⟨m, hm, hc⟩
  · intro c _ hc
    rw [Finsupp.notMem_support_iff.1 hc, zero_smul]
end GroundTheory.Heights₂.Heights.ChowFormExtend
