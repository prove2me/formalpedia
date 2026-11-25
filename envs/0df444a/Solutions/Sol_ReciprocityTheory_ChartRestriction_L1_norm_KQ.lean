-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.norm_KQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:55:21.61123+00:00
-- url     : https://prove2.me/submissions/7fc0558f-8c09-4329-b00f-66106ec1469e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQuadInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModPrincNorm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_sqK_mul_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {d : ℕ} (hd : 0 < d) (z : KQ d) (p q : ℚ) (h : (z : ℂ) = p + q * sqD d) :
    Algebra.norm ℚ z = p ^ 2 + d * q ^ 2 := by
  have h0 : bKQ hd 0 = 1 := by simp [bKQ]
  have h1 : bKQ hd 1 = sqK d := by simp [bKQ]
  have hz := sqK_decomp z p q h
  have e0 : z * bKQ hd 0 = p • bKQ hd 0 + q • bKQ hd 1 := by
    rw [h0, h1, mul_one]; exact hz
  have e1 : z * bKQ hd 1 = (-(d : ℚ) * q) • bKQ hd 0 + p • bKQ hd 1 := by
    rw [h0, h1, hz, add_mul, smul_mul_assoc, smul_mul_assoc, sqK_mul_self, one_mul]
    simp only [Algebra.smul_def, mul_one]
    push_cast
    ring
  rw [Algebra.norm_eq_matrix_det (bKQ hd), Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, e0, e1, map_add, map_smul, Module.Basis.repr_self]
  simp
  ring
end ReciprocityTheory.ChartRestriction.L1
