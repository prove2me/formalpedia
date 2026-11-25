-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_dehom_mul_of_isMultiHomog_db1b22d71340
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:23:18.761881+00:00
-- url     : https://prove2.me/submissions/89645613-b7df-409b-a71c-84bcf0c3d6f2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBridge
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_dehom_monomial_mul_874b10e5036f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.IntNumPoint
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
variable (V : Ideal (MRing ι F)) [V.IsPrime]
variable {V}
variable (i : ∀ k, ι k) (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι F) ∉ V)
include hi
namespace GroundTheory.Heights₂.Heights.NumbersDVR.IntNumPoint
theorem _root_.solution {h : MRing ι F} {a : K → ℕ} (hh : IsMultiHomog h a) :
    dehom V i h * ∏ k, xc V ⟨k, i k⟩ ^ a k = cls V h := by
  conv_rhs => rw [h.as_sum]
  conv_lhs => rw [h.as_sum]
  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hw : Finsupp.weight (blockWeight ι) m = a := hh (mem_support_iff.mp hm)
  have hmon : monomial m (coeff m h) = coeff m h • monomial m (1 : F) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hmon, map_smul, map_smul, smul_mul_assoc, ← hw, dehom_monomial_mul i hi]
end GroundTheory.Heights₂.Heights.NumbersDVR.IntNumPoint
