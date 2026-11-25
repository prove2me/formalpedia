-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.gauss_height_add_of_sphere
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:31:17.785216+00:00
-- url     : https://prove2.me/submissions/9778f282-8eaf-4554-b59f-27ac1e6cc478

import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussAbsMulOfMonomialOrder
import Definitions.Def_ReciprocityTheory_SemistableReduction_LagrangeIdealLiftsFact
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_height_mul_multihomogeneous
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_height_const_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory NumberField
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (hInt : SphereLogIntegrableStatement) : HeightAdditiveStatement := by
  intro K _ _ B n a a' f g hn hf hg haf hbg
  refine ⟨gauss_height_mul_multihomogeneous hInt B n a a' f g hf hg haf hbg, fun c hc => ?_⟩
  have hC : IsMultiHomogeneous (fun _ : Fin B => 0) (MvPolynomial.C c : MvPolynomial (Fin B × Fin n) K) := by
    intro s hs b
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hs
    split_ifs at hs with h
    · subst h; simp
    · exact absurd rfl hs
  have hC0 : (MvPolynomial.C c : MvPolynomial (Fin B × Fin n) K) ≠ 0 := by
    rwa [Ne, MvPolynomial.C_eq_zero]
  rw [gauss_height_mul_multihomogeneous hInt B n _ a _ f hC0 hf hC haf, gauss_height_const_eq_zero B n hn c hc, zero_add]
end ReciprocityTheory.MultiplicativeHeights
