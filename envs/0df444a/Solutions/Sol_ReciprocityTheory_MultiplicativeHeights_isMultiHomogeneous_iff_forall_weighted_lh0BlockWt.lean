-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.isMultiHomogeneous_iff_forall_weighted_lh0BlockWt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:31:46.45885+00:00
-- url     : https://prove2.me/submissions/23024131-3593-4e97-88d6-07b9e2e9b0fd

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_AevalIsWeightedHomogeneous
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_weight_lh0BlockWt_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MvPolynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {R : Type*} [CommSemiring R] {B n : ℕ} (a : Fin B → ℕ)
    (f : MvPolynomial (Fin B × Fin n) R) :
    IsMultiHomogeneous a f ↔ ∀ b, IsWeightedHomogeneous (blockIndexWeight b) f (a b) := by
  simp only [IsMultiHomogeneous, IsWeightedHomogeneous, weight_lh0BlockWt_apply, mem_support_iff]
  constructor
  · intro h b d hd
    exact h d hd b
  · intro h s hs b
    exact h b hs
end ReciprocityTheory.MultiplicativeHeights
