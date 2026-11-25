-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.weight_lh0BlockWt_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:27:22.641614+00:00
-- url     : https://prove2.me/submissions/84481bb5-9341-4065-9388-5159691ef414

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_AevalIsWeightedHomogeneous

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
theorem _root_.solution {B n : ℕ} (b : Fin B) (s : Fin B × Fin n →₀ ℕ) :
    Finsupp.weight (blockIndexWeight (n := n) b) s = ∑ j : Fin n, s (b, j) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [blockIndexWeight, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single b (fun x _ hx => by simp [hx]) (by simp)]
  simp
end ReciprocityTheory.MultiplicativeHeights
