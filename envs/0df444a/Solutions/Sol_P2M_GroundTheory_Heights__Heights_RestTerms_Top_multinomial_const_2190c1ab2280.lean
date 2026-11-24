-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_multinomial_const_2190c1ab2280
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:46.965804+00:00
-- url     : https://prove2.me/submissions/e8be0666-7ef6-412a-beb0-54f7dc463eba

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_BlockValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSameFactorFormula

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
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Top
theorem _root_.solution (f x : ℕ) :
    (Nat.multinomial Finset.univ (fun _ : Fin f => x) : ℚ) =
      ((f * x).factorial : ℚ) / (x.factorial : ℚ) ^ f := by
  have h := Nat.multinomial_spec (Finset.univ : Finset (Fin f)) (fun _ => x)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.sum_const,
    smul_eq_mul] at h
  have hx : (x.factorial : ℚ) ^ f ≠ 0 := pow_ne_zero _ (by exact_mod_cast Nat.factorial_ne_zero x)
  rw [eq_div_iff hx, mul_comm]
  exact_mod_cast h
end GroundTheory.Heights₂.Heights.RestTerms.Top
