-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BlockSurjectivity_eval_atBlock_972328f14a36
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:48:07.752372+00:00
-- url     : https://prove2.me/submissions/3023fcea-459a-4ecc-9589-631377653c9e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousSepBlock
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_eval_atBlock_X_eea668c7f675

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
open MvPolynomial Module
noncomputable section
open GroundTheory.Heights₂.Heights.BlockSurjectivity
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights.BlockSurjectivity
theorem _root_.solution (k₀ : ι) (w : Cone (fun _ : Unit ↦ n k₀) ℂ) (x : Coord n → ℂ)
    (q : MvPolynomial (Coord n) ℤ) :
    eval x (atBlock k₀ w q) = evalCone (withBlock k₀ (w ()) x) q := by
  induction q using MvPolynomial.induction_on with
  | C a =>
    simp only [evalCone, eval₂_C]
    simp [atBlock, sepBlock]
  | add p q hp hq =>
    rw [map_add (atBlock k₀ w), map_add (eval x), hp, hq]
    simp only [evalCone, eval₂_add]
  | mul_X p v hp =>
    rw [map_mul (atBlock k₀ w), map_mul (eval x), hp, eval_atBlock_X]
    simp only [evalCone, eval₂_mul, eval₂_X]
end GroundTheory.Heights₂.Heights.BlockSurjectivity
