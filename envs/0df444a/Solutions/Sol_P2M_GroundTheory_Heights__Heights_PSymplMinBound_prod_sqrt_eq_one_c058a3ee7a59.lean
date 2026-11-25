-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplMinBound_prod_sqrt_eq_one_c058a3ee7a59
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:46:11.972899+00:00
-- url     : https://prove2.me/submissions/ecfe697e-792d-4c7e-be6e-8e5948cbfd8d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplMinBound

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
open Matrix
open GroundTheory.Heights₂.Heights.PSymplMinBound
namespace GroundTheory.Heights₂.Heights.PSymplMinBound
theorem _root_.solution {ι : Type} [Fintype ι] (lam : ι → ℝ) (hlam : ∀ i, 0 < lam i)
    (hprod : ∏ i, lam i = 1) : ∏ i, Real.sqrt (lam i) = 1 := by
  have hnn : 0 ≤ ∏ i, Real.sqrt (lam i) := Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _
  have hsq : (∏ i, Real.sqrt (lam i)) ^ 2 = 1 := by
    rw [← Finset.prod_pow]
    simp_rw [Real.sq_sqrt (hlam _).le]
    exact hprod
  nlinarith [hsq, hnn]
end GroundTheory.Heights₂.Heights.PSymplMinBound
