-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RootAnchorNonzeroAlt_eval_homForm_698e79acdc72
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:14:15.119998+00:00
-- url     : https://prove2.me/submissions/60cadad0-1f61-427c-b608-f9e444b5d307

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootAnchorNonzero

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.RootAnchorNonzeroAlt
namespace GroundTheory.Heights₂.Heights.RootAnchorNonzeroAlt
theorem _root_.solution {f j m : ℕ} {q : Polynomial ℤ} (hq : q.Monic) {τ : Fin f} {I : PlIdx j m}
    {z : (Σ _ : Fin f, PlIdx j m) → ℂ} (hz : z ⟨τ, plAnchor j m⟩ = 0) :
    eval z (map (Int.castRingHom ℂ) (homForm q τ I)) = z ⟨τ, I⟩ ^ q.natDegree := by
  simp only [homForm, map_sum, map_mul, map_pow, map_C, map_X, eval_C, eval_X, hz]
  rw [Finset.sum_range_succ, Finset.sum_eq_zero]
  · simp [hq.coeff_natDegree]
  · intro k hk
    have : q.natDegree - k ≠ 0 := by have := Finset.mem_range.mp hk; omega
    simp [zero_pow this]
end GroundTheory.Heights₂.Heights.RootAnchorNonzeroAlt
