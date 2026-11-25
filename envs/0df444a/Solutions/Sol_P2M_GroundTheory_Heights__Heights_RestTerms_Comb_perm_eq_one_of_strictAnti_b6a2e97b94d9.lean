-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Comb_perm_eq_one_of_strictAnti_b6a2e97b94d9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:50:23.967769+00:00
-- url     : https://prove2.me/submissions/84387b06-f4a0-4efd-90c4-5ff5d77b29f1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VandermondeOfEqDet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Comb
open MvPolynomial Finset Equiv
noncomputable section
variable {m : ℕ}
namespace GroundTheory.Heights₂.Heights.RestTerms.Comb
theorem _root_.solution {v : Fin m → ℕ} (hv : StrictAnti v) (σ : Perm (Fin m))
    (h : StrictAnti (v ∘ σ)) : σ = 1 := by
  have hmono : StrictMono σ := by
    intro a b hab
    have := h hab
    simp only [Function.comp_apply] at this
    exact hv.lt_iff_gt.mp this
  have hmono' : StrictMono σ.symm := by
    intro a b hab
    by_contra hc
    push Not at hc
    have := hmono.monotone hc
    simp at this
    exact absurd hab (not_lt.mpr this)
  ext i
  have h1 : i ≤ σ i := hmono.le_apply
  have h2 : i ≤ σ.symm i := hmono'.le_apply
  have h3 : σ i ≤ σ (σ.symm i) := hmono.monotone h2
  simp only [Equiv.apply_symm_apply] at h3
  simp [le_antisymm h3 h1]
end GroundTheory.Heights₂.Heights.RestTerms.Comb
