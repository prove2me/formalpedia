-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagVandermondeDvd_rename_swap_eq_c2b89be0fe92
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:51:59.17569+00:00
-- url     : https://prove2.me/submissions/736c73eb-f2ac-4be4-a186-3df198fcfb36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagVandermondeDvd

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
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.FlagVandermondeDvd
namespace GroundTheory.Heights₂.Heights.RestTerms.FlagVandermondeDvd
theorem _root_.solution (f N : ℕ) (τ : Fin f) (i j : Fin N) :
    (rename (Equiv.swap (τ, i) (τ, j)) : RootRing f N →ₐ[ℚ] RootRing f N) =
      blockPermute f N (Function.update 1 τ (Equiv.swap i j)) := by
  unfold blockPermute
  congr 1
  funext p
  obtain ⟨σ, k⟩ := p
  by_cases hσ : σ = τ
  · subst hσ
    simp only [Function.update_self, Equiv.swap_apply_def, Prod.mk.injEq, true_and]
    split_ifs <;> rfl
  · simp only [Function.update_of_ne hσ, Pi.one_apply, Equiv.Perm.coe_one, id]
    rw [Equiv.swap_apply_of_ne_of_ne] <;> simp [hσ]
end GroundTheory.Heights₂.Heights.RestTerms.FlagVandermondeDvd
