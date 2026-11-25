-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MahlerSection_hypotheses_inhabited_066629c10381
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:01:29.447817+00:00
-- url     : https://prove2.me/submissions/20fe4c67-a0ad-48d9-8734-b74813df830a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isProjPrime_point_e4b734f59300
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isMultiHomog_point_50a43e297f77
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_linForm_one_not_mem_point_805b757dbb4c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isChowFormCycle_point_beac62e59d4d

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
open MvPolynomial MeasureTheory NumberField
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace MahlerSection
theorem _root_.solution :
    (∀ W ∈ (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 1).support, IsProjPrime W) ∧
      IsChowFormCycle (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 1) (0 + 1) (X (0, 0)) ∧
      IsMultiHomog 1 (X (0, 0) : MvPolynomial (Fin (0 + 1) × Fin 1) ℂ) ∧
      (∀ W ∈ (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 1).support,
        linForm (fun _ => (1 : ℂ)) ∉ W) := by
  have hs : (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 1).support = {⊥} :=
    Finsupp.support_single _ one_ne_zero
  refine ⟨?_, isChowFormCycle_point ℂ, isMultiHomog_point ℂ, ?_⟩
  · intro W hW
    rw [hs, Finset.mem_singleton] at hW
    subst hW
    exact isProjPrime_point ℂ
  · intro W hW
    rw [hs, Finset.mem_singleton] at hW
    subst hW
    exact linForm_one_not_mem_point ℂ
end MahlerSection
end GroundTheory.Heights₂.Heights
