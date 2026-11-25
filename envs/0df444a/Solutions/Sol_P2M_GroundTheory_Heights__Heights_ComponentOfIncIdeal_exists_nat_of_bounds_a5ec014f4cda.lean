-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComponentOfIncIdeal_exists_nat_of_bounds_a5ec014f4cda
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:10:40.07752+00:00
-- url     : https://prove2.me/submissions/68024566-c088-46f9-b40d-5817b881bf17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartMax
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PComponentOfIncIdeal

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
open MvPolynomial
open GroundTheory.Heights₂.Heights.ComponentOfIncIdeal
namespace GroundTheory.Heights₂.Heights.ComponentOfIncIdeal
theorem _root_.solution {x : WithBot ℕ∞} {e : ℕ} (h1 : 1 ≤ x) (h2 : x + 1 ≤ ((e + 1 : ℕ) : WithBot ℕ∞)) :
    ∃ k : ℕ, x = (k : WithBot ℕ∞) ∧ 1 ≤ k ∧ k ≤ e := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h1 (by simp)
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      have h3 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) :=
        le_trans (le_add_of_nonneg_right zero_le_one) h2
      have h4 : (⊤ : ℕ∞) ≤ ((e + 1 : ℕ) : ℕ∞) := by exact_mod_cast h3
      exact absurd h4 (by simp)
    | coe k =>
      refine ⟨k, rfl, ?_, ?_⟩
      · exact_mod_cast h1
      · have : ((k + 1 : ℕ) : WithBot ℕ∞) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast h2
        have : k + 1 ≤ e + 1 := by exact_mod_cast this
        omega
end GroundTheory.Heights₂.Heights.ComponentOfIncIdeal
