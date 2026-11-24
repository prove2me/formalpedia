-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_withBotENat_lt_of_add_one_le_110602cf25ee
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:45.207914+00:00
-- url     : https://prove2.me/submissions/ec00586f-afac-4d8e-ba7b-42c5e45efb74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialDimBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {a : WithBot ℕ∞} {n : ℕ} (h : a + 1 ≤ (n : WithBot ℕ∞)) :
    a < (n : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : ((⊤ : ℕ∞) + 1 : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast h
      simp at h'
    | coe m =>
      have h' : ((m + 1 : ℕ) : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast h
      have h'' : m + 1 ≤ n := by exact_mod_cast h'
      exact_mod_cast (show m < n by omega)
end GroundTheory.Heights₂.Heights.NumbersDVR
