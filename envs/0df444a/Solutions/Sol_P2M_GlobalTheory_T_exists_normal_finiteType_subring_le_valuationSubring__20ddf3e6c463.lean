-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_normal_finiteType_subring_le_valuationSubring__20ddf3e6c463
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:54:16.316292+00:00
-- url     : https://prove2.me/submissions/2ec6404b-59ad-482b-8644-ffa76fb2b053

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNormalFiniteTypeSubringLeValuationSubringA
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNormalFiniteTypeSubringLeValuationSubringAStatement
import Theorems.Thm_GlobalTheory_exists_normal_finiteType_subring_le_valuationSubring


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {κ : Type} [Field κ] [Algebra ℂ κ] (V : ValuationSubring κ) (T : Finset κ), (∀ a : ℂ, algebraMap ℂ κ a ∈ V) → (∀ x ∈ T, x ∈ V) → (∀ f : κ, ∃ a ∈ Algebra.adjoin ℂ (T : Set κ), ∃ b ∈ Algebra.adjoin ℂ (T : Set κ), b ≠ 0 ∧ f * b = a) → ∃ (R : Subring κ) (hcR : ∀ a : ℂ, algebraMap ℂ κ a ∈ R), ((algebraMap ℂ κ).codRestrict R hcR).FiniteType ∧ (∀ x ∈ T, x ∈ R) ∧ R ≤ V.toSubring ∧ IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsFractionRing R κ := by
  first | exact @GlobalTheory.exists_normal_finiteType_subring_le_valuationSubring | exact GlobalTheory.exists_normal_finiteType_subring_le_valuationSubring | (intros; apply GlobalTheory.exists_normal_finiteType_subring_le_valuationSubring <;> assumption)
end _root_.GlobalTheory.T
