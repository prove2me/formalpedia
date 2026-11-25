-- Prove2me | solution 1 for UpperTheory.Top.exists_pageN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:46:52.352713+00:00
-- url     : https://prove2.me/submissions/9323ba51-c58d-4555-a641-6b65934044d5

import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_ExistsPageN

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open UpperTheory UpperTheory.Top
open Formalism.HC
namespace UpperTheory.Top
theorem _root_.solution (eps : ℝ) (he : 0 < eps) : ∃ e : ℝ → ℕ, ∀ x ≥ (1 : ℝ), PageN eps x (e x) := by
  have : ∀ x : ℝ, ∃ e : ℕ, x ≥ 1 → PageN eps x e := by
    intro x
    by_cases hx : x ≥ 1
    · have h1 : (1 : ℝ) ≤ x ^ (2 + 8 * eps) := Real.one_le_rpow hx (by linarith)
      obtain ⟨n, a, b⟩ := exists_nat_pow_near h1 (by norm_num : (1 : ℝ) < 2)
      refine ⟨n + 1, fun _ => ⟨b.le, ?_⟩⟩
      rw [pow_succ]; linarith
    · exact ⟨0, fun h => absurd h hx⟩
  choose e he using this
  exact ⟨e, he⟩
end UpperTheory.Top
