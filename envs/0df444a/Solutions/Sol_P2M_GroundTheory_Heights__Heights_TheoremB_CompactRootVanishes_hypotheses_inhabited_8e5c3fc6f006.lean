-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TheoremB_CompactRootVanishes_hypotheses_inhabited_8e5c3fc6f006
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:50:20.315888+00:00
-- url     : https://prove2.me/submissions/bbbf7130-5bab-4ac7-bb2c-2dca2c06c297

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_antisymDelta_mul_vanishes_02d963608782
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_antisymSample_mem_5e7a0459a761


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.TheoremB
open MvPolynomial Finset
variable (d : IndexData)
namespace GroundTheory.Heights₂.Heights.TheoremB
namespace CompactRootVanishes
theorem _root_.solution :
    antisymSample ∈ vSpace d2 ∧ antisymSample ≠ 0 ∧
      ((⟨0, by norm_num⟩ : Fin d2.N) < ⟨1, by norm_num⟩ ∧ (0 < d2.j ↔ 1 < d2.j)) ∧
      antisymSample = antisymDelta (Fin d2.f) d2.N * ∑ p : Idx d2, X p ∧
      ∀ (τ : Fin d2.f) (a b : Fin d2.N), IsCross d2 a b →
        ∃ O : Set (Weight d2), IsOpen O ∧ (O ∩ rootHyperplane d2 τ a b).Nonempty ∧
          ∀ x ∈ O ∩ rootHyperplane d2 τ a b, eval x (antisymSample : LamPoly d2) = 0 := by
  refine ⟨antisymSample_mem.1, antisymSample_mem.2, ⟨by decide, by decide⟩, rfl, ?_⟩
  intro τ a b hab
  exact antisymDelta_mul_vanishes (Fin 1) 3 2 _ τ a b hab.1 hab.2
end CompactRootVanishes
end GroundTheory.Heights₂.Heights.TheoremB
