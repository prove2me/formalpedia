-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_gradedSpan_gen_mem_90c514e33d20
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:40.870505+00:00
-- url     : https://prove2.me/submissions/74472c37-c78c-41ba-8b58-239b5fefd637

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSerreGraded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
noncomputable section
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution {Ω : Type*} [CommRing Ω] {q r : ℕ} (w : Fin q → Ω) (d : Fin r → ℕ) (t : Fin r → Ω)
    (l : Fin r) (μ : Fin q → ℕ) : t l * ∏ j, w j ^ μ j ∈ gradedSpan w d t (d l + ∑ j, μ j) :=
  AddSubgroup.subset_closure ⟨l, μ, rfl, rfl⟩
end GroundTheory.Heights₂.Heights.HilbertSamuel
