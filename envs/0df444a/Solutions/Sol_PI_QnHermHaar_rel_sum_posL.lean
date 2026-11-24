-- Prove2me | solution 1 for PI.QnHermHaar.rel_sum_posL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:24:54.484959+00:00
-- url     : https://prove2.me/submissions/0dfa6c58-e307-44a4-94a3-d9d5261ab85e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_RestrictedGramHermitianInvolution
import Theorems.Thm_PI_QnHermHaar_rel_posL_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.QnHermHaar
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
namespace PI.QnHermHaar
theorem _root_.solution (k r : ℕ) (i : Fin (r + 1)) (F : Fin (2 * r + k + 1) → ℂ)
    (hF : ∀ a : Fin (2 * r + k + 1), (a.val < i.val ∨ 2 * r + k < a.val + i.val) → F a = 0) :
    ∑ a, F a = ∑ l : Fin (mdim k r i), F (posL k r i l) := by
  rw [← Finset.sum_image (s := Finset.univ) (g := posL k r i)
    (fun x _ y _ h => rel_posL_injective k r i h)]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro a _ ha
  apply hF
  by_contra hc
  push_neg at hc
  apply ha
  have hi := i.isLt
  refine Finset.mem_image.2 ⟨⟨a.val - i.val, ?_⟩, Finset.mem_univ _, ?_⟩
  · show a.val - i.val < 2 * (r - i.val) + k + 1
    omega
  · apply Fin.ext
    show a.val - i.val + i.val = a.val
    omega
end PI.QnHermHaar
