-- Prove2me | solution 1 for PI.StabBigW.sum_mid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:33:27.034935+00:00
-- url     : https://prove2.me/submissions/18066f8d-764b-4ace-a5c7-c82cc5645706

import Definitions.Def_Formalism_PeriodIntegrals_StabBig
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LargeStabilizerInverse_GLeftInv
import Theorems.Thm_PI_StabBigW_wI_val
import Theorems.Thm_PI_StabBigW_wI_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.StabBigW
open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts
variable {k r : ℕ}
namespace PI.StabBigW
theorem _root_.solution (f : Fin (2 * r + k + 1) → ℂ)
    (hf : ∀ m : Fin (2 * r + k + 1), (m.val < r ∨ r + k < m.val) → f m = 0) :
    ∑ m, f m = ∑ s : Fin (k + 1), f (wI k r s) := by
  have himg : ∑ s : Fin (k + 1), f (wI k r s) = ∑ m ∈ Finset.univ.image (wI k r), f m :=
    (Finset.sum_image (fun u _ t _ h => wI_inj h)).symm
  rw [himg]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro m _ hm
  apply hf
  by_contra hc
  apply hm
  have hml := m.isLt
  rw [Finset.mem_image]
  refine ⟨⟨m.val - r, by omega⟩, Finset.mem_univ _, ?_⟩
  ext
  simp only [wI_val]
  omega
end PI.StabBigW
