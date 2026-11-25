-- Prove2me | solution 1 for PI.FJMB.edge_succ_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:38:34.891534+00:00
-- url     : https://prove2.me/submissions/8d54e95a-5dd8-43c4-8b33-8a231aa91f0d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurElim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Classical
open PI PI.FJMB
variable {σ : Type*}
variable {m n : ℕ} (ι : Fin (m + 1) × Fin (n + 1) → σ) (hι : Function.Injective ι)
include hι
namespace PI.FJMB
theorem _root_.solution (i : Fin m) (k : Fin n) : ι (i.succ, k.succ) ∉ edge ι := by
  rintro (⟨l, hl⟩ | ⟨j, hj⟩)
  · have := hι hl; simp at this; exact Fin.succ_ne_zero _ this.1.symm
  · have := hι hj; simp at this; exact Fin.succ_ne_zero _ this.2.symm
end PI.FJMB
