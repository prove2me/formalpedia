-- Prove2me | solution 1 for PI.QnHermHaar.pull1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:11:08.361555+00:00
-- url     : https://prove2.me/submissions/7c560bb3-1cc5-4a3a-b235-98857d8428ed

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_SumFourCommVersion
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_GeneralSecondMinorExpansion

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
open Formalism.REAL Formalism.FourierDecayAlt.Q
namespace PI.QnHermHaar
theorem _root_.solution {A : Type*} [AddCommMonoid A] {m : ℕ} (g : Fin m → Fin m → Fin m → A) :
    ∑ a, ∑ b, ∑ c, g a b c = ∑ c, ∑ a, ∑ b, g a b c := by
  calc ∑ a, ∑ b, ∑ c, g a b c = ∑ a, ∑ c, ∑ b, g a b c :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, g a b c := Finset.sum_comm
end PI.QnHermHaar
