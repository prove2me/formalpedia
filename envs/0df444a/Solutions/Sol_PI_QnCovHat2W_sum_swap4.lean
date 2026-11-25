-- Prove2me | solution 1 for PI.QnCovHat2W.sum_swap4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:15:12.9665+00:00
-- url     : https://prove2.me/submissions/70d01a85-7636-4eac-beba-64d092845fb3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_GGEq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_SumSgnLProdCol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open PI PI.QnCovHat2W
open Formalism.REAL Formalism.FourierDecayAlt.Q
namespace PI.QnCovHat2W
theorem _root_.solution {ι κ : Type*} [Fintype ι] [Fintype κ] {M : Type*} [AddCommMonoid M]
    (f : ι → ι → κ → κ → M) :
    ∑ c, ∑ d, ∑ x, ∑ y, f c d x y = ∑ x, ∑ y, ∑ c, ∑ d, f c d x y := by
  calc ∑ c, ∑ d, ∑ x, ∑ y, f c d x y = ∑ c, ∑ x, ∑ d, ∑ y, f c d x y :=
        Finset.sum_congr rfl (fun c _ => Finset.sum_comm)
    _ = ∑ x, ∑ c, ∑ d, ∑ y, f c d x y := Finset.sum_comm
    _ = ∑ x, ∑ c, ∑ y, ∑ d, f c d x y :=
        Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun c _ => Finset.sum_comm))
    _ = ∑ x, ∑ y, ∑ c, ∑ d, f c d x y := Finset.sum_congr rfl (fun x _ => Finset.sum_comm)
end PI.QnCovHat2W
