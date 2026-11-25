-- Prove2me | solution 1 for PI.WwMinorExpandWork.wwMinorExpand_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:42:23.080944+00:00
-- url     : https://prove2.me/submissions/9df64e14-e169-4e19-9cea-92caacde326f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwMinorExpand
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_DetSubmatrixFun
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorExpansion_WwMinorExpandMain
import Theorems.Thm_PI_WwMinorExpandWork_minor_rep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open PI PI.WwMinorExpandWork
open PI.WwMinorExpand
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ)
namespace PI.WwMinorExpandWork
theorem _root_.solution : WwMinorExpand := by
  intro Lt _ _ N0 N1 nu I
  have h := fun (s : Lt) (c : Fin ((nu s).rowLen 0)) =>
    minor_rep N0 N1 s ((nu s).colLen c) (I s c)
  choose d hd using h
  refine ⟨fun J => ∏ s, ∏ c, d s c (J s c), ?_⟩
  change _ = ∑ᶠ J : (∀ (s : Lt) (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) ↪o Fin N0),
    MvPolynomial.rename Sum.inl (KM.nablaX N0 nu J) *
      MvPolynomial.rename Sum.inr (∏ s, ∏ c, d s c (J s c))
  rw [finsum_eq_sum_of_fintype]
  unfold KM.Gxz
  simp_rw [hd]
  simp_rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  simp only [KM.nablaX, minX, map_prod, ← Finset.prod_mul_distrib]
end PI.WwMinorExpandWork
