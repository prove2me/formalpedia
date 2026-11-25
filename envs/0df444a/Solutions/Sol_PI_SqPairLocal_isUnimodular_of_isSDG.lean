-- Prove2me | solution 1 for PI.SqPairLocal.isUnimodular_of_isSDG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:23:26.632141+00:00
-- url     : https://prove2.me/submissions/6b526a48-8726-4454-87ea-18c855c93fdf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SqPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UnimodGenus
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsUnimodularOfIsSDG
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG PI.UG
variable {E : Type} [Field E] [NumberField E] [StarRing E]
namespace PI.SqPairLocal
theorem _root_.solution {N : ℕ} {L : Submodule (𝓞 E) (Fin N → E)} (h : IsSDG E N L) :
    IsUnimodular (hStd E N) L := by
  obtain ⟨-, -, h3⟩ := h
  unfold PI.UG.IsUnimodular PI.UG.dual
  ext y
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one]
  rw [h3 y]
  exact forall₂_congr fun x _ => RingHom.mem_range.symm
end PI.SqPairLocal
