-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.FlagGramNonneg.zt_zt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:40:01.62014+00:00
-- url     : https://prove2.me/submissions/b93926d7-5a59-47ee-a408-53b468e6c90b

import Definitions.Def_Formalism_PeriodIntegrals_FlagGramNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FlagGramNonnegativity_SumMulCommMulVec
import Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_herm
import Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_left_sub_sum
import Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_right_sub_sum
import Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_e_zt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PI.FlagGramNonneg
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FlagGramNonneg
variable {E : Type} [Field E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
variable (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (e e' : Fin r → V) (z z' : V)
namespace PI.UnitaryGroupMassFormula.FlagGramNonneg
theorem _root_.solution (hS : hT.IsSymm) (he : ∀ a b, hT (e a) (e b) = 0) (hez : ∀ a, hT (e a) z = 0) :
    hT (zt hT e e' z) (zt hT e e' z) = hT z z := by
  nth_rw 1 [zt]
  rw [left_sub_sum]
  simp only [e_zt hT e e' z he hez, mul_zero, Finset.sum_const_zero, sub_zero]
  have hze : ∀ a, hT z (e a) = 0 := fun a => by rw [herm hS, hez, star_zero]
  unfold zt
  rw [right_sub_sum]
  simp [hze]
end PI.UnitaryGroupMassFormula.FlagGramNonneg
