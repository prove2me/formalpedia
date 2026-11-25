-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.FlagGramNonneg.yv_zt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:54:45.627836+00:00
-- url     : https://prove2.me/submissions/428a3967-1708-4559-83bf-c4d0bf5a47d6

import Definitions.Def_Formalism_PeriodIntegrals_FlagGramNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FlagGramNonnegativity_SumMulCommMulVec
import Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_herm
import Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_left_sub_sum
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_FlagGramNonneg_zt_e__5c081d0faef5
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
theorem _root_.solution (hS : hT.IsSymm) (hA : IsUnit (amat hT e e').det) (he : ∀ a b, hT (e a) (e b) = 0)
    (hez : ∀ a, hT (e a) z = 0) (a : Fin r) : hT (yv hT e e' a) (zt hT e e' z) = 0 := by
  unfold yv
  rw [left_sub_sum, e_zt hT e e' z he hez]
  have h : ∀ b, hT (e' b) (zt hT e e' z) = 0 := fun b => by
    rw [herm hS, zt_e' hT e e' z hA, star_zero]
  simp [h]
end PI.UnitaryGroupMassFormula.FlagGramNonneg
