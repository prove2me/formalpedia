-- Prove2me | solution 1 for P2M_PI_UnitaryGroupMassFormula_FlagGramNonneg_zt__zt__f753000f342f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:48:01.598227+00:00
-- url     : https://prove2.me/submissions/ea2b27ac-ad10-4e89-9d58-9323c04b803c

import Definitions.Def_Formalism_PeriodIntegrals_FlagGramNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FlagGramNonnegativity_SumMulCommMulVec
import Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_herm
import Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_left_sub_sum
import Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_right_sub_sum
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_FlagGramNonneg_e__zt__84c28ab36502

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
theorem _root_.solution (hS : hT.IsSymm) (he' : ∀ a b, hT (e' a) (e' b) = 0)
    (hez' : ∀ a, hT (e' a) z' = 0) :
    hT (zt' hT e e' z') (zt' hT e e' z') = hT z' z' := by
  nth_rw 1 [zt']
  rw [left_sub_sum]
  simp only [e'_zt' hT e e' z' he' hez', mul_zero, Finset.sum_const_zero, sub_zero]
  have hze : ∀ a, hT z' (e' a) = 0 := fun a => by rw [herm hS, hez', star_zero]
  unfold zt'
  rw [right_sub_sum]
  simp [hze]
end PI.UnitaryGroupMassFormula.FlagGramNonneg
