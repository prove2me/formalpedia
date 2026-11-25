-- Prove2me | solution 1 for P2M_PI_UnitaryGroupMassFormula_FlagGramNonneg_yv_zt__a7df7ecdfada
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:53:28.706286+00:00
-- url     : https://prove2.me/submissions/788f902d-110b-4ce1-8586-953955f53561

import Definitions.Def_Formalism_PeriodIntegrals_FlagGramNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FlagGramNonnegativity_SumMulCommMulVec
import Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_left_sub_sum
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_FlagGramNonneg_e_zt__73625be99166
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
theorem _root_.solution (hA : IsUnit (amat hT e e').det) (he' : ∀ a b, hT (e' a) (e' b) = 0)
    (hez' : ∀ a, hT (e' a) z' = 0) (a : Fin r) : hT (yv hT e e' a) (zt' hT e e' z') = 0 := by
  unfold yv
  rw [left_sub_sum, e_zt' hT e e' z' hA]
  simp [e'_zt' hT e e' z' he' hez']
end PI.UnitaryGroupMassFormula.FlagGramNonneg
