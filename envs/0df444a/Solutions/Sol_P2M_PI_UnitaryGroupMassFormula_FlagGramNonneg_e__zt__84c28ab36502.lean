-- Prove2me | solution 1 for P2M_PI_UnitaryGroupMassFormula_FlagGramNonneg_e__zt__84c28ab36502
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:28.689906+00:00
-- url     : https://prove2.me/submissions/29f96e3b-bee1-4f8c-a43e-8262bb866aea

import Definitions.Def_Formalism_PeriodIntegrals_FlagGramNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FlagGramNonnegativity_SumMulCommMulVec
import Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_right_sub_sum

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
theorem _root_.solution (he' : ∀ a b, hT (e' a) (e' b) = 0) (hez' : ∀ a, hT (e' a) z' = 0) (c : Fin r) :
    hT (e' c) (zt' hT e e' z') = 0 := by
  unfold zt'
  rw [right_sub_sum, hez']
  simp [he']
end PI.UnitaryGroupMassFormula.FlagGramNonneg
