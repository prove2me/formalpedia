-- Prove2me | solution 1 for PI.ParahoricIdxZ.W.card_range_redJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:02:59.942488+00:00
-- url     : https://prove2.me/submissions/7b55c227-a8e2-4277-811e-8b66d9eea285

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_ThetaInjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_CardRangeRedJ
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_GLRed_ker_red


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures.P.GLRed
open PI PI.ParahoricIdxZ PI.ParahoricIdxZ.W
variable {F : Type} [Field F] (O : Subring F) (ϖ : F) (hϖ : ϖ ∈ O)
namespace PI.ParahoricIdxZ.W
theorem _root_.solution (hϖ0 : ϖ ≠ 0) {a : ℕ} (J' : Subgroup (GL (Fin a) F))
    (hJ : J' ≤ Formalism.DoubleCosetMeasures.GLint O a) :
    Nat.card (redJ O ϖ hϖ J' hJ).range = Nat.card (J' ⧸ (Formalism.DoubleCosetMeasures.congSub O ϖ a).subgroupOf J') := by
  have hk : (redJ O ϖ hϖ J' hJ).ker = (Formalism.DoubleCosetMeasures.congSub O ϖ a).subgroupOf J' := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change red O a ϖ hϖ (Subgroup.inclusion hJ k) = 1 ↔ _
    rw [← MonoidHom.mem_ker, ker_red O ϖ hϖ hϖ0, Subgroup.mem_subgroupOf]
    rfl
  rw [← hk]
  exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv).symm
end PI.ParahoricIdxZ.W
