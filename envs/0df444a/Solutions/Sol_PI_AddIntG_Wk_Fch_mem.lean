-- Prove2me | solution 1 for PI.AddIntG.Wk.Fch_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:02:26.214191+00:00
-- url     : https://prove2.me/submissions/d03cc3bc-6975-4cb9-9c80-e8e31f00a6dd

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_VarZeroSubVarOneNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_FormalGroupLawExists
import Theorems.Thm_PI_AddIntG_Wk_bZ_const
import Theorems.Thm_PI_AddIntG_Wk_Fch_eq
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_mvsubst_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_thirdRoot_mem_coeffSubring


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.AddIntG PI.AddIntG.Wk
variable {p : ℕ} [Fact p.Prime]
namespace PI.AddIntG.Wk
theorem _root_.solution {S : Subring ℂ_[p]} {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]}
    (h1 : W.a₁ ∈ S) (h2 : W.a₂ ∈ S) (h3 : W.a₃ ∈ S) (h4 : W.a₄ ∈ S) (h6 : W.a₆ ∈ S) (h : IsWq W wq) :
    ∀ n, MvPowerSeries.coeff n (Fch W wq) ∈ S := by
  have hZ := thirdRoot_mem_coeffSubring h1 h2 h3 h4 h6 h
  have hb : ∀ i, bZ W wq i ∈ SerS S (Fin 2) := by
    intro i
    unfold bZ
    split_ifs
    · exact zero_mem _
    · exact hZ
  rw [Fch_eq]
  exact (mem_SerS S _).mp (mvsubst_mem_SerS S (bZ_const W wq) hb hZ)
end PI.AddIntG.Wk
