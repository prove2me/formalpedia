-- Prove2me | solution 1 for PIW.AdelClassFin.lDense_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:09:30.153832+00:00
-- url     : https://prove2.me/submissions/ebc0214e-fb46-4a97-b12f-c122ebcb4ed1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictLat
import Theorems.Thm_PIW_AdelClassFin_DictLat_Lf_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix
namespace PIW.AdelClassFin
theorem _root_.solution (h : DDense) : LDense := by
  intro I N hN y hy
  have hle : I.Lf ≤ denseSub I N h hN := DictLat.Lf_le I _ fun l hl => by
    show ∃ l' ∈ I.L, ∃ y' ∈ I.Lf, iv I l = iv I l' + (N : I.E ⊗[I.F] Af I.F) • y'
    exact ⟨l, hl, 0, I.Lf.zero_mem, by rw [smul_zero, add_zero]⟩
  exact hle hy
end PIW.AdelClassFin
