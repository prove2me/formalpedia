-- Prove2me | solution 1 for PIW.AdelClassFin.hmk_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:19:40.486265+00:00
-- url     : https://prove2.me/submissions/bedff785-76ba-4d72-8612-13e18b04837f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HmkFactor
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open MeasureTheory Matrix Module
open scoped MatrixOrder
namespace PIW.AdelClassFin
theorem _root_.solution {N : ℕ} (x : Fin N → ℝ)
    (hx : x ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin N)))) :
    ∃ c : Fin N → ℤ, (fun i => (c i : ℝ)) = x := by
  rw [(Pi.basisFun ℝ (Fin N)).mem_span_iff_repr_mem (R := ℤ) x] at hx
  choose c hc using hx
  refine ⟨c, funext fun i => ?_⟩
  have := hc i
  simp only [Pi.basisFun_repr, algebraMap_int_eq, Int.coe_castRingHom] at this
  exact this
end PIW.AdelClassFin
