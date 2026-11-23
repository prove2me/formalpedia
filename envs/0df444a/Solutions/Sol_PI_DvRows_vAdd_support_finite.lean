-- Prove2me | solution 1 for PI.DvRows.vAdd_support_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:05.07386+00:00
-- url     : https://prove2.me/submissions/0b34a441-7540-4db5-92a5-5fa016487c1d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_AsmBound
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
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv Formalism.LFunctionChainParameters.LLcv
variable {K : Type} [Field K] [NumberField K]
namespace PI.DvRows
theorem _root_.solution (x : K) :
    (Function.support fun w : HeightOneSpectrum (𝓞 K) => vAdd w x).Finite := by
  by_cases hx : x = 0
  · simp [vAdd, hx]
  · refine ((IsDedekindDomain.HeightOneSpectrum.Support.finite (𝓞 K) x).union
        (IsDedekindDomain.HeightOneSpectrum.Support.finite (𝓞 K) x⁻¹)).subset ?_
    intro w hw
    rw [Function.mem_support] at hw
    have hne : w.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
    rcases lt_trichotomy (w.valuation K x) 1 with hlt | heq | hgt
    · right
      show 1 < w.valuation K x⁻¹
      rw [map_inv₀]
      exact (one_lt_inv₀ (zero_lt_iff.mpr hne)).mpr hlt
    · exact absurd (by simp [vAdd, heq]) hw
    · left
      exact hgt
end PI.DvRows
