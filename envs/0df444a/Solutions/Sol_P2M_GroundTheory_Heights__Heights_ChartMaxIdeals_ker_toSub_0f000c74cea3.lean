-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_ker_toSub_0f000c74cea3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:04:30.415944+00:00
-- url     : https://prove2.me/submissions/15f4bb27-489a-4c38-af52-9c8508df8f3c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProperSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartMaxIdeals

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartMaxIdeals
variable {F : Type} [Field F] {n e : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartMaxIdeals
theorem _root_.solution {I W : Ideal (MvPolynomial (Fin n) F)} (h : I ≤ W) (t : Fin n → F) :
    RingHom.ker (toSub h t e) = W.map (chartX I t e) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := chartIncIdeal I t e) x
    have hy : y ∈ chartIncIdeal W t e := Ideal.Quotient.eq_zero_iff_mem.mp hx
    rw [chartIncIdeal_eq_sup h t, Submodule.mem_sup] at hy
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    have hb' : Ideal.Quotient.mk (chartIncIdeal I t e) b ∈ W.map (chartX I t e) := by
      have hle : W.map (rename Sum.inl) ≤ (W.map (chartX I t e)).comap (Ideal.Quotient.mk (chartIncIdeal I t e)) := by
        rw [Ideal.map_le_iff_le_comap]
        intro w hw
        exact Ideal.mem_map_of_mem (chartX I t e) hw
      exact hle hb
    have ha' : Ideal.Quotient.mk (chartIncIdeal I t e) a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
    rw [map_add, ha', zero_add]
    exact hb'
  · rw [Ideal.map_le_iff_le_comap]
    intro w hw
    rw [Ideal.mem_comap, RingHom.mem_ker]
    show Ideal.Quotient.mk (chartIncIdeal W t e) (rename Sum.inl w) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, chartIncIdeal_eq_sup h t]
    exact Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hw)
end GroundTheory.Heights₂.Heights.ChartMaxIdeals
