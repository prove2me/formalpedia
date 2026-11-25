-- Prove2me | solution 1 for PI.VolStabW.exists_appr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:58:49.423378+00:00
-- url     : https://prove2.me/submissions/ba4f5f60-1485-4620-b2de-6a234df52e99

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntRes
import Theorems.Thm_PI_VolStabW_vcoe
import Theorems.Thm_PI_VolStabW_HasDens_le
import Theorems.Thm_PI_VolStabW_HasDens_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace PI.VolStabW
theorem _root_.solution {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) :
    ∃ a : 𝓞 F, Valued.v (x - iO v a) < 1 := by
  have hU : IsOpen {y : Fv F v | Valued.v (x - y) < 1} := by
    have e : {y : Fv F v | Valued.v (x - y) < 1} = {y : Fv F v | ‖x - y‖ < 1} := by
      ext y; simp only [Set.mem_setOf_eq]; exact Valued.toNormedField.norm_lt_one_iff.symm
    rw [e]
    exact isOpen_lt (continuous_const.sub continuous_id).norm continuous_const
  obtain ⟨y, hy⟩ := (v.denseRange_algebraMap (K := F)).exists_mem_open hU
    ⟨x, by simp⟩
  simp only [Set.mem_setOf_eq] at hy
  have hx1 : Valued.v x ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) (K := F) (v := v)).1 hx
  have hy1 : v.valuation F y ≤ 1 := by
    rw [← vcoe]
    have : algebraMap F (Fv F v) y = x - (x - algebraMap F (Fv F v) y) := by ring
    rw [this]
    exact (Valuation.map_sub _ _ _).trans (max_le hx1 hy.le)
  obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer hy1 (1 : (WithZero (Multiplicative ℤ))ˣ)
  refine ⟨a, ?_⟩
  have ha' : Valued.v (iO v a - algebraMap F (Fv F v) y) < 1 := by
    rw [iO, ← map_sub, vcoe]; simpa using ha
  have : x - iO v a = (x - algebraMap F (Fv F v) y) - (iO v a - algebraMap F (Fv F v) y) := by ring
  rw [this]
  exact Valuation.map_sub_lt _ hy ha'
end PI.VolStabW
