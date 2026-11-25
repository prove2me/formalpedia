-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.zPlus_V
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:26:28.657033+00:00
-- url     : https://prove2.me/submissions/2507bfcc-24e5-4c8f-8169-09f8871c448c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_zPlus_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_zPlus_khw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) {Λ : Fin n → ℝ}
    {V : Submodule ℂ M} (hV : IsKIrrHW ε E Λ V) :
    ∀ v ∈ V, zPlus ε E v = (∑ c ∈ plusIdx ε, ((Λ c : ℝ) : ℂ)) • v := by
  obtain ⟨_, hst, hirr, w, hwV, hw0, hw⟩ := hV
  have hS'st : IsKStableSub ε E
      (V ⊓ LinearMap.ker (zPlus ε E - (∑ c ∈ plusIdx ε, ((Λ c : ℝ) : ℂ)) • 1)) := by
    intro a b hab v hv
    rw [Submodule.mem_inf, LinearMap.mem_ker] at hv ⊢
    refine ⟨hst a b hab v hv.1, ?_⟩
    have hz := hv.2
    rw [LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply, Module.End.one_apply] at hz
    have hc := LinearMap.congr_fun (zPlus_comm (ε := ε) hE a b) v
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, hz, hab, sub_self,
      zero_smul, add_zero] at hc
    rw [LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply, Module.End.one_apply, hc, map_smul]
  rcases hirr _ inf_le_left hS'st with h0 | hV'
  · exfalso
    apply hw0
    have hwS : w ∈ V ⊓ LinearMap.ker (zPlus ε E - (∑ c ∈ plusIdx ε, ((Λ c : ℝ) : ℂ)) • 1) := by
      rw [Submodule.mem_inf, LinearMap.mem_ker]
      refine ⟨hwV, ?_⟩
      rw [LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply, Module.End.one_apply]
      exact zPlus_khw hw
    rw [h0] at hwS
    exact (Submodule.mem_bot ℂ).1 hwS
  · intro v hv
    rw [← hV', Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero,
      LinearMap.smul_apply, Module.End.one_apply] at hv
    exact hv.2
end ReciprocityTheory.ChartRestriction.DS
