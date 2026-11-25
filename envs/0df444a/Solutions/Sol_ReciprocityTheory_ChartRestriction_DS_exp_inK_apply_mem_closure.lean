-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.exp_inK_apply_mem_closure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:03:31.919244+00:00
-- url     : https://prove2.me/submissions/8cd340f1-5ecc-4f08-aa48-5b2bb4bdddd6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Taylor
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ClosureK
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_actM_pow_mem_layer_of_inK
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_exists_norm_actM_pow_le_of_inK
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_genSub_eq_iSup_layer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_hasSum_orbit_of_bound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_layer_le_genSub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_layer_mono


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
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hVf : FiniteDimensional ℂ V) (hVK : IsKStableSub ε E V)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) {v : D} (hv : v ∈ genSub E V) :
    σ (NormedSpace.exp Z) (v : H) ∈ ((genSub E V).map D.subtype).topologicalClosure := by
  have hE := hD.glRep
  have hv' := hv
  rw [genSub_eq_iSup_layer hE hVK] at hv'
  obtain ⟨k, hk⟩ : ∃ k, v ∈ layer ε E V k :=
    (Submodule.mem_iSup_of_directed _ (Monotone.directed_le fun i j hij => layer_mono hij)).mp hv'
  obtain ⟨C, hC0, hC⟩ := exists_norm_actM_pow_le_of_inK hE hVK hVf hZ k
  have hs : Summable fun m : ℕ => C ^ m * ‖v‖ * |(1 : ℝ) - 0| ^ m / (m.factorial : ℝ) := by
    have := (Real.summable_pow_div_factorial C).mul_left ‖v‖
    refine this.congr fun m => ?_
    simp only [sub_zero, abs_one, one_pow, mul_one]
    ring
  have hsum := hasSum_orbit_of_bound hσ hD hZ.1 v (fun m => C ^ m * ‖v‖)
    (fun m => by simpa using hC v hk m) 0 1 hs
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hσ.1.1, Complex.ofReal_one,
    one_smul, ContinuousLinearMap.one_apply, sub_zero, one_pow] at hsum
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  refine mem_closure_of_tendsto hsum.tendsto_sum_nat (Filter.Eventually.of_forall fun N => ?_)
  refine Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ ?_
  exact Submodule.mem_map_of_mem
    (layer_le_genSub (ε := ε) k (actM_pow_mem_layer_of_inK hE hVK hZ hk m))
end ReciprocityTheory.ChartRestriction.DS
