-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.finiteDimensional_prodSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:23:14.092608+00:00
-- url     : https://prove2.me/submissions/897207e6-42d7-41af-bfce-697d4d0e0498

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_SchForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCore
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_prFst_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_prSnd_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.prFst_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.prSnd_apply



set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {V₁ : Submodule ℂ M₁} {V₂ : Submodule ℂ M₂} (h₁ : FiniteDimensional ℂ V₁)
    (h₂ : FiniteDimensional ℂ V₂) : FiniteDimensional ℂ (prodSub V₁ V₂) := by
  have h₁' : V₁.FG := Module.Finite.iff_fg.mp h₁
  have h₂' : V₂.FG := Module.Finite.iff_fg.mp h₂
  refine Module.Finite.iff_fg.mpr ?_
  unfold prodSub
  first
    | (rw [Submodule.comap_equiv_eq_map_symm]; exact (h₁'.prod h₂').map _)
    | (have heq : Submodule.comap (WithLp.linearEquiv 2 ℂ (M₁ × M₂)).toLinearMap (V₁.prod V₂) =
          Submodule.map (WithLp.linearEquiv 2 ℂ (M₁ × M₂)).symm.toLinearMap (V₁.prod V₂) := by
         ext x
         simp only [Submodule.mem_comap, Submodule.mem_map]
         constructor
         · intro hx
           exact ⟨_, hx, by simp⟩
         · rintro ⟨y, hy, rfl⟩
           simpa using hy
       rw [heq]
       exact (h₁'.prod h₂').map _)
end ReciprocityTheory.ChartRestriction.DS
