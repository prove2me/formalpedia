-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.chartFlat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:52:05.478036+00:00
-- url     : https://prove2.me/submissions/d2222300-b3d3-4a9b-9036-6bcf7a38a6b2

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_ChartB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_ChartFlat
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_chT_S
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_chT_back
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_chT_div
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_chT_plateau
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_chartTransport_indicator_memLp_two


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set Function
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hExt : ExtendStatement n M)
    (hFlat : FlatGraphStatement n) :
    ChartFlatStatement n M := by
  intro z hz e G D S he hGl hDl hSl hDiv hSw hGc hDc hSc hGs hDs hSs
  have hTc : IsCompact (tsupport G ∪ tsupport D ∪ tsupport S) := (hGc.union hDc).union hSc
  have hTs : tsupport G ∪ tsupport D ∪ tsupport S ⊆ e.source :=
    union_subset (union_subset hGs hDs) hSs
  have hKc : IsCompact (e '' (tsupport G ∪ tsupport D ∪ tsupport S)) :=
    hTc.image_of_continuousOn (e.continuousOn.mono hTs)
  have hKt : e '' (tsupport G ∪ tsupport D ∪ tsupport S) ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩; exact e.map_source (hTs hx)
  have hK : ∀ y ∈ e.target, e.symm y ∈ tsupport G ∪ tsupport D ∪ tsupport S →
      y ∈ e '' (tsupport G ∪ tsupport D ∪ tsupport S) :=
    fun y hy hT => ⟨e.symm y, hT, e.right_inv hy⟩
  obtain ⟨ρ, hρd, hρc, hρt, O, hOo, hKO, h1⟩ := chT_plateau _ _ hKc e.open_target hKt
  have hdivT := chT_div hExt hz he G D hGl.1 hDl.1 hGs hDs hDiv ρ hρd hρc hρt O hOo h1
    (fun y hy hT => hKO (hK y hy (by rcases hT with h | h <;> simp [h])))
  have hST := chT_S hExt hz he G S hGl.1 hSl.1 hGs hSs hSw ρ hρd hρc hρt O hOo h1
    (fun y hy hT => hKO (hK y hy (by rcases hT with h | h <;> simp [h])))
  have hvan : ∀ y, y ∉ e '' (tsupport G ∪ tsupport D ∪ tsupport S) →
      e.target.indicator (G ∘ e.symm) y = 0 ∧ e.target.indicator (D ∘ e.symm) y = 0 ∧
        e.target.indicator (S ∘ e.symm) y = 0 := by
    intro y hy
    by_cases hyt : y ∈ e.target
    · have hn : e.symm y ∉ tsupport G ∪ tsupport D ∪ tsupport S := fun h => hy (hK y hyt h)
      simp only [indicator_of_mem hyt, Function.comp_apply]
      refine ⟨image_eq_zero_of_notMem_tsupport (fun h => hn ?_),
        image_eq_zero_of_notMem_tsupport (fun h => hn ?_),
        image_eq_zero_of_notMem_tsupport (fun h => hn ?_)⟩ <;> simp [h]
    · simp [indicator_of_notMem hyt]
  obtain ⟨K₀, hK₀c, hK₀t, happ⟩ := hFlat e.target _ (e.target.indicator (G ∘ e.symm))
    (e.target.indicator (D ∘ e.symm)) (e.target.indicator (S ∘ e.symm)) e.open_target hKc hKt
    hvan (chartTransport_indicator_memLp_two hz he G hGl hGc hGs) (chartTransport_indicator_memLp_two hz he D hDl hDc hDs)
    (chartTransport_indicator_memLp_two hz he S hSl hSc hSs) (fun φ hφd hφc => hdivT φ hφd hφc)
    (fun φ hφd hφc j k => hST φ hφd hφc j k)
  refine ⟨e.symm '' K₀, hK₀c.image_of_continuousOn (e.continuousOn_symm.mono hK₀t),
    fun δ hδ => ?_⟩
  obtain ⟨G', hG'd, hG'0, hε1, hε2, hε3⟩ := happ δ hδ
  exact chT_back hExt hz he G D S hGl.1 hDl.1 hSl.1 hGs hDs hSs K₀ hK₀c hK₀t G' hG'd hG'0 δ
    hε1 hε2 hε3
end ReciprocityTheory.L2DbarEstimates.F
