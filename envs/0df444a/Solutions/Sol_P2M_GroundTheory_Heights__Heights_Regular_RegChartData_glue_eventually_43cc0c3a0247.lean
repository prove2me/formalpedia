-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_RegChartData_glue_eventually_43cc0c3a0247
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:34:59.254843+00:00
-- url     : https://prove2.me/submissions/48587a43-9ddd-4e1c-a63d-2bf2735766cb

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_RegMaxReindex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_GlueCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PGlueRegularised
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_regMax_of_injective_e20efb725643
import Theorems.Thm_ReciprocityTheory_AnForm_levi_add_smul
import Theorems.Thm_ReciprocityTheory_AnForm_levi_comp
import Theorems.Thm_ReciprocityTheory_AnForm_levi_congr
import Theorems.Thm_ReciprocityTheory_AnForm_levi_re_analytic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology Set
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh Mollifier molli coordDiv limsupExt regMax)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open ReciprocityTheory.AnForm (levi levi_congr levi_comp levi_add_smul levi_re_analytic)
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.RegChartData
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} (R : RegChartData A)
open Classical
namespace GroundTheory.Heights₂.Heights.Regular.RegChartData
theorem _root_.solution (ρ : Mollifier D) (η : Fin R.N → X → ℝ) {Cη K t ε : ℝ}
    (hcut : R.IsCutoffFamily η Cη) (hε : 0 ≤ ε)
    (hcmp : ∀ j k, ∀ x ∈ R.mid j ∩ R.mid k, |R.phReg ρ K t j x - R.phReg ρ K t k x| ≤ ε)
    (x₀ : X) : ∀ᶠ y in 𝓝 x₀, (∀ j, x₀ ∈ R.mid j → y ∈ R.mid j) ∧
      R.regularised ρ K t ε η y =
        regMax ε (fun j : {j // x₀ ∈ R.mid j} => R.phReg ρ K t j y + 4 * ε * η j y) + ε / 2 := by
  choose L hLc hLsub hL using hcut.eq_neg_one
  have hev : ∀ᶠ y in 𝓝 x₀, ∀ j, (x₀ ∈ R.mid j → y ∈ R.mid j) ∧
      (x₀ ∉ R.mid j → y ∉ L j ∧ y ∉ closure (R.inner j)) := by
    refine Filter.eventually_all.2 fun j => ?_
    by_cases h : x₀ ∈ R.mid j
    · filter_upwards [(R.isOpen_mid j).mem_nhds h] with y hy
      exact ⟨fun _ => hy, fun h' => absurd h h'⟩
    · have hc : IsOpen (L j ∪ closure (R.inner j))ᶜ :=
        ((hLc j).union isClosed_closure).isOpen_compl
      have hx : x₀ ∈ (L j ∪ closure (R.inner j))ᶜ := by
        rintro (h1 | h1)
        · exact h (hLsub j h1)
        · exact h (R.closure_inner j h1)
      filter_upwards [hc.mem_nhds hx] with y hy
      simp only [mem_compl_iff, mem_union, not_or] at hy
      exact ⟨fun h' => absurd h' h, fun _ => hy⟩
  filter_upwards [hev] with y hy
  refine ⟨fun j hj => (hy j).1 hj, ?_⟩
  simp only [RegChartData.regularised, PotentialCharts.glue]
  refine congrArg (· + ε / 2) ?_
  refine regMax_of_injective
    (fun j : {j // x₀ ∈ R.mid j} => (⟨j.1, (hy j.1).1 j.2⟩ : {j // y ∈ R.mid j}))
    (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab)) hε _ ?_
  intro i hi
  obtain ⟨k, hk⟩ := R.cover y
  have hk0 : x₀ ∈ R.mid k := by
    by_contra h
    exact ((hy k).2 h).2 (subset_closure hk)
  refine ⟨⟨k, hk0⟩, ?_⟩
  have hi0 : x₀ ∉ R.mid i := fun h => hi ⟨i.1, h⟩ rfl
  have hiL : η i y = -1 := hL i y ⟨i.2, ((hy i).2 hi0).1⟩
  have hk1 : η k y = 0 := hcut.eq_zero k y hk
  have hc := (abs_le.1 (hcmp i k y ⟨i.2, R.inner_subset_mid k hk⟩)).2
  simp only [hiL, hk1]
  linarith
end GroundTheory.Heights₂.Heights.Regular.RegChartData
