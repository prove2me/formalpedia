-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.loc_db_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:10:16.217738+00:00
-- url     : https://prove2.me/submissions/ee5c7127-c25e-4238-8380-9bb88f481fe5

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_LocalizeA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) {ι : Type*}
    (s : Finset ι) (f : ι → M → ℂ) (hf : ∀ i, Ck n z 1 (f i)) (j : Fin n) (x : M) :
    db n z j (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, db n z j (f i) x := by
  by_cases hc : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · simp only [db, dif_pos hc]
    set e := Classical.choose hc with he_def
    have he : IsChart n z e ∧ x ∈ e.source := Classical.choose_spec hc
    have hdiff : ∀ i ∈ s, DifferentiableAt ℝ (f i ∘ e.symm) (z x) := by
      intro i _
      rw [he.1 he.2]
      exact ((hf i e he.1).contDiffAt (e.open_target.mem_nhds (e.map_source he.2))).differentiableAt
        (by first | simp | norm_num | exact le_rfl)
    have hsum : ((fun y => ∑ i ∈ s, f i y) ∘ e.symm) = fun y => ∑ i ∈ s, (f i ∘ e.symm) y := rfl
    unfold wdb
    (first | rw [hsum, fderiv_fun_sum hdiff] | rw [hsum, ← Finset.sum_fn, fderiv_sum hdiff])
    have key : ∀ L : ι → (V n →L[ℝ] ℂ), ((∑ i ∈ s, L i) (bas n j) + Complex.I * (∑ i ∈ s, L i) (Complex.I • bas n j)) / 2 =
        ∑ i ∈ s, (L i (bas n j) + Complex.I * L i (Complex.I • bas n j)) / 2 := by
      intro L
      simp only [ContinuousLinearMap.sum_apply, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
    exact key _
  · simp only [db, dif_neg hc, Finset.sum_const_zero]
end ReciprocityTheory.L2DbarEstimates.F
