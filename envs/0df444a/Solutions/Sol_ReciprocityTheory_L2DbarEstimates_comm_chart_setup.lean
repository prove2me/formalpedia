-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.comm_chart_setup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:43:24.282182+00:00
-- url     : https://prove2.me/submissions/ad1a653b-bdf9-4692-b107-093b363be1d9

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
private theorem chart_symm_eventuallyEq_symm {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e e' : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (he' : IsChart n z e') (y : M)
    (hy : y ∈ e.source) (hy' : y ∈ e'.source) : (e'.symm : V n → M) =ᶠ[𝓝 (z y)] e.symm := by
  have hzy : z y = e' y := he' hy'
  have ht : z y ∈ e'.target := by rw [hzy]; exact e'.map_source hy'
  have hc : ContinuousAt e'.symm (z y) := e'.continuousAt_symm ht
  have hs : e.source ∈ 𝓝 (e'.symm (z y)) := by
    rw [hzy, e'.left_inv hy']; exact e.open_source.mem_nhds hy
  filter_upwards [e'.open_target.mem_nhds ht, hc hs] with w hw hw2
  have h1 : e (e'.symm w) = w := by
    rw [← he hw2, he' (e'.map_target hw), e'.right_inv hw]
  calc e'.symm w = e.symm (e (e'.symm w)) := (e.left_inv hw2).symm
    _ = e.symm w := by rw [h1]
private theorem d_apply_eq_wd_comp_chart_symm {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n)
    (f : M → ℂ) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (y : M)
    (hy : y ∈ e.source) : d n z j f y = wd n j (f ∘ e.symm) (z y) := by
  have h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ y ∈ e.source := ⟨e, he, hy⟩
  have hg : (f ∘ (Classical.choose h).symm) =ᶠ[𝓝 (z y)] (f ∘ e.symm) :=
    (chart_symm_eventuallyEq_symm n z e _ he (Classical.choose_spec h).1 y hy
      (Classical.choose_spec h).2).fun_comp f
  simp only [d, dif_pos h, wd, hg.fderiv_eq]
private theorem db_apply_eq_wdb_comp_chart_symm {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n)
    (f : M → ℂ) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (y : M)
    (hy : y ∈ e.source) : db n z j f y = wdb n j (f ∘ e.symm) (z y) := by
  have h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ y ∈ e.source := ⟨e, he, hy⟩
  have hg : (f ∘ (Classical.choose h).symm) =ᶠ[𝓝 (z y)] (f ∘ e.symm) :=
    (chart_symm_eventuallyEq_symm n z e _ he (Classical.choose_spec h).1 y hy
      (Classical.choose_spec h).2).fun_comp f
  simp only [db, dif_pos h, wdb, hg.fderiv_eq]
end
end ReciprocityTheory.L2DbarEstimates
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ)
    (hf : Ck n z 2 f) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (x : M)
    (hx : x ∈ e.source) :
    z x ∈ e.target ∧ ContDiffAt ℝ 2 (f ∘ e.symm) (z x) ∧
      (∀ j, (d n z j f ∘ e.symm) =ᶠ[𝓝 (z x)] wd n j (f ∘ e.symm)) ∧
      (∀ j, (db n z j f ∘ e.symm) =ᶠ[𝓝 (z x)] wdb n j (f ∘ e.symm)) := by
  have h1 : z x ∈ e.target := by rw [he hx]; exact e.map_source hx
  refine ⟨h1, ?_, ?_, ?_⟩
  · have h2 := (hf e he).contDiffAt (e.open_target.mem_nhds h1)
    exact_mod_cast h2
  · intro j
    filter_upwards [e.open_target.mem_nhds h1] with w hw
    have hs : e.symm w ∈ e.source := e.map_target hw
    show d n z j f (e.symm w) = wd n j (f ∘ e.symm) w
    rw [d_apply_eq_wd_comp_chart_symm n z j f e he _ hs, he hs, e.right_inv hw]
  · intro j
    filter_upwards [e.open_target.mem_nhds h1] with w hw
    have hs : e.symm w ∈ e.source := e.map_target hw
    show db n z j f (e.symm w) = wdb n j (f ∘ e.symm) w
    rw [db_apply_eq_wdb_comp_chart_symm n z j f e he _ hs, he hs, e.right_inv hw]
end ReciprocityTheory.L2DbarEstimates
