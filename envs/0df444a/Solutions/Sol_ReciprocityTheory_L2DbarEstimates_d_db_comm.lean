-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.d_db_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:02:50.45672+00:00
-- url     : https://prove2.me/submissions/fde8605f-9881-4475-981c-427772108eea

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_comm_wd_wdb
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_comm_chart_setup
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
private theorem wd_congr_of_eventuallyEq' (n : ℕ) (j : Fin n) {g h : V n → ℂ} {w : V n}
    (hgh : g =ᶠ[𝓝 w] h) : wd n j g w = wd n j h w := by
  simp only [wd, hgh.fderiv_eq]
private theorem wdb_congr_of_eventuallyEq (n : ℕ) (j : Fin n) {g h : V n → ℂ} {w : V n}
    (hgh : g =ᶠ[𝓝 w] h) : wdb n j g w = wdb n j h w := by
  simp only [wdb, hgh.fderiv_eq]
end
end ReciprocityTheory.L2DbarEstimates
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ) (hf : Ck n z 2 f) (j k : Fin n) (x : M) :
    d n z j (db n z k f) x = db n z k (d n z j f) x := by
  by_cases h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · obtain ⟨e, he, hx⟩ := h
    obtain ⟨_, h2, h3, h4⟩ := comm_chart_setup n z f hf e he x hx
    rw [d_apply_eq_wd_comp_chart_symm n z j _ e he x hx, db_apply_eq_wdb_comp_chart_symm n z k _ e he x hx,
      wd_congr_of_eventuallyEq' n j (h4 k), wdb_congr_of_eventuallyEq n k (h3 j)]
    exact comm_wd_wdb _ _ h2 j k
  · simp [d, db, h]
end ReciprocityTheory.L2DbarEstimates
