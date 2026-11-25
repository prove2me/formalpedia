-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.cut_db_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:08:37.201614+00:00
-- url     : https://prove2.me/submissions/d89dbb08-10d2-4d3e-9b83-22732a6d81cc

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_CutoffA
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
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (j : Fin n) (f g : M → ℂ) (x : M) (h : f =ᶠ[𝓝 x] g) :
    db n z j f x = db n z j g x := by
  unfold db
  split_ifs with hc
  · have hs := Classical.choose_spec hc
    generalize Classical.choose hc = e at hs ⊢
    obtain ⟨hch, hxs⟩ := hs
    have hzx : z x = e x := hch hxs
    have ht : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
      first
      | exact e.tendsto_symm hxs
      | (have h0 := e.continuousAt_symm (e.map_source hxs)
         unfold ContinuousAt at h0
         rwa [e.left_inv hxs] at h0)
    have hev : f ∘ e.symm =ᶠ[𝓝 (z x)] g ∘ e.symm := by
      rw [hzx]
      exact h.comp_tendsto ht
    unfold wdb
    rw [hev.fderiv_eq]
  · rfl
end ReciprocityTheory.L2DbarEstimates.F
