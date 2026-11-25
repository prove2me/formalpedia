-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.vanish_outside_tsupport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:06:17.801732+00:00
-- url     : https://prove2.me/submissions/1eeef4e9-02e4-4843-aa82-938687322791

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsIbp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {D : ℕ} {v : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ}
    (hy : y ∉ tsupport v) :
    cplx v =ᶠ[𝓝 y] (fun _ => 0) ∧ (∀ k, dzb k (cplx v) =ᶠ[𝓝 y] fun _ => 0) ∧
      fderiv ℝ (fderiv ℝ v) y = 0 := by
  have hWo : IsOpen (tsupport v)ᶜ := (isClosed_tsupport v).isOpen_compl
  have hy' : y ∈ (tsupport v)ᶜ := (Set.mem_compl_iff _ _).2 hy
  have hv0 : ∀ z ∈ (tsupport v)ᶜ, v z = 0 := fun z hz => by
    by_contra h
    exact (Set.mem_compl_iff _ _).1 hz (subset_tsupport v (Function.mem_support.2 h))
  have hc : ∀ z ∈ (tsupport v)ᶜ, cplx v =ᶠ[𝓝 z] fun _ => (0 : ℂ) := fun z hz => by
    filter_upwards [hWo.mem_nhds hz] with x hx
    simp [cplx, hv0 x hx]
  have hr : ∀ z ∈ (tsupport v)ᶜ, v =ᶠ[𝓝 z] fun _ => (0 : ℝ) := fun z hz => by
    filter_upwards [hWo.mem_nhds hz] with x hx using hv0 x hx
  refine ⟨hc y hy', fun k => ?_, ?_⟩
  · filter_upwards [hWo.mem_nhds hy'] with z hz
    have hfz := (hc z hz).fderiv_eq (𝕜 := ℝ)
    simp [dzb, hfz]
  · have h1 : fderiv ℝ v =ᶠ[𝓝 y] fun _ => (0 : (Fin D → ℂ) →L[ℝ] ℝ) := by
      filter_upwards [hWo.mem_nhds hy'] with z hz
      rw [(hr z hz).fderiv_eq (𝕜 := ℝ)]
      simp
    rw [h1.fderiv_eq (𝕜 := ℝ)]
    simp
end ReciprocityTheory.AnForm.A
