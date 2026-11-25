-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_form_pair_b1860578b0d2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:42:14.275744+00:00
-- url     : https://prove2.me/submissions/d1aece71-4df1-471a-90ab-81971f18ecae

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PRepresentative
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_weightedHomogeneousComponent_mul_form_f630f1747419
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_component_not_mem_53dbbac47368

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {P H : Ideal (MRing ι R)} [hP : P.IsPrime] [hH : H.IsPrime]
    (hPm : IsMultiHomogIdeal P) (hPH : P ≤ H) {f g u v : MRing ι R} {bf bg : K → ℕ}
    (hf : IsMultiHomog f bf) (hg : IsMultiHomog g bg) (hfP : f ∉ P) (hgP : g ∉ P) (hu : u ∉ H)
    (hv : v ∉ H) (h : u * f - v * g ∈ P) :
    ∃ (u' v' : MRing ι R) (e d : K → ℕ), IsMultiHomog u' e ∧ IsMultiHomog v' d ∧
      d + bg = e + bf ∧ u' ∉ H ∧ v' ∉ H ∧ u' * f - v' * g ∈ P := by
  classical
  obtain ⟨e, he⟩ := exists_component_not_mem hu
  set u' := weightedHomogeneousComponent (blockWeight ι) e u with hu'
  have hc := hPm _ h (e + bf)
  rw [map_sub, weightedHomogeneousComponent_mul_form hf, weightedHomogeneousComponent_mul_form hg,
    if_pos le_add_self, add_tsub_cancel_right, ← hu'] at hc
  by_cases hle : bg ≤ e + bf
  · rw [if_pos hle] at hc
    set v' := weightedHomogeneousComponent (blockWeight ι) (e + bf - bg) v
    refine ⟨u', v', e, e + bf - bg, weightedHomogeneousComponent_isWeightedHomogeneous _ _,
      weightedHomogeneousComponent_isWeightedHomogeneous _ _, tsub_add_cancel_of_le hle, he, ?_, hc⟩
    intro hv'
    have h2 : g * (u * v' - u' * v) ∈ P := by
      have e2 : g * (u * v' - u' * v) = u' * (u * f - v * g) - u * (u' * f - v' * g) := by ring
      rw [e2]
      exact P.sub_mem (P.mul_mem_left _ h) (P.mul_mem_left _ hc)
    have h3 : u * v' - u' * v ∈ H := hPH ((hP.mem_or_mem h2).resolve_left hgP)
    have h4 : u' * v ∈ H := by
      have h5 := H.sub_mem (H.mul_mem_left u hv') h3
      rwa [sub_sub_cancel] at h5
    exact (hH.mem_or_mem h4).elim he hv
  · rw [if_neg hle, sub_zero] at hc
    exact ((hP.mem_or_mem hc).elim (fun h' => he (hPH h')) hfP).elim
end GroundTheory.Heights₂.Heights.NumbersDVR
