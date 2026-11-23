-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.E.ck_dTw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:33:47.488813+00:00
-- url     : https://prove2.me/submissions/b4c067fc-cbc5-4fde-a77e-3e13da0d135d

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_BasicIdentityStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HasCompactSupportDTw
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.L2DbarEstimates.E
open MeasureTheory
open scoped ComplexConjugate ContDiff
noncomputable section
private theorem d_eq_wd_comp_chart_symm {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n)
    (u : M → ℂ) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (x : M)
    (hx : x ∈ e.source) : d n z j u x = wd n j (u ∘ e.symm) (z x) := by
  have h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source := ⟨e, he, hx⟩
  rw [d, dif_pos h]
  obtain ⟨he', hx'⟩ := Classical.choose_spec h
  set e' := Classical.choose h

  have hzx : z x = e x := he hx
  have hzx' : z x = e' x := he' hx'
  have hev : ∀ᶠ w in nhds (z x), e'.symm w = e.symm w := by
    have ht : ∀ᶠ w in nhds (z x), w ∈ e.target := by
      rw [hzx]
      exact e.open_target.mem_nhds (e.map_source hx)
    have ht' : ∀ᶠ w in nhds (z x), w ∈ e'.target := by
      rw [hzx']
      exact e'.open_target.mem_nhds (e'.map_source hx')
    have hsrc : ∀ᶠ w in nhds (z x), e'.symm w ∈ e.source := by
      have hc : ContinuousAt e'.symm (z x) := by
        rw [hzx']
        exact e'.continuousAt_symm (e'.map_source hx')
      have hx0 : e'.symm (z x) = x := by
        rw [hzx']
        exact e'.left_inv hx'
      exact hc.preimage_mem_nhds (by rw [hx0]; exact e.open_source.mem_nhds hx)
    filter_upwards [ht, ht', hsrc] with w hw hw' hws
    apply e.injOn hws (e.map_target hw)
    rw [e.right_inv hw, ← he hws, he' (e'.map_target hw'), e'.right_inv hw']
  have hf : u ∘ e'.symm =ᶠ[nhds (z x)] u ∘ e.symm := hev.mono fun w hw => by
    simp only [Function.comp_apply, hw]
  simp only [wd, hf.fderiv_eq]
private theorem contDiffOn_wd_of_contDiffOn_succ (n : ℕ) (j : Fin n) (k : ℕ) (U : V n → ℂ) (s : Set (V n))
    (hs : IsOpen s) (hU : ContDiffOn ℝ ((k + 1 : ℕ)) U s) : ContDiffOn ℝ k (wd n j U) s := by
  have hD : ContDiffOn ℝ k (fun y => fderiv ℝ U y) s :=
    hU.fderiv_of_isOpen hs (by exact_mod_cast le_rfl)
  have h1 := hD.clm_apply (contDiffOn_const (c := bas n j))
  have h2 := hD.clm_apply (contDiffOn_const (c := Complex.I • bas n j))
  exact (h1.sub (contDiffOn_const.mul h2)).div_const 2
end
end ReciprocityTheory.L2DbarEstimates.E
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.E
open MeasureTheory
open scoped ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.E
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (ph : M → ℝ) (j : Fin n) (u : M → ℂ)
    (hph : CkR n z (k + 1) ph) (hu : Ck n z (k + 1) u) : Ck n z k (dTw n z ph j u) := by
  intro e he
  have key : ∀ w ∈ e.target, (dTw n z ph j u ∘ e.symm) w =
      wd n j (u ∘ e.symm) w - (u ∘ e.symm) w * wd n j ((fun y => (ph y : ℂ)) ∘ e.symm) w := by
    intro w hw
    have hs : e.symm w ∈ e.source := e.map_target hw
    have hz : z (e.symm w) = w := by
      rw [he hs]
      exact e.right_inv hw
    simp only [Function.comp_apply, dTw]
    rw [d_eq_wd_comp_chart_symm n z j u e he _ hs, d_eq_wd_comp_chart_symm n z j _ e he _ hs, hz]
  refine ContDiffOn.congr ?_ key
  exact (contDiffOn_wd_of_contDiffOn_succ n j k _ _ e.open_target (hu e he)).sub
    (((hu e he).of_le (by exact_mod_cast Nat.le_succ k)).mul
      (contDiffOn_wd_of_contDiffOn_succ n j k _ _ e.open_target (hph e he)))
end ReciprocityTheory.L2DbarEstimates.E
