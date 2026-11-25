-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.sh_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:32:40.432888+00:00
-- url     : https://prove2.me/submissions/7a4c8c94-251d-4192-8d9c-736aea6f76c0

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ShellA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_shG_apply
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_shG_contDiffOn
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_sh_jac
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology Set
open scoped ENNReal ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (hg : ∀ i, Holo n z (g i)) (p : M) (hp : p ∈ zeroSet n g)
    (hJ : jac n z g p ≠ 0) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e)
    (hpe : p ∈ e.source) :
    ∃ ρ > 0, ball (e p) ρ ⊆ e.target ∧ InjOn (shG n g e.symm) (ball (e p) ρ) ∧
      ∀ ρ' > 0, ∃ κ > 0, ∀ y ∈ ball (e p) ρ, ‖shG n g e.symm y‖ < κ → y ∈ ball (e p) ρ' := by
  have hy0 : e p ∈ e.target := e.map_source hpe
  have hcd : ContDiffAt ℂ ∞ (shG n g e.symm) (e p) :=
    (shG_contDiffOn n z g hg e he).contDiffAt (e.open_target.mem_nhds hy0)
  have hdet : (fderiv ℂ (shG n g e.symm) (e p)).det ≠ 0 := by
    have h := sh_jac n z g hg e he (e p) hy0
    rw [e.left_inv hpe] at h
    rw [ContinuousLinearMap.det, ← h]
    exact hJ
  set f' := (fderiv ℂ (shG n g e.symm) (e p)).toContinuousLinearEquivOfDetNeZero hdet
  have hf' : HasFDerivAt (shG n g e.symm) (f' : V n →L[ℂ] V n) (e p) := by
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact (hcd.differentiableAt (by simp)).hasFDerivAt
  have hn0 : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  set Φ := hcd.toOpenPartialHomeomorph (shG n g e.symm) hf' hn0
  have hΦ : (Φ : V n → V n) = shG n g e.symm := rfl
  have hsrc : e p ∈ Φ.source := hcd.mem_toOpenPartialHomeomorph_source hf' hn0
  have htgt : shG n g e.symm (e p) ∈ Φ.target :=
    hcd.image_mem_toOpenPartialHomeomorph_target hf' hn0
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 (e.open_target.inter Φ.open_source) (e p)
    ⟨hy0, hsrc⟩
  refine ⟨ρ, hρ, fun y hy => (hball hy).1, ?_, ?_⟩
  · rw [← hΦ]
    exact Φ.injOn.mono fun y hy => (hball hy).2
  intro ρ' hρ'
  have hG0 : shG n g e.symm (e p) = 0 := by
    ext i
    rw [shG_apply, e.left_inv hpe]
    exact hp i
  have hsymm : Φ.symm (shG n g e.symm (e p)) = e p := by
    rw [← hΦ]
    exact Φ.left_inv hsrc
  have hc : ContinuousAt Φ.symm (shG n g e.symm (e p)) := Φ.continuousAt_symm htgt
  have hmem : Φ.symm ⁻¹' ball (e p) ρ' ∈ 𝓝 (shG n g e.symm (e p)) :=
    hc.preimage_mem_nhds (by rw [hsymm]; exact ball_mem_nhds _ hρ')
  obtain ⟨κ, hκ, hκb⟩ := Metric.mem_nhds_iff.1 hmem
  refine ⟨κ, hκ, fun y hy hGy => ?_⟩
  have h1 : shG n g e.symm y ∈ ball (shG n g e.symm (e p)) κ := by
    rw [hG0, mem_ball_zero_iff]
    exact hGy
  have h2 := hκb h1
  simp only [mem_preimage] at h2
  rwa [← hΦ, Φ.left_inv (hball hy).2] at h2
end ReciprocityTheory.L2DbarEstimates.I
