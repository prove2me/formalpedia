-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.psh_line
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:52.315581+00:00
-- url     : https://prove2.me/submissions/0ad15958-9dd9-4849-a1a3-652b8b5fd019

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Real Filter Topology MeasureTheory
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
open ReciprocityTheory.AnForm.A
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
theorem _root_.solution {V : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ} (h : IsPsh V φ)
    (z w : Fin D → ℂ) {a : ℂ} {s : ℝ} (hs : 0 < s)
    (hV : ∀ ζ ∈ closedBall a s, z + ζ • w ∈ V) :
    CircleIntegrable (fun ζ => φ (z + ζ • w)) a s ∧
      φ (z + a • w) ≤ circleAverage (fun ζ => φ (z + ζ • w)) a s := by
  have key : ∀ θ : ℝ, z + circleMap a s θ • w = (z + a • w) + circleMap 0 1 θ • ((s : ℂ) • w) := by
    intro θ
    ext i
    simp only [circleMap, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_one]
    ring
  have hU : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → (z + a • w) + ζ • ((s : ℂ) • w) ∈ V := by
    intro ζ hζ
    have hn : ‖(s : ℂ) * ζ‖ ≤ s := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le]
      nlinarith [norm_nonneg ζ]
    have h1 : a + (s : ℂ) * ζ ∈ closedBall a s := by
      rw [mem_closedBall, dist_eq_norm]
      simpa using hn
    have h2 := hV _ h1
    have e : z + (a + (s : ℂ) * ζ) • w = (z + a • w) + ζ • ((s : ℂ) • w) := by
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e] at h2
    exact h2
  obtain ⟨hi, hle⟩ := h.2 (z + a • w) ((s : ℂ) • w) hU
  refine ⟨?_, ?_⟩
  · unfold CircleIntegrable at hi ⊢
    simpa only [key] using hi
  · unfold Real.circleAverage at hle ⊢
    simpa only [key] using hle
end ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
