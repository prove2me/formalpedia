-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.green_of_poincareLelongHyperplane
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:22:45.260645+00:00
-- url     : https://prove2.me/submissions/9e1863c1-23f0-43b0-9c8a-7b82654db28a

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenOfPoincareLelongHyperplane

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (h : PoincareLelongHyperplane) (u : (Fin 1 → ℂ) → ℝ) (hu : ContDiff ℝ 3 u)
    (hcs : HasCompactSupport u) :
    Integrable (fun z : Fin 1 → ℂ => Real.log ‖z 0‖ * ReciprocityTheory.AnForm.maDens ![u] z) ∧
      ∫ z : Fin 1 → ℂ, Real.log ‖z 0‖ * ReciprocityTheory.AnForm.maDens ![u] z = u 0 := by
  obtain ⟨h1, -, h3⟩ := h 0 Set.univ u Fin.elim0
    ⟨isOpen_univ, hu, hcs, Set.subset_univ _, fun k => k.elim0⟩
  have hv : densV u (Fin.elim0 : Fin 0 → (Fin 1 → ℂ) → ℝ) = ReciprocityTheory.AnForm.maDens ![u] := by
    funext z; rfl
  rw [hv] at h1 h3
  refine ⟨h1, ?_⟩
  rw [h3]
  have hw : ∀ w : Fin 0 → ℂ,
      u (hypIncl w) * densHyp (Fin.elim0 : Fin 0 → (Fin 1 → ℂ) → ℝ) w = u 0 := by
    intro w
    have e1 : hypIncl w = 0 := by
      funext j
      refine Fin.cases rfl (fun i => i.elim0) j
    have e2 : densHyp (Fin.elim0 : Fin 0 → (Fin 1 → ℂ) → ℝ) w = 1 := by
      simp [densHyp, ReciprocityTheory.AnForm.maDens, ReciprocityTheory.AnForm.mdisc]
    rw [e1, e2, mul_one]
  simp_rw [hw]
  simp [MeasureTheory.integral_const, MeasureTheory.volume_pi, MeasureTheory.measureReal_def,
    MeasureTheory.Measure.pi_univ]
end ReciprocityTheory.AnForm.A
