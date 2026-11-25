-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.det_near_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:40:29.276927+00:00
-- url     : https://prove2.me/submissions/08242af5-eedf-45bb-ba84-f8a040d6fc2f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfH

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
theorem _root_.solution (n : ℕ) : ∃ η > 0, ∀ A : Matrix (Fin n) (Fin n) ℂ,
    (∀ i j, ‖A i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ < η) → 1 / 2 ≤ ‖A.det‖ := by
  set g : (Fin n → Fin n → ℂ) → ℂ :=
    fun A => ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, A (σ i) i with hg
  have hgc : Continuous g := by rw [hg]; fun_prop
  have hgdet : ∀ A : Matrix (Fin n) (Fin n) ℂ, A.det = g A := fun A => Matrix.det_apply A
  set I : Fin n → Fin n → ℂ := (1 : Matrix (Fin n) (Fin n) ℂ) with hI
  have hgI : g I = 1 := by rw [← hgdet]; exact Matrix.det_one
  obtain ⟨η, hη, h⟩ := Metric.continuousAt_iff.1 hgc.continuousAt (1 / 2 : ℝ) (by norm_num)
  refine ⟨η, hη, fun A hA => ?_⟩
  have hd : dist (Matrix.of.symm A) I < η :=
    (dist_pi_lt_iff hη).2 fun i => (dist_pi_lt_iff hη).2 fun j => by rw [dist_eq_norm]; exact hA i j
  have h2 := h hd
  have h4 : g (Matrix.of.symm A) = A.det := (hgdet A).symm
  rw [hgI, h4, dist_eq_norm] at h2
  have h3 := norm_sub_norm_le (1 : ℂ) A.det
  rw [norm_sub_rev, norm_one] at h3
  linarith
end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
