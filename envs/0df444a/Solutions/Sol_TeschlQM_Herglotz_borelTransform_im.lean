-- Prove2me | solution 1 for TeschlQM.Herglotz.borelTransform_im
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-05T00:30:50.898423+00:00
-- url     : https://prove2.me/submissions/01c4fbd1-65e6-464f-85bd-1fd0a3a7f3b2

import Definitions.Def_TeschlQM_Herglotz_borelTransform
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.NormNum

open MeasureTheory Filter Set
open scoped Topology

namespace HerglotzStieltjes


end HerglotzStieltjes

open HerglotzStieltjes

theorem solution (μ : Measure ℝ) [IsFiniteMeasure μ] (t ε : ℝ) (hε : 0 < ε) :
    (TeschlQM.Herglotz.borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im =
      ∫ x : ℝ, ε / ((x - t)^2 + ε^2) ∂μ := by
  let z : ℂ := (t : ℂ) + (ε : ℂ) * Complex.I
  have hz : z.im = ε := by simp [z]
  have hi : Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹) μ := by
    apply Integrable.of_bound ((Complex.measurable_ofReal.sub_const z).inv).aestronglyMeasurable ε⁻¹
    apply Eventually.of_forall
    intro x
    change ‖((x : ℂ) - z)⁻¹‖ ≤ ε⁻¹
    rw [norm_inv]
    apply inv_anti₀ hε
    calc
      ε = |((x : ℂ) - z).im| := by simp [hz, abs_of_pos hε]
      _ ≤ ‖(x : ℂ) - z‖ := Complex.abs_im_le_norm _
  unfold TeschlQM.Herglotz.borelTransform
  change RCLike.im (∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂μ) = _
  rw [← integral_im hi]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  simp [Complex.normSq_apply, z, pow_two]

