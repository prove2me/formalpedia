-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.logMahlerMeasure_comp_C_mul_X_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:48:14.326951+00:00
-- url     : https://prove2.me/submissions/fd0508ee-975f-4b6c-b582-6138457cbb88

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereTorusA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Polynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (p : ℂ[X]) {c : ℂ} (hc : c ≠ 0) (hc1 : ‖c‖ ≤ 1) :
    (p.comp (C c * X)).logMahlerMeasure ≤ p.logMahlerMeasure := by
  by_cases hp : p = 0
  · simp [hp]
  have hq : p.comp (C c * X) ≠ 0 := by
    intro h
    apply hp
    have h' := congrArg (fun r => r.comp (C c⁻¹ * X)) h
    have hX : (C c * X).comp (C c⁻¹ * X) = (X : ℂ[X]) := by
      simp [← mul_assoc, ← C_mul, mul_inv_cancel₀ hc]
    simpa [Polynomial.comp_assoc, hX] using h'
  have key : ∀ s : Multiset ℂ, (((s.map fun a => X - C a).prod).comp (C c * X)).mahlerMeasure ≤
      ((s.map fun a => X - C a).prod).mahlerMeasure := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, mul_comp, mahlerMeasure_mul]
      apply mul_le_mul _ ih (mahlerMeasure_nonneg _) (mahlerMeasure_nonneg _)
      have h1 : (X - C a).comp (C c * X) = C c * X + C (-a) := by
        simp [sub_eq_add_neg]
      rw [h1, mahlerMeasure_C_mul_X_add_C hc, mahlerMeasure_X_sub_C, norm_neg]
      exact max_le_max hc1 le_rfl
  rw [logMahlerMeasure_eq_log_MahlerMeasure, logMahlerMeasure_eq_log_MahlerMeasure]
  apply Real.log_le_log (mahlerMeasure_pos_of_ne_zero hq)
  have hs := (IsAlgClosed.splits p).eq_prod_roots
  rw [hs, mul_comp, C_comp, mahlerMeasure_mul, mahlerMeasure_mul]
  exact mul_le_mul_of_nonneg_left (key _) (mahlerMeasure_nonneg _)
end ReciprocityTheory.MultiplicativeHeights
