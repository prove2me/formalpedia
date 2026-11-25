-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartFormsAlt_exists_form_of_mem_chartRing_e51b8144b218
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:48:26.57963+00:00
-- url     : https://prove2.me/submissions/9949e14a-54cd-48ae-8878-12f1b0a27e4b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_ExistsFormOfMemChartRing
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartFormsAlt_chartMonomial_add_31144b20e51b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartFormsAlt_chartMonomial_zero_b41998796e10
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartFormsAlt_chartMonomial_single_631243a33806
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mkF_eq_zero_iff_91580b64c057


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartFormsAlt
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.ChartFormsAlt
theorem _root_.solution (P : ArithVariety n) (c : (k : ι) → Fin (n k + 1))
    (hc : P.IsLive c) {x : P.FunField} (hx : x ∈ P.chartRing c) :
    ∃ (F : MvPolynomial (Coord n) ℤ) (e : ι → ℕ), IsWeightedHomogeneous (coordDeg n) F e ∧
      x * P.mkF (chartMonomial c e) = P.mkF F := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    have hne : P.mkF (X ⟨v.1, c v.1⟩) ≠ 0 := fun h ↦ hc v.1 ((P.mkF_eq_zero_iff _).mp h)
    refine ⟨X v, Pi.single v.1 1, ?_, ?_⟩
    · have h := isWeightedHomogeneous_X (R := ℤ) (coordDeg n) v
      simpa [coordDeg] using h
    · rw [chartMonomial_single, ArithVariety.chartCoord, div_mul_cancel₀ _ hne]
  | zero => exact ⟨0, 0, isWeightedHomogeneous_zero _ _ _, by simp⟩
  | one => exact ⟨1, 0, isWeightedHomogeneous_one _ _, by simp [chartMonomial_zero]⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨F, e, hF, hxF⟩ := ihx
    obtain ⟨F', e', hF', hyF⟩ := ihy
    refine ⟨F * chartMonomial c e' + F' * chartMonomial c e, e + e', ?_, ?_⟩
    · refine (hF.mul (isWeightedHomogeneous_chartMonomial c e')).add ?_
      rw [add_comm e e']
      exact hF'.mul (isWeightedHomogeneous_chartMonomial c e)
    · rw [chartMonomial_add, map_add, map_mul, map_mul, map_mul, ← hxF, ← hyF]
      ring
  | neg x _ ih =>
    obtain ⟨F, e, hF, hxF⟩ := ih
    exact ⟨-F, e, hF.neg, by rw [map_neg, ← hxF, neg_mul]⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨F, e, hF, hxF⟩ := ihx
    obtain ⟨F', e', hF', hyF⟩ := ihy
    refine ⟨F * F', e + e', hF.mul hF', ?_⟩
    rw [chartMonomial_add, map_mul, map_mul, ← hxF, ← hyF]
    ring
end GroundTheory.Heights₂.Heights.ChartFormsAlt
