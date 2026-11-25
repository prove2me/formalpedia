-- Prove2me | solution 1 for P2M_GlobalTheory_StepData_Model_opE_ne_zero__77ad6a831e75
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:34:19.757455+00:00
-- url     : https://prove2.me/submissions/3603d3ad-e1d8-4c8f-ad86-9c1af2103b25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_TypeChainPrincipalEntryNeZero
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space
import Theorems.Thm_GlobalTheory_StepData_IntM_add
import Theorems.Thm_GlobalTheory_StepData_MaxM_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.StepData GlobalTheory.StepData.Model
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable [MeasurableSpace k] [BorelSpace k]
omit [DecidableEq n] [DecidableEq n']
namespace GlobalTheory.StepData.Model
theorem _root_.solution (ψ : AddChar k Circle) (ν : Measure k)
    [ν.IsAddHaarMeasure] (p : ℕ) {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} (hΦ : Φ ∈ SB _)
    (h01 : ∀ x, Φ x ≠ 0 → Φ x = ψ (ch x)) {x₀ : Matrix n n' k} {e₀} (he : Φ (affPt p x₀ e₀) ≠ 0) :
    opE ψ ν p Φ x₀ ≠ 0 := by
  classical
  have := secondCountable k
  have := t2Space k
  have hc : Continuous (affPt (c := c) p x₀) := by
    refine continuous_const.add (continuous_pi fun r => continuous_pi fun s => ?_)
    by_cases hf : Free p (r, s)
    · simp only [Matrix.of_apply, dif_pos hf]; exact continuous_apply _
    · simp only [Matrix.of_apply, dif_neg hf]; exact continuous_const
  have key : ∀ e, Φ (affPt p x₀ e) * (ψ (-ch (affPt p x₀ e)) : ℂ) = (‖Φ (affPt p x₀ e)‖ : ℝ) := fun e => by
    by_cases h : Φ (affPt p x₀ e) = 0
    · simp [h]
    · rw [h01 _ h, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, Circle.norm_coe]; simp
  unfold opE
  simp only [key]
  rw [integral_complex_ofReal, Complex.ofReal_ne_zero]
  refine (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (hΦ.1.continuous.comp hc).norm ?_
    (fun _ => norm_nonneg _) (x := e₀) (norm_ne_zero_iff.2 he)).ne'
  refine HasCompactSupport.intro (IsCompact.image hΦ.2
    (f := fun x (rs : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs}) =>
      x rs.1.1 rs.1.2 - basePt c x₀ rs.1.1 rs.1.2) (by fun_prop))
    fun e he' => norm_eq_zero.2 (by_contra fun h => he' ⟨_, subset_tsupport _ h, ?_⟩)
  funext ⟨⟨r, s⟩, hf⟩
  simp [affPt, hf]
end GlobalTheory.StepData.Model
