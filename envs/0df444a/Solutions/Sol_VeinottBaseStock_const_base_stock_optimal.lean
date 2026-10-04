-- Prove2me | solution 1 for VeinottBaseStock.const_base_stock_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T20:22:44.50878+00:00
-- url     : https://prove2.me/submissions/d058663a-95df-4c84-b0ff-8c3959bc553f

import Mathlib
import Definitions.Def_VeinottBaseStock_Model
import Definitions.Def_VeinottBaseStock_BaseStock

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

open VeinottBaseStock MeasureTheory ProbabilityTheory in
theorem solution {n m : ℕ} (M : Model n m) (ybar : ℕ → Fin n → ℝ)
    (x₁ : Fin n → ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℕ → Ω → Fin m → ℝ) (hM : M.Standing) (hD : M.IsDemandProcess P D)
    (hx₁ : x₁ ∈ M.X 0) (h3a : M.H3a ybar) (h3b : M.H3b ybar)
    (hq : M.q 0 x₁ ≤ coeVec (ybar 0)) :
    M.IsOptimal x₁ P D (fun k _ => ybar k) ∧
      M.cost P D (fun k _ => ybar k) =
        (((∑' k, ENNReal.ofReal (M.β k * (M.G k (ybar k) - M.γ k)) : ENNReal)) : EReal) +
          ((∑' k, M.β k * M.γ k : ℝ) : EReal) := by
  have hfeas : M.Feasible x₁ (fun k _ => ybar k) := by
    refine ⟨fun k => measurable_const, fun k _ => (h3a k).1, ?_⟩
    intro d hd k
    cases k with
    | zero => exact hq
    | succ k => exact h3b k (d k) (hd k)
  have hexc : M.excess P D (fun k _ => ybar k) =
      ∑' k, ENNReal.ofReal (M.β k * (M.G k (ybar k) - M.γ k)) := by
    unfold Model.excess
    congr 1
    funext k
    simp [Model.orderSeq, lintegral_const, measure_univ]
  refine ⟨⟨hfeas, fun Y' hF => ?_⟩, ?_⟩
  · unfold Model.cost
    refine add_le_add_left (EReal.coe_ennreal_le_coe_ennreal_iff.mpr ?_) _
    unfold Model.excess
    refine ENNReal.tsum_le_tsum fun k => lintegral_mono fun ω => ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have hβ : 0 ≤ M.β k := Finset.prod_nonneg fun j _ => hM.alpha_nonneg j
    have hG : M.G k (ybar k) ≤ M.G k (M.orderSeq Y' (fun j => D j ω) k) :=
      (h3a k).2 _ (hF.mem_Y k _)
    have h0 : M.orderSeq (fun k _ => ybar k) (fun j => D j ω) k = ybar k := rfl
    rw [h0]
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right hG _) hβ
  · unfold Model.cost
    rw [hexc]
