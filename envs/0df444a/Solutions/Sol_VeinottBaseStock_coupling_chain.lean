-- Prove2me | solution 1 for VeinottBaseStock.coupling_chain
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:52:09.69781+00:00
-- url     : https://prove2.me/submissions/6dfbb1e4-39c2-439e-b191-cb5024159b41

import Mathlib
import Definitions.Def_VeinottBaseStock_Model
import Definitions.Def_VeinottBaseStock_BaseStock

open MeasureTheory ProbabilityTheory

namespace VeinottBaseStock

lemma aux_cc_coeVec_mono {n : ℕ} {a b : Fin n → ℝ} (h : a ≤ b) : coeVec a ≤ coeVec b :=
  fun j => EReal.coe_le_coe_iff.mpr (h j)

lemma aux_cc_closed_le {n : ℕ} (q : Fin n → EReal) :
    IsClosed {y : Fin n → ℝ | q ≤ coeVec y} := by
  have : Continuous (fun y : Fin n → ℝ => coeVec y) :=
    continuous_pi (fun j => continuous_coe_real_ereal.comp (continuous_apply j))
  exact isClosed_le continuous_const this

lemma aux_cc_closed_chain_least {n : ℕ} {S : Set (Fin n → ℝ)} (hc : IsClosed S)
    (hch : IsChain (· ≤ ·) S) (hne : S.Nonempty) (hb : BddBelow S) :
    ∃ a, IsLeast S a := by
  have hglb : IsGLB S (sInf S) := isGLB_csInf hne hb
  refine ⟨sInf S, ?_, hglb.1⟩
  have : Nonempty S := hne.to_subtype
  have : IsDirected S (· ≥ ·) := ⟨fun a b => by
    rcases hch.total a.2 b.2 with h | h
    · exact ⟨a, le_refl _, h⟩
    · exact ⟨b, h, le_refl _⟩⟩
  have hmono : Monotone (Subtype.val : S → Fin n → ℝ) := fun a b h => h
  have hr : Set.range (Subtype.val : S → Fin n → ℝ) = S := Subtype.range_val
  have hglb' : IsGLB (Set.range (Subtype.val : S → Fin n → ℝ)) (sInf S) := by
    rw [hr]; exact hglb
  have ht := tendsto_atBot_isGLB hmono hglb'
  exact hc.mem_of_tendsto ht (Filter.Eventually.of_forall fun a => a.2)

lemma aux_cc_least {n m : ℕ} {M : Model n m} {ybar : ℕ → Fin n → ℝ} (h3a : M.H3a ybar)
    (h3c : M.H3c) (hfeas : M.OrderFeasible) {k : ℕ} {x : Fin n → ℝ} (hx : x ∈ M.X k) :
    ∃ a, IsLeast (M.orderSet ybar k x) a := by
  apply aux_cc_closed_chain_least
  · exact ((h3c k).1.inter ((aux_cc_closed_le _).inter isClosed_Ici))
  · exact (h3c k).2.mono Set.inter_subset_left
  · obtain ⟨y, hy, hq⟩ := hfeas k x hx
    rcases (h3c k).2.total hy (h3a k).1 with h | h
    · exact ⟨ybar k, (h3a k).1, le_trans hq (aux_cc_coeVec_mono h), le_refl _⟩
    · exact ⟨y, hy, hq, h⟩
  · exact ⟨ybar k, fun y hy => hy.2.2⟩

lemma aux_cc_w_spec {n m : ℕ} {M : Model n m} {ybar : ℕ → Fin n → ℝ} (h3a : M.H3a ybar)
    (h3c : M.H3c) (hfeas : M.OrderFeasible) {k : ℕ} {x : Fin n → ℝ} (hx : x ∈ M.X k) :
    IsLeast (M.orderSet ybar k x) (M.w ybar k x) := by
  have h := aux_cc_least h3a h3c hfeas hx
  unfold Model.w
  rw [dif_pos h]
  exact h.choose_spec

lemma aux_cc_w_mem {n m : ℕ} {M : Model n m} {ybar : ℕ → Fin n → ℝ} (h3a : M.H3a ybar)
    {k : ℕ} {x : Fin n → ℝ} : M.w ybar k x ∈ M.Y k := by
  unfold Model.w
  split_ifs with h
  · exact h.choose_spec.1.1
  · exact (h3a k).1

lemma aux_cc_rule_mem {n m : ℕ} {M : Model n m} {ybar : ℕ → Fin n → ℝ} (h3a : M.H3a ybar)
    {k : ℕ} {x : Fin n → ℝ} : M.baseStockRule ybar k x ∈ M.Y k := by
  unfold Model.baseStockRule
  split_ifs
  · exact (h3a k).1
  · exact aux_cc_w_mem h3a

lemma aux_cc_bss_congr {n m : ℕ} (M : Model n m) (ybar : ℕ → Fin n → ℝ) (x₁ : Fin n → ℝ)
    {d d' : ℕ → Fin m → ℝ} :
    ∀ k, (∀ j < k, d j = d' j) → M.baseStockState ybar x₁ d k = M.baseStockState ybar x₁ d' k
  | 0, _ => rfl
  | k + 1, h => by
    simp only [Model.baseStockState]
    rw [aux_cc_bss_congr M ybar x₁ k (fun j hj => h j (by omega)), h k (by omega)]

lemma aux_cc_order {n m : ℕ} (M : Model n m) (ybar : ℕ → Fin n → ℝ) (x₁ : Fin n → ℝ)
    (d : ℕ → Fin m → ℝ) (k : ℕ) :
    M.orderSeq (M.baseStock ybar x₁) d k =
      M.baseStockRule ybar k (M.baseStockState ybar x₁ d k) := by
  unfold Model.orderSeq Model.baseStock
  congr 1
  apply aux_cc_bss_congr
  intro j hj
  simp [extendHist, hj]

lemma aux_cc_state {n m : ℕ} (M : Model n m) (ybar : ℕ → Fin n → ℝ) (x₁ : Fin n → ℝ)
    (d : ℕ → Fin m → ℝ) : ∀ k,
    M.stateSeq (M.baseStock ybar x₁) x₁ d k = M.baseStockState ybar x₁ d k
  | 0 => rfl
  | k + 1 => by
    simp only [Model.stateSeq, Model.baseStockState]
    rw [aux_cc_order]

lemma aux_cc_step {n m : ℕ} {M : Model n m} {ybar : ℕ → Fin n → ℝ} (h3a : M.H3a ybar)
    (h3c : M.H3c) (h3d : M.H3d ybar) (hfeas : M.OrderFeasible) {k : ℕ} {xs x y : Fin n → ℝ}
    (hxs : xs ∈ M.X k) (hx : x ∈ M.X k) (hle : xs ≤ x)
    (hnot : ¬ M.q k xs ≤ coeVec (ybar k))
    (hy : y ∈ M.Y k) (hqy : M.q k x ≤ coeVec y) :
    ybar k < M.w ybar k xs ∧ M.w ybar k xs ≤ M.w ybar k x ∧ M.w ybar k x ≤ y := by
  have hws := aux_cc_w_spec h3a h3c hfeas hxs
  have hw := aux_cc_w_spec h3a h3c hfeas hx
  have hqq : M.q k xs ≤ M.q k x := h3d.2.2 k xs hxs x hx hle hnot
  refine ⟨?_, ?_, ?_⟩
  · refine lt_of_le_of_ne hws.1.2.2 ?_
    intro heq
    apply hnot
    have := hws.1.2.1
    rw [← heq] at this
    exact this
  · apply hws.2
    exact ⟨hw.1.1, le_trans hqq hw.1.2.1, hw.1.2.2⟩
  · apply hw.2
    refine ⟨hy, hqy, ?_⟩
    rcases (h3c k).2.total hy (h3a k).1 with h | h
    · exfalso
      apply hnot
      exact le_trans hqq (le_trans hqy (aux_cc_coeVec_mono h))
    · exact h

end VeinottBaseStock

open VeinottBaseStock
open MeasureTheory ProbabilityTheory

theorem solution {n m : ℕ} (M : Model n m) (ybar : ℕ → Fin n → ℝ) (x₁ : Fin n → ℝ)
    (hM : M.Standing) (hx₁ : x₁ ∈ M.X 0) (h3a : M.H3a ybar) (h3b : M.H3b ybar) (h3c : M.H3c)
    (h3d : M.H3d ybar) (hfeas : M.OrderFeasible)
    (Ŷ : Pol n m) (hŶ : M.Feasible x₁ Ŷ) (d : ℕ → Fin m → ℝ) (hd : ∀ j, d j ∈ M.Dset j)
    (k : ℕ)
    (hbefore : ∀ j ≤ k, ¬ M.q j (M.stateSeq (M.baseStock ybar x₁) x₁ d j) ≤ coeVec (ybar j)) :
    ybar k < M.orderSeq (M.baseStock ybar x₁) d k ∧
      M.orderSeq (M.baseStock ybar x₁) d k =
        M.w ybar k (M.stateSeq (M.baseStock ybar x₁) x₁ d k) ∧
      M.w ybar k (M.stateSeq (M.baseStock ybar x₁) x₁ d k) ≤
        M.w ybar k (M.stateSeq Ŷ x₁ d k) ∧
      M.w ybar k (M.stateSeq Ŷ x₁ d k) ≤ M.orderSeq Ŷ d k := by
  have hYmem : ∀ j, M.orderSeq Ŷ d j ∈ M.Y j := fun j => hŶ.mem_Y j _
  have hYsmem : ∀ j, M.orderSeq (M.baseStock ybar x₁) d j ∈ M.Y j := by
    intro j
    rw [aux_cc_order]
    exact aux_cc_rule_mem h3a
  have hX : ∀ j, M.stateSeq Ŷ x₁ d j ∈ M.X j := by
    intro j
    cases j with
    | zero => exact hx₁
    | succ j =>
      show M.s j (M.orderSeq Ŷ d j) (d j) ∈ M.X (j + 1)
      exact hM.s_mem j _ (hYmem j) _ (hd j)
  have hXs : ∀ j, M.stateSeq (M.baseStock ybar x₁) x₁ d j ∈ M.X j := by
    intro j
    cases j with
    | zero => exact hx₁
    | succ j =>
      show M.s j (M.orderSeq (M.baseStock ybar x₁) d j) (d j) ∈ M.X (j + 1)
      exact hM.s_mem j _ (hYsmem j) _ (hd j)
  have hystar : ∀ j, ¬ M.q j (M.stateSeq (M.baseStock ybar x₁) x₁ d j) ≤ coeVec (ybar j) →
      M.orderSeq (M.baseStock ybar x₁) d j =
        M.w ybar j (M.stateSeq (M.baseStock ybar x₁) x₁ d j) := by
    intro j hnot
    rw [aux_cc_order, ← aux_cc_state]
    unfold Model.baseStockRule
    rw [if_neg hnot]
  have hmono : ∀ j ≤ k, M.stateSeq (M.baseStock ybar x₁) x₁ d j ≤ M.stateSeq Ŷ x₁ d j := by
    intro j
    induction j with
    | zero => intro _; exact le_refl _
    | succ j ih =>
      intro hj
      have hjk : j ≤ k := by omega
      have hle := ih hjk
      have hnot := hbefore j hjk
      obtain ⟨h1, h2, h3⟩ := aux_cc_step (y := M.orderSeq Ŷ d j) h3a h3c h3d hfeas
        (hXs j) (hX j) hle hnot (hYmem j) (hŶ.q_le d hd j)
      have hys := hystar j hnot
      show M.s j (M.orderSeq (M.baseStock ybar x₁) d j) (d j) ≤
        M.s j (M.orderSeq Ŷ d j) (d j)
      rw [hys]
      apply h3d.2.1 j (d j) (hd j)
      · exact ⟨aux_cc_w_mem h3a, h1.le⟩
      · exact ⟨hYmem j, le_trans h1.le (le_trans h2 h3)⟩
      · exact le_trans h2 h3
  have hle := hmono k le_rfl
  have hnot := hbefore k le_rfl
  obtain ⟨h1, h2, h3⟩ := aux_cc_step (y := M.orderSeq Ŷ d k) h3a h3c h3d hfeas
    (hXs k) (hX k) hle hnot (hYmem k) (hŶ.q_le d hd k)
  have hys := hystar k hnot
  refine ⟨?_, hys, h2, h3⟩
  rw [hys]
  exact h1
