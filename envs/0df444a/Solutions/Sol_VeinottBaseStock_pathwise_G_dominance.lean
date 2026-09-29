-- Prove2me | solution 1 for VeinottBaseStock.pathwise_G_dominance
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:23:43.404717+00:00
-- url     : https://prove2.me/submissions/5f17718a-a343-4a40-ae1d-bacc3ce59ece

import Mathlib
import Definitions.Def_VeinottBaseStock_Model
import Definitions.Def_VeinottBaseStock_BaseStock

open MeasureTheory ProbabilityTheory

namespace VeinottBaseStock

theorem aux_vpg_coeVec_mono {n : ℕ} {y y' : Fin n → ℝ} (h : y ≤ y') :
    coeVec y ≤ coeVec y' :=
  fun j => EReal.coe_le_coe_iff.mpr (h j)

theorem aux_vpg_exists_least {n : ℕ} (S : Set (Fin n → ℝ)) (hS : IsClosed S)
    (hc : IsChain (· ≤ ·) S) (hne : S.Nonempty) (hb : BddBelow S) : ∃ a, IsLeast S a := by
  have hglb : IsGLB S (sInf S) := isGLB_csInf hne hb
  refine ⟨sInf S, ?_, hglb.1⟩
  have : Nonempty S := hne.to_subtype
  have : IsCodirectedOrder S := ⟨fun a b => by
    by_cases h : a = b
    · subst h
      exact ⟨a, le_refl _, le_refl _⟩
    · rcases hc a.2 b.2 (fun e => h (Subtype.ext e)) with h1 | h1
      · exact ⟨a, le_refl _, h1⟩
      · exact ⟨b, h1, le_refl _⟩⟩
  have ht := InfConvergenceClass.tendsto_coe_atBot_isGLB (sInf S) S hglb
  exact hS.mem_of_tendsto ht (Filter.Eventually.of_forall fun x => x.2)

theorem aux_vpg_state_congr {n m : ℕ} (M : Model n m) (ybar : ℕ → Fin n → ℝ)
    (x₁ : Fin n → ℝ) :
    ∀ k (d d' : ℕ → Fin m → ℝ), (∀ j < k, d j = d' j) →
      M.baseStockState ybar x₁ d k = M.baseStockState ybar x₁ d' k := by
  intro k
  induction k with
  | zero => intro d d' _; rfl
  | succ k ih =>
    intro d d' h
    simp only [Model.baseStockState]
    rw [ih d d' (fun j hj => h j (by omega)), h k (by omega)]

theorem aux_vpg_orderSeq_baseStock {n m : ℕ} (M : Model n m) (ybar : ℕ → Fin n → ℝ)
    (x₁ : Fin n → ℝ) (d : ℕ → Fin m → ℝ) (k : ℕ) :
    M.orderSeq (M.baseStock ybar x₁) d k
      = M.baseStockRule ybar k (M.baseStockState ybar x₁ d k) := by
  simp only [Model.orderSeq, Model.baseStock]
  congr 1
  apply aux_vpg_state_congr
  intro j hj
  simp [extendHist, hj]

theorem aux_vpg_stateSeq_mem {n m : ℕ} (M : Model n m) (x₁ : Fin n → ℝ)
    (hM : M.Standing) (hx₁ : x₁ ∈ M.X 0)
    (Ŷ : Pol n m) (hŶ : M.Feasible x₁ Ŷ) (d : ℕ → Fin m → ℝ) (hd : ∀ j, d j ∈ M.Dset j) :
    ∀ k, M.stateSeq Ŷ x₁ d k ∈ M.X k
  | 0 => hx₁
  | k + 1 => hM.s_mem k _ (hŶ.mem_Y k _) (d k) (hd k)

theorem aux_vpg_caseb {n m : ℕ} (M : Model n m) (ybar : ℕ → Fin n → ℝ)
    (h3a : M.H3a ybar) (h3c : M.H3c) (h3d : M.H3d ybar) (k : ℕ) (xs x y : Fin n → ℝ)
    (hxs : xs ∈ M.X k) (hx : x ∈ M.X k) (hle : xs ≤ x) (hq : ¬ M.q k xs ≤ coeVec (ybar k))
    (hy : y ∈ M.Y k) (hqy : M.q k x ≤ coeVec y) :
    M.baseStockRule ybar k xs ∈ M.Y k ∧ ybar k ≤ M.baseStockRule ybar k xs ∧
      M.baseStockRule ybar k xs ≤ y ∧ ybar k ≤ y := by
  have hq' : M.q k xs ≤ coeVec y := le_trans (h3d.2.2 k xs hxs x hx hle hq) hqy
  have hyb : ybar k ≤ y := by
    rcases (h3c k).2.total (h3a k).1 hy with h | h
    · exact h
    · exact absurd (le_trans hq' (aux_vpg_coeVec_mono h)) hq
  have hmem : y ∈ M.orderSet ybar k xs := ⟨hy, hq', hyb⟩
  have hex : ∃ a, IsLeast (M.orderSet ybar k xs) a := by
    apply aux_vpg_exists_least
    · have hcont : Continuous (fun y : Fin n → ℝ => coeVec y) :=
        continuous_pi fun j => continuous_coe_real_ereal.comp (continuous_apply j)
      have h1 : IsClosed {y : Fin n → ℝ | M.q k xs ≤ coeVec y} :=
        isClosed_le continuous_const hcont
      have h2 : IsClosed {y : Fin n → ℝ | ybar k ≤ y} := isClosed_le continuous_const continuous_id
      exact (h3c k).1.inter (h1.inter h2)
    · exact (h3c k).2.mono Set.inter_subset_left
    · exact ⟨y, hmem⟩
    · exact ⟨ybar k, fun z hz => hz.2.2⟩
  have hw : M.baseStockRule ybar k xs = hex.choose := by
    simp only [Model.baseStockRule, if_neg hq, Model.w, dif_pos hex]
  rw [hw]
  have hs := hex.choose_spec
  exact ⟨hs.1.1, hs.1.2.2, hs.2 hmem, hyb⟩

theorem aux_vpg_inv {n m : ℕ} (M : Model n m) (ybar : ℕ → Fin n → ℝ) (x₁ : Fin n → ℝ)
    (hM : M.Standing) (hx₁ : x₁ ∈ M.X 0) (h3a : M.H3a ybar) (h3b : M.H3b ybar) (h3c : M.H3c)
    (h3d : M.H3d ybar)
    (Ŷ : Pol n m) (hŶ : M.Feasible x₁ Ŷ) (d : ℕ → Fin m → ℝ) (hd : ∀ j, d j ∈ M.Dset j) :
    ∀ k, M.baseStockState ybar x₁ d k ∈ M.X k ∧
      (M.q k (M.baseStockState ybar x₁ d k) ≤ coeVec (ybar k) ∨
        M.baseStockState ybar x₁ d k ≤ M.stateSeq Ŷ x₁ d k) := by
  intro k
  induction k with
  | zero => exact ⟨hx₁, Or.inr le_rfl⟩
  | succ k ih =>
    obtain ⟨hX, hor⟩ := ih
    have hstep : M.baseStockState ybar x₁ d (k + 1)
        = M.s k (M.baseStockRule ybar k (M.baseStockState ybar x₁ d k)) (d k) := rfl
    by_cases hq : M.q k (M.baseStockState ybar x₁ d k) ≤ coeVec (ybar k)
    · have hr : M.baseStockRule ybar k (M.baseStockState ybar x₁ d k) = ybar k := by
        simp only [Model.baseStockRule, if_pos hq]
      rw [hstep, hr]
      exact ⟨hM.s_mem k _ (h3a k).1 _ (hd k), Or.inl (h3b k (d k) (hd k))⟩
    · have hle := hor.resolve_left hq
      obtain ⟨hY, hyb, hwy, hyb'⟩ := aux_vpg_caseb M ybar h3a h3c h3d k
        (M.baseStockState ybar x₁ d k) (M.stateSeq Ŷ x₁ d k) (M.orderSeq Ŷ d k) hX
        (aux_vpg_stateSeq_mem M x₁ hM hx₁ Ŷ hŶ d hd k) hle hq (hŶ.mem_Y k _) (hŶ.q_le d hd k)
      rw [hstep]
      refine ⟨hM.s_mem k _ hY _ (hd k), Or.inr ?_⟩
      show _ ≤ M.s k (M.orderSeq Ŷ d k) (d k)
      exact h3d.2.1 k (d k) (hd k) ⟨hY, hyb⟩ ⟨hŶ.mem_Y k _, hyb'⟩ hwy

end VeinottBaseStock

open VeinottBaseStock
open MeasureTheory ProbabilityTheory

theorem solution {n m : ℕ} (M : Model n m) (ybar : ℕ → Fin n → ℝ) (x₁ : Fin n → ℝ)
    (hM : M.Standing) (hx₁ : x₁ ∈ M.X 0) (h3a : M.H3a ybar) (h3b : M.H3b ybar) (h3c : M.H3c)
    (h3d : M.H3d ybar) (hfeas : M.OrderFeasible)
    (Ŷ : Pol n m) (hŶ : M.Feasible x₁ Ŷ) (d : ℕ → Fin m → ℝ) (hd : ∀ j, d j ∈ M.Dset j) :
    ∀ k, M.G k (M.orderSeq (M.baseStock ybar x₁) d k) ≤ M.G k (M.orderSeq Ŷ d k) := by
  intro k
  rw [aux_vpg_orderSeq_baseStock]
  obtain ⟨hX, hor⟩ := aux_vpg_inv M ybar x₁ hM hx₁ h3a h3b h3c h3d Ŷ hŶ d hd k
  by_cases hq : M.q k (M.baseStockState ybar x₁ d k) ≤ coeVec (ybar k)
  · have hr : M.baseStockRule ybar k (M.baseStockState ybar x₁ d k) = ybar k := by
      simp only [Model.baseStockRule, if_pos hq]
    rw [hr]
    exact (h3a k).2 _ (hŶ.mem_Y k _)
  · obtain ⟨hY, hyb, hwy, hyb'⟩ := aux_vpg_caseb M ybar h3a h3c h3d k
      (M.baseStockState ybar x₁ d k) (M.stateSeq Ŷ x₁ d k) (M.orderSeq Ŷ d k) hX
      (aux_vpg_stateSeq_mem M x₁ hM hx₁ Ŷ hŶ d hd k) (hor.resolve_left hq) hq
      (hŶ.mem_Y k _) (hŶ.q_le d hd k)
    exact h3d.1 k ⟨hY, hyb⟩ ⟨hŶ.mem_Y k _, hyb'⟩ hwy
