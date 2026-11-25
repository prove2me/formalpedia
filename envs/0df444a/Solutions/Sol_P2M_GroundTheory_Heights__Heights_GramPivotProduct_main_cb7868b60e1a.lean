-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GramPivotProduct_main_cb7868b60e1a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:42:03.323864+00:00
-- url     : https://prove2.me/submissions/b230df54-927c-4d5f-bf4c-2bda46eac803

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PGramPivotProduct
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GramPivotProduct_pivot_submatrix_7b75b2f54d37
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GramPivotProduct_pivot_pos_9ead156e20bb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GramPivotProduct_intGram_transpose_79e03d83922d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GramPivotProduct_one_le_sq_of_ne_zero_18c0c11e55b7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCCusp_transpose_eq_of_posSemidef_d388a88d8b69


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
open Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.GramPivotProduct
namespace GroundTheory.Heights₂.Heights.GramPivotProduct
theorem _root_.solution (hLL : LeadMinorLeading.Statement) (hLB : LeadMinorBasic.Statement)
    (hPL : PivotLast.Statement) (hU : UnimodularLast.Statement) (hSD : SchurDetBound.Statement)
    (hQ : IntGramQf.Statement) (hUni : IntGramUnimodular.Statement)
    (hDrop : IntGramDropLast.Statement) (hSub : IntGramSubLast.Statement) :
    GramPivotProduct.Statement := by
  intro d
  induction d with
  | zero =>
    intro S hS k N hN
    cases k with
    | zero => exact ⟨∅, by simp, by simp [Matrix.det_isEmpty]⟩
    | succ k =>
      exfalso
      have h0 := hN (Pi.single 0 1) (funext fun i => i.elim0)
      have := congrFun h0 0
      simp at this
  | succ d ih =>
    intro S hS k N hN
    set S' := S.submatrix Fin.castSucc Fin.castSucc with hS'
    have hS'pd : S'.PosDef := hS.submatrix (Fin.castSucc_injective d)
    by_cases hrow : ∀ j, N (Fin.last d) j = 0
    · obtain ⟨P, hP, hprod⟩ := ih S' hS'pd k (N.submatrix Fin.castSucc id) (by
        intro c hc
        apply hN c
        funext i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · simp [mulVec, dotProduct, hrow]
        · exact congrFun hc i)
      refine ⟨P, fun i hi => Nat.lt_succ_of_lt (hP i hi), ?_⟩
      rw [hDrop d k S N hrow]
      calc ∏ i ∈ P, pivot S i = ∏ i ∈ P, pivot S' i :=
            Finset.prod_congr rfl fun i hi => (pivot_submatrix hLL S (hP i hi)).symm
        _ ≤ _ := hprod
    · simp only [not_forall] at hrow
      obtain ⟨j0, hj0⟩ := hrow
      cases k with
      | zero => exact j0.elim0
      | succ k =>
        set ρ : Fin (k + 1) → ℤ := fun j => N (Fin.last d) j with hρ
        have hρ0 : ρ ≠ 0 := fun h => hj0 (congrFun h j0)
        obtain ⟨U, hUdet, hUc, hUl⟩ := hU k ρ hρ0
        set M := N * U with hM
        have hMlast : ∀ j, M (Fin.last d) j = (ρ ᵥ* U) j := fun j => rfl
        set N' : Matrix (Fin d) (Fin k) ℤ := M.submatrix Fin.castSucc Fin.castSucc with hN'
        have hN'ind : ∀ c : Fin k → ℤ, N' *ᵥ c = 0 → c = 0 := by
          intro c hc
          have hMc : M *ᵥ Fin.snoc (α := fun _ => ℤ) c 0 = 0 := by
            funext i
            refine Fin.lastCases ?_ (fun i => ?_) i
            · simp [mulVec, dotProduct, Fin.sum_univ_castSucc, hMlast, hUc]
            · have := congrFun hc i
              simpa [mulVec, dotProduct, Fin.sum_univ_castSucc, hN'] using this
          have hUc0 : U *ᵥ Fin.snoc (α := fun _ => ℤ) c 0 = 0 :=
            hN _ (by rw [mulVec_mulVec]; exact hMc)
          have hsnoc : (Fin.snoc (α := fun _ => ℤ) c 0 : Fin (k + 1) → ℤ) = 0 := by
            have := congrArg (fun v => U⁻¹ *ᵥ v) hUc0
            simpa [mulVec_mulVec, nonsing_inv_mul U hUdet] using this
          funext j
          have := congrFun hsnoc (Fin.castSucc j)
          simpa using this
        obtain ⟨P', hP', hprod'⟩ := ih S' hS'pd k N' hN'ind
        set G := intGram S M with hG
        have hsub : G.submatrix Fin.castSucc Fin.castSucc = intGram S' N' :=
          hSub d k S M (fun j => by rw [hMlast]; exact hUc j)
        have hprodpos : 0 < ∏ i ∈ P', pivot S' i :=
          Finset.prod_pos fun i hi => pivot_pos hLB S' hS'pd (hP' i hi)
        have hG'pos : 0 < (G.submatrix Fin.castSucc Fin.castSucc).det := by
          rw [hsub]
          exact lt_of_lt_of_le hprodpos hprod'
        have hSt : Sᵀ = S := MCCusp.transpose_eq_of_posSemidef hS.posSemidef
        have hGt : Gᵀ = G := intGram_transpose hSt M
        have hpd : 0 < pivot S d := pivot_pos hLB S hS (Nat.lt_succ_self d)
        have hlow : ∀ v : Fin (k + 1) → ℝ, v (Fin.last k) = 1 → pivot S d ≤ MCSchur.qf G v := by
          intro v hv
          rw [hG, hQ]
          have hxl : (M.map (Int.cast : ℤ → ℝ) *ᵥ v) (Fin.last d) =
              ((ρ ᵥ* U) (Fin.last k) : ℝ) := by
            simp [mulVec, dotProduct, Fin.sum_univ_castSucc, hMlast, hUc, hv]
          have h1 : (1 : ℝ) ≤ (M.map (Int.cast : ℤ → ℝ) *ᵥ v) (Fin.last d) ^ 2 := by
            rw [hxl]
            exact one_le_sq_of_ne_zero hUl
          calc pivot S d = 1 * pivot S d := (one_mul _).symm
            _ ≤ (M.map (Int.cast : ℤ → ℝ) *ᵥ v) (Fin.last d) ^ 2 * pivot S d :=
                mul_le_mul_of_nonneg_right h1 hpd.le
            _ ≤ MCSchur.qf S (M.map (Int.cast : ℤ → ℝ) *ᵥ v) := hPL d S hS _
        have hsd := hSD k G hGt hG'pos (pivot S d) hlow
        refine ⟨insert d P', ?_, ?_⟩
        · intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact Nat.lt_succ_self _
          · exact Nat.lt_succ_of_lt (hP' i hi)
        · have hdP : d ∉ P' := fun h => lt_irrefl d (hP' d h)
          rw [Finset.prod_insert hdP, ← hUni (d + 1) (k + 1) S N U hUdet]
          calc pivot S d * ∏ i ∈ P', pivot S i = pivot S d * ∏ i ∈ P', pivot S' i := by
                rw [Finset.prod_congr rfl fun i hi => (pivot_submatrix hLL S (hP' i hi)).symm]
            _ ≤ pivot S d * (G.submatrix Fin.castSucc Fin.castSucc).det := by
                rw [hsub]
                exact mul_le_mul_of_nonneg_left hprod' hpd.le
            _ ≤ G.det := hsd
end GroundTheory.Heights₂.Heights.GramPivotProduct
