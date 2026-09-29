-- Prove2me | solution 1 for VeinottBaseStock.w_isLeast
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:23:42.498117+00:00
-- url     : https://prove2.me/submissions/4c851da9-0e64-4a6e-bdd8-49fc7ca4b7a5

import Mathlib
import Definitions.Def_VeinottBaseStock_Model
import Definitions.Def_VeinottBaseStock_BaseStock

open MeasureTheory ProbabilityTheory

namespace VeinottBaseStock

/-- A nonempty closed chain in `Fin n → ℝ` that is bounded below has a least element. -/
theorem aux_wil_closedChain_least {n : ℕ} (S : Set (Fin n → ℝ)) (hne : S.Nonempty)
    (hbdd : BddBelow S) (hcl : IsClosed S) (hch : IsChain (· ≤ ·) S) :
    ∃ a, IsLeast S a := by
  have hglb : IsGLB S (sInf S) := isGLB_csInf hne hbdd
  have : Nonempty S := hne.to_subtype
  have : IsDirected S (· ≥ ·) := by
    refine ⟨fun a b => ?_⟩
    by_cases hab : a = b
    · exact ⟨a, le_refl _, hab ▸ le_refl _⟩
    · have hne' : (a : Fin n → ℝ) ≠ b := fun h => hab (Subtype.ext h)
      rcases hch a.2 b.2 hne' with h | h
      · exact ⟨a, le_refl _, h⟩
      · exact ⟨b, h, le_refl _⟩
  have ht : Filter.Tendsto ((↑) : S → Fin n → ℝ) Filter.atBot (nhds (sInf S)) :=
    InfConvergenceClass.tendsto_coe_atBot_isGLB _ _ hglb
  have hmem : sInf S ∈ S :=
    hcl.mem_of_tendsto ht (Filter.Eventually.of_forall fun x => x.2)
  exact ⟨sInf S, hmem, hglb.1⟩

theorem aux_wil_isClosed_orderSet {n m : ℕ} (M : Model n m) (ybar : ℕ → Fin n → ℝ)
    (k : ℕ) (x : Fin n → ℝ) (hY : IsClosed (M.Y k)) :
    IsClosed (M.orderSet ybar k x) := by
  unfold Model.orderSet
  refine hY.inter ?_
  have h1 : IsClosed {y : Fin n → ℝ | M.q k x ≤ coeVec y} := by
    have : {y : Fin n → ℝ | M.q k x ≤ coeVec y} =
        ⋂ j, (fun y : Fin n → ℝ => ((y j : ℝ) : EReal)) ⁻¹' Set.Ici (M.q k x j) := by
      ext y
      simp [Pi.le_def, coeVec]
    rw [this]
    refine isClosed_iInter fun j => ?_
    exact isClosed_Ici.preimage (continuous_coe_real_ereal.comp (continuous_apply j))
  have h2 : IsClosed {y : Fin n → ℝ | ybar k ≤ y} := isClosed_le continuous_const continuous_id
  have : {y | M.q k x ≤ coeVec y ∧ ybar k ≤ y} =
      {y : Fin n → ℝ | M.q k x ≤ coeVec y} ∩ {y : Fin n → ℝ | ybar k ≤ y} := rfl
  rw [this]
  exact h1.inter h2

end VeinottBaseStock

open VeinottBaseStock
open MeasureTheory ProbabilityTheory

theorem solution {n m : ℕ} (M : Model n m) (ybar : ℕ → Fin n → ℝ)
    (hM : M.Standing) (h3a : M.H3a ybar) (h3c : M.H3c) (hfeas : M.OrderFeasible)
    (k : ℕ) (x : Fin n → ℝ) (hx : x ∈ M.X k) :
    IsLeast (M.orderSet ybar k x) (M.w ybar k x) ∧
      (M.q k x ≤ coeVec (ybar k) → M.w ybar k x = ybar k) := by
  obtain ⟨hYcl, hYch⟩ := h3c k
  obtain ⟨hybarY, -⟩ := h3a k
  -- nonemptiness
  obtain ⟨y, hyY, hqy⟩ := hfeas k x hx
  have hne : (M.orderSet ybar k x).Nonempty := by
    by_cases hyb : y = ybar k
    · exact ⟨y, hyY, hqy, le_of_eq hyb.symm⟩
    · rcases hYch hyY hybarY hyb with h | h
      · -- y ≤ ybar
        refine ⟨ybar k, hybarY, ?_, le_refl _⟩
        intro j
        exact (hqy j).trans (EReal.coe_le_coe_iff.mpr (h j))
      · exact ⟨y, hyY, hqy, h⟩
  have hbdd : BddBelow (M.orderSet ybar k x) := ⟨ybar k, fun z hz => hz.2.2⟩
  have hcl := aux_wil_isClosed_orderSet M ybar k x hYcl
  have hch : IsChain (· ≤ ·) (M.orderSet ybar k x) := hYch.mono (fun z hz => hz.1)
  have hex : ∃ a, IsLeast (M.orderSet ybar k x) a :=
    aux_wil_closedChain_least _ hne hbdd hcl hch
  have hw : M.w ybar k x = hex.choose := by
    unfold Model.w
    rw [dif_pos hex]
  have hleast : IsLeast (M.orderSet ybar k x) (M.w ybar k x) := by
    rw [hw]; exact hex.choose_spec
  refine ⟨hleast, fun hq => ?_⟩
  have hl2 : IsLeast (M.orderSet ybar k x) (ybar k) :=
    ⟨⟨hybarY, hq, le_refl _⟩, fun z hz => hz.2.2⟩
  exact hleast.unique hl2
