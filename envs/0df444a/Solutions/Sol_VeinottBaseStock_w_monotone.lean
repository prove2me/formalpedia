-- Prove2me | solution 1 for VeinottBaseStock.w_monotone
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:32:28.791883+00:00
-- url     : https://prove2.me/submissions/9ef91de7-a95e-4702-9797-c5354265ae96

import Mathlib
import Definitions.Def_VeinottBaseStock_Model
import Definitions.Def_VeinottBaseStock_BaseStock

open MeasureTheory ProbabilityTheory

namespace VeinottBaseStock

/-- A nonempty closed chain in `ℝⁿ` that is bounded below has a least element. -/
theorem aux_vbwm_least {n : ℕ} (S : Set (Fin n → ℝ)) (hS : IsClosed S)
    (hc : IsChain (· ≤ ·) S) (b : Fin n → ℝ) (hb : ∀ y ∈ S, b ≤ y) (hne : S.Nonempty) :
    ∃ a, IsLeast S a := by
  obtain ⟨c, hcS⟩ := hne
  have hK : IsCompact (S ∩ Set.Icc b c) := isCompact_Icc.inter_left hS
  have hKne : (S ∩ Set.Icc b c).Nonempty := ⟨c, hcS, hb c hcS, le_rfl⟩
  have hcont : Continuous (fun y : Fin n → ℝ => ∑ j, y j) := by fun_prop
  obtain ⟨a, haK, hmin⟩ := hK.exists_isMinOn hKne hcont.continuousOn
  refine ⟨a, haK.1, ?_⟩
  intro y hy
  rcases eq_or_ne a y with h | h
  · exact h.le
  rcases hc haK.1 hy h with h1 | h1
  · exact h1
  · exfalso
    have hyK : y ∈ S ∩ Set.Icc b c := ⟨hy, hb y hy, h1.trans haK.2.2⟩
    have hm : (∑ j, a j) ≤ ∑ j, y j := hmin hyK
    have hlt : y < a := lt_of_le_of_ne h1 (Ne.symm h)
    rw [Pi.lt_def] at hlt
    obtain ⟨hle, i, hi⟩ := hlt
    have : (∑ j, y j) < ∑ j, a j :=
      Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ i, hi⟩
    linarith

theorem aux_vbwm_closed {n : ℕ} (v : Fin n → EReal) :
    IsClosed {y : Fin n → ℝ | v ≤ coeVec y} := by
  have : {y : Fin n → ℝ | v ≤ coeVec y} = ⋂ j, {y : Fin n → ℝ | v j ≤ ((y j : ℝ) : EReal)} := by
    ext y
    simp [Pi.le_def, coeVec]
  rw [this]
  refine isClosed_iInter fun j => ?_
  exact isClosed_le continuous_const (continuous_coe_real_ereal.comp (continuous_apply j))

end VeinottBaseStock

open VeinottBaseStock
open MeasureTheory ProbabilityTheory

theorem solution {n m : ℕ} (M : Model n m) (ybar : ℕ → Fin n → ℝ)
    (hM : M.Standing) (h3a : M.H3a ybar) (h3c : M.H3c) (h3d : M.H3d ybar)
    (hfeas : M.OrderFeasible) (k : ℕ) (x x' : Fin n → ℝ) (hx : x ∈ M.X k) (hx' : x' ∈ M.X k)
    (hle : x ≤ x') (hq : ¬ M.q k x ≤ coeVec (ybar k)) :
    M.w ybar k x ≤ M.w ybar k x' := by
  have key : ∀ z ∈ M.X k, ∃ a, IsLeast (M.orderSet ybar k z) a := by
    intro z hz
    refine aux_vbwm_least _ ?_ ?_ (ybar k) ?_ ?_
    · have : M.orderSet ybar k z = M.Y k ∩ ({y | M.q k z ≤ coeVec y} ∩ Set.Ici (ybar k)) := rfl
      rw [this]
      exact (h3c k).1.inter ((aux_vbwm_closed (M.q k z)).inter isClosed_Ici)
    · exact (h3c k).2.mono Set.inter_subset_left
    · intro y hy
      exact hy.2.2
    · obtain ⟨y, hyY, hqy⟩ := hfeas k z hz
      rcases (h3c k).2.total hyY (h3a k).1 with h | h
      · refine ⟨ybar k, (h3a k).1, hqy.trans ?_, le_rfl⟩
        intro j
        exact EReal.coe_le_coe_iff.mpr (h j)
      · exact ⟨y, hyY, hqy, h⟩
  have hw : ∀ z ∈ M.X k, IsLeast (M.orderSet ybar k z) (M.w ybar k z) := by
    intro z hz
    have h := key z hz
    unfold Model.w
    rw [dif_pos h]
    exact h.choose_spec
  have hsub : M.orderSet ybar k x' ⊆ M.orderSet ybar k x := by
    rintro y ⟨hY, hq', hb⟩
    exact ⟨hY, (h3d.2.2 k x hx x' hx' hle hq).trans hq', hb⟩
  exact (hw x hx).2 (hsub (hw x' hx').1)
