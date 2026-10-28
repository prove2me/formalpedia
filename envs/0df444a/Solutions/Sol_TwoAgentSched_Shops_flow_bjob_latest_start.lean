-- Prove2me | solution 1 for TwoAgentSched.Shops.flow_bjob_latest_start
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T05:58:17.332752+00:00
-- url     : https://prove2.me/submissions/594aa226-4f63-43db-8b56-152649e8b3e3

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Card
import Mathlib.Data.List.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_TwoAgentSched_Shops_Construction

open TwoAgentSched.Shops

private lemma nonoverlap_sum_le {α : Type*} [DecidableEq α] (a L : α → ℝ)
    (hL : ∀ i, 0 ≤ L i)
    (hdisj : ∀ i j, i ≠ j → a i + L i ≤ a j ∨ a j + L j ≤ a i) :
    ∀ (n : ℕ) (T : Finset α), T.card = n → ∀ (lo hi : ℝ), lo ≤ hi →
      (∀ i ∈ T, lo ≤ a i ∧ a i + L i ≤ hi) → ∑ i ∈ T, L i ≤ hi - lo := by
  intro n
  induction n with
  | zero =>
    intro T hcard lo hi hle _
    rw [Finset.card_eq_zero.mp hcard, Finset.sum_empty]
    linarith
  | succ n ih =>
    intro T hcard lo hi hle hT
    by_cases hzero : ∃ i₀ ∈ T, L i₀ = 0
    · obtain ⟨i₀, hi₀, hLi₀⟩ := hzero
      rw [← Finset.add_sum_erase _ _ hi₀, hLi₀, zero_add]
      exact ih (T.erase i₀) (by rw [Finset.card_erase_of_mem hi₀, hcard]; rfl) lo hi hle
        (fun i hi => hT i (Finset.mem_of_mem_erase hi))
    · push_neg at hzero
      have hpos : ∀ i ∈ T, 0 < L i := fun i hi => lt_of_le_of_ne (hL i) (Ne.symm (hzero i hi))
      have hne : T.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image T a hne
      rw [← Finset.add_sum_erase _ _ hi₀]
      have hi₀_bounds := hT i₀ hi₀
      have hsub : ∑ i ∈ T.erase i₀, L i ≤ hi - (a i₀ + L i₀) := by
        refine ih (T.erase i₀) (by rw [Finset.card_erase_of_mem hi₀, hcard]; rfl)
          (a i₀ + L i₀) hi hi₀_bounds.2 (fun j hj => ?_)
        have hjT : j ∈ T := Finset.mem_of_mem_erase hj
        have hne_ji : i₀ ≠ j := (Finset.ne_of_mem_erase hj).symm
        have haj : a i₀ ≤ a j := hmin j hjT
        have hLj : 0 < L j := hpos j hjT
        rcases hdisj i₀ j hne_ji with h1 | h2
        · exact ⟨h1, (hT j hjT).2⟩
        · linarith
      linarith

theorem solution (p : List ℕ)
    (s₁ s₂ : Fin ((flowInst p).nA + (flowInst p).nB) → ℝ)
    (hfeas : JohnsonFlowShop.TwoStage.IsFeasible (flowInst p).p1 (flowInst p).p2 s₁ s₂)
    (hB : (flowInst p).MeetsB s₁ s₂ (flowQB p)) :
    s₂ (flowB p) ≤ partSum p / 2 + eps p ∧
      ∑ i ∈ Finset.univ.filter (fun i : Fin p.length => s₂ (flowA p i) < s₂ (flowB p)),
        (p.get i : ℝ) ≤ partSum p / 2 := by
  have hb : finSumFinEquiv.symm (flowB p) = Sum.inr ⟨0, Nat.one_pos⟩ :=
    finSumFinEquiv_symm_apply_natAdd ⟨0, Nat.one_pos⟩
  have hpB2 : (flowInst p).p2 (flowB p) = partSum p / 2 := by
    unfold Instance.p2
    rw [hb]
    rfl
  have hB_end : s₂ (flowB p) + partSum p / 2 ≤ partSum p + eps p := by
    exact (hB ⟨0, Nat.one_pos⟩).2
  have hs2B : s₂ (flowB p) ≤ partSum p / 2 + eps p := by linarith
  refine ⟨hs2B, ?_⟩
  have ha : ∀ i : Fin p.length, finSumFinEquiv.symm (flowA p i) = Sum.inl i :=
    fun i => finSumFinEquiv_symm_apply_castAdd i
  have hpA1 : ∀ i : Fin p.length, (flowInst p).p1 (flowA p i) = eps p := by
    intro i
    unfold Instance.p1
    rw [ha i]
    rfl
  have hpA2 : ∀ i : Fin p.length, (flowInst p).p2 (flowA p i) = (p.get i : ℝ) := by
    intro i
    unfold Instance.p2
    rw [ha i]
    rfl
  have ha_inj : Function.Injective (flowA p) := by
    intro i j hij
    have := congrArg finSumFinEquiv.symm hij
    rw [ha i, ha j] at this
    exact Sum.inl_injective this
  have ha_ne_B : ∀ i : Fin p.length, flowA p i ≠ flowB p := by
    intro i h
    have := congrArg finSumFinEquiv.symm h
    rw [ha i, hb] at this
    nomatch this
  set S := Finset.univ.filter (fun i : Fin p.length => s₂ (flowA p i) < s₂ (flowB p))
  have hpart_nonneg : 0 ≤ partSum p / 2 := by
    unfold partSum; positivity
  have hsum := nonoverlap_sum_le (fun i : Fin p.length => s₂ (flowA p i))
    (fun i : Fin p.length => (p.get i : ℝ)) (fun i => by positivity)
    (fun i j hij => by
      have := hfeas.2.2.1 (flowA p i) (flowA p j) (fun e => hij (ha_inj e))
      rwa [hpA2 i, hpA2 j] at this)
    S.card S rfl (eps p) (partSum p / 2 + eps p) (by linarith)
    (fun i hi => by
      have hilt : s₂ (flowA p i) < s₂ (flowB p) := (Finset.mem_filter.mp hi).2
      have h1 : 0 ≤ s₁ (flowA p i) := hfeas.1 (flowA p i)
      have h12 : s₁ (flowA p i) + eps p ≤ s₂ (flowA p i) := by
        have := hfeas.2.2.2 (flowA p i)
        rwa [hpA1 i] at this
      have hdisjB := hfeas.2.2.1 (flowA p i) (flowB p) (ha_ne_B i)
      rw [hpA2 i, hpB2] at hdisjB
      rcases hdisjB with hle | hge
      · exact ⟨by linarith, by linarith⟩
      · linarith)
  linarith
