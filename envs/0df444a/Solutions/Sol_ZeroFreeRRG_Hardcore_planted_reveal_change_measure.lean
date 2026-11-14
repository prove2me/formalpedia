-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.planted_reveal_change_measure
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:27:57.412551+00:00
-- url     : https://prove2.me/submissions/b9b9bbff-4bfc-452f-b2b2-1efc5e7b54f7

import Theorems.Thm_ZeroFreeRRG_Hardcore_revealed_pattern_change_measure
import Theorems.Thm_ZeroFreeRRG_Hardcore_planted_graph_conditional_gibbs
import Theorems.Thm_ZeroFreeRRG_Hardcore_planted_weights_sum_one
import Theorems.Thm_ZeroFreeRRG_Hardcore_planted_reveal_nonnegative
import Theorems.Thm_ZeroFreeRRG_Hardcore_normalized_partition_positive
import Theorems.Thm_ZeroFreeRRG_Hardcore_model_pi_positive_simplex
import Theorems.Thm_ZeroFreeRRG_Hardcore_model_edge_nonnegative
import Mathlib
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (hm : m.Valid) (t s : ℝ) (ht : m.PosParam t)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (d n : ℕ) [Nonempty (Matching n d)] (a₀ : m.Spin) (B R : ℝ)
    (H : ∀ U : Finset (Fin n), ({v : Fin n // v ∈ U} → m.Spin) →
      ({v : Fin n // v ∈ U} → m.Spin) → Prop)
    (hreference : (∑ U : Finset (Fin n), revealProb s U *
      ∑ y : ({v : Fin n // v ∈ U} → m.Spin), ∑ y' : ({v : Fin n // v ∈ U} → m.Spin),
        if H U y y' then
          (∏ v : {v : Fin n // v ∈ U}, m.pi t (y v)) *
          (∏ v : {v : Fin n // v ∈ U}, m.pi t (y' v)) else 0) ≤ R) :
    (∑ M : Matching n d, ∑ σ : Fin n → m.Spin, ∑ σ' : Fin n → m.Spin, ∑ U : Finset (Fin n),
      planted m t M σ * gibbs m t M σ' * revealProb s U *
        (if H U (fun v => σ v.1) (fun v => σ' v.1) ∧
            pinnedLL m t M σ U + pinnedLL m t M σ' U ≤ B then 1 else 0)) ≤ Real.exp B * R := by
  classical
  have hπ : ∀ a, 0 < m.pi t a := (model_pi_positive_simplex m hm t ht).1
  have hP := model_edge_nonnegative m hm t ht
  have hM : ∀ a b, 0 ≤ m.M t a b := fun a b =>
    div_nonneg (hP a b) (mul_nonneg (hπ a).le (hπ b).le)
  have hgibbs (M : Matching n d) (σ : Fin n → m.Spin) : 0 ≤ gibbs m t M σ := by
    unfold gibbs
    apply div_nonneg _ (normalized_partition_positive m hm t ht d n M).le
    unfold weight
    exact mul_nonneg (Finset.prod_nonneg fun v hv => (hπ (σ v)).le)
      (Finset.prod_nonneg fun x hx => hM (σ x.1) (σ (M.1 x).1))
  have hplant (M : Matching n d) (σ : Fin n → m.Spin) : 0 ≤ planted m t M σ := by
    have hh := planted_reveal_nonnegative m t 0 d n (fun a => (hπ a).le) hP (by norm_num) (by norm_num) M σ ∅
    simpa [revealProb] using hh
  let mass : Matching n d → ℝ := fun M => ∑ σ : Fin n → m.Spin, planted m t M σ
  have hmass (M : Matching n d) : 0 ≤ mass M := Finset.sum_nonneg fun σ hσ => hplant M σ
  have hmasssum : (∑ M, mass M) = 1 := planted_weights_sum_one m hm t ht d n
  have hreveal (U : Finset (Fin n)) : 0 ≤ revealProb s U := by
    unfold revealProb
    exact mul_nonneg (pow_nonneg hs _) (pow_nonneg (sub_nonneg.mpr hs1) _)
  let obs (U : Finset (Fin n)) (σ : Fin n → m.Spin) (v : {v : Fin n // v ∈ U}) := σ v.1
  let prior (U : Finset (Fin n)) (y : {v : Fin n // v ∈ U} → m.Spin) :=
    ∏ v : {v : Fin n // v ∈ U}, m.pi t (y v)
  let ref (U : Finset (Fin n)) := ∑ y, ∑ y', if H U y y' then prior U y * prior U y' else 0
  have hlocal (M : Matching n d) (U : Finset (Fin n)) :
      (∑ σ : Fin n → m.Spin, ∑ σ' : Fin n → m.Spin,
        if H U (obs U σ) (obs U σ') ∧ pinnedLL m t M σ U + pinnedLL m t M σ' U ≤ B then
          gibbs m t M σ * gibbs m t M σ' else 0) ≤ Real.exp B * ref U := by
    have hh := revealed_pattern_change_measure m t d n M U a₀ B (H U) hπ (hgibbs M)
    dsimp only at hh
    have hprior (y : {v : Fin n // v ∈ U} → m.Spin) :
        (∏ v ∈ U, m.pi t (if h : v ∈ U then y ⟨v,h⟩ else a₀)) = prior U y := by
      rw [← Finset.prod_coe_sort]
      apply Finset.prod_congr rfl
      intro v hv
      simp [prior,v.2]
    simpa only [obs,ref,hprior] using hh
  have hswap : (∑ M : Matching n d, ∑ σ : Fin n → m.Spin, ∑ σ' : Fin n → m.Spin, ∑ U : Finset (Fin n),
      planted m t M σ * gibbs m t M σ' * revealProb s U *
        (if H U (obs U σ) (obs U σ') ∧ pinnedLL m t M σ U + pinnedLL m t M σ' U ≤ B then 1 else 0)) =
    ∑ M : Matching n d, mass M * (∑ U : Finset (Fin n), revealProb s U *
      (∑ σ : Fin n → m.Spin, ∑ σ' : Fin n → m.Spin,
        if H U (obs U σ) (obs U σ') ∧ pinnedLL m t M σ U + pinnedLL m t M σ' U ≤ B then
          gibbs m t M σ * gibbs m t M σ' else 0)) := by
    apply Finset.sum_congr rfl
    intro M hM'
    calc
      _ = ∑ σ : Fin n → m.Spin, ∑ U : Finset (Fin n), ∑ σ' : Fin n → m.Spin,
          planted m t M σ * gibbs m t M σ' * revealProb s U *
            (if H U (obs U σ) (obs U σ') ∧ pinnedLL m t M σ U + pinnedLL m t M σ' U ≤ B then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro σ hσ
        rw [Finset.sum_comm]
      _ = ∑ U : Finset (Fin n), ∑ σ : Fin n → m.Spin, ∑ σ' : Fin n → m.Spin,
          planted m t M σ * gibbs m t M σ' * revealProb s U *
            (if H U (obs U σ) (obs U σ') ∧ pinnedLL m t M σ U + pinnedLL m t M σ' U ≤ B then 1 else 0) := by
        rw [Finset.sum_comm]
      _ = mass M * (∑ U : Finset (Fin n), revealProb s U *
          (∑ σ : Fin n → m.Spin, ∑ σ' : Fin n → m.Spin,
            if H U (obs U σ) (obs U σ') ∧ pinnedLL m t M σ U + pinnedLL m t M σ' U ≤ B then
              gibbs m t M σ * gibbs m t M σ' else 0)) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro U hU
        apply Finset.sum_congr rfl
        intro σ hσ
        apply Finset.sum_congr rfl
        intro σ' hσ'
        rw [planted_graph_conditional_gibbs m hm t ht d n M σ]
        split_ifs <;> ring
  change (∑ M : Matching n d, ∑ σ : Fin n → m.Spin, ∑ σ' : Fin n → m.Spin, ∑ U : Finset (Fin n),
      planted m t M σ * gibbs m t M σ' * revealProb s U *
        (if H U (obs U σ) (obs U σ') ∧ pinnedLL m t M σ U + pinnedLL m t M σ' U ≤ B then 1 else 0)) ≤ _
  rw [hswap]
  calc
    _ ≤ ∑ M : Matching n d, mass M * (∑ U : Finset (Fin n), revealProb s U * (Real.exp B * ref U)) := by
      apply Finset.sum_le_sum
      intro M hM'
      apply mul_le_mul_of_nonneg_left _ (hmass M)
      apply Finset.sum_le_sum
      intro U hU
      exact mul_le_mul_of_nonneg_left (hlocal M U) (hreveal U)
    _ = Real.exp B * (∑ U : Finset (Fin n), revealProb s U * ref U) := by
      rw [← Finset.sum_mul,hmasssum,one_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro U hU
      ring
    _ ≤ Real.exp B * R := mul_le_mul_of_nonneg_left hreference (Real.exp_pos B).le
