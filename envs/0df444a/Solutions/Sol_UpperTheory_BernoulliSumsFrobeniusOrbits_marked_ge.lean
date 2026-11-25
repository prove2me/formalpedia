-- Prove2me | solution 1 for UpperTheory.BernoulliSumsFrobeniusOrbits.marked_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:58:07.100353+00:00
-- url     : https://prove2.me/submissions/c6ce09cd-e5b0-43b7-b639-e7f6325cddbd

import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_MarkedLow
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_expectationSpec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ChoiceOfTops
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_MarkedGe
import Theorems.Thm_GlobalTheory_RandomTops_cell_card
import Theorems.Thm_GlobalTheory_RandomTops_cell_subset
import Theorems.Thm_GlobalTheory_RandomTops_ico_disjoint
import Theorems.Thm_GlobalTheory_RandomTops_prod_alternate
import Theorems.Thm_UpperTheory_BernoulliSumsFrobeniusOrbits_expectation_spec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0
private theorem ind_pos' {q : Prop} (h : q) : ind q = 1 := by simp [ind, h]
private theorem ind_neg' {q : Prop} (h : ¬ q) : ind q = 0 := by simp [ind, h]
private theorem ind_nonneg' (q : Prop) : 0 ≤ ind q := by
  unfold ind
  split_ifs <;> norm_num
private theorem ind_le_one' (q : Prop) : ind q ≤ 1 := by
  unfold ind
  split_ifs <;> norm_num
private theorem pow_le_prod {p : ℕ → ℝ} {δ : ℝ} (hp : ∀ a, p a ≤ δ) (h1 : δ ≤ 1) (C : Finset ℕ) :
    (1 - δ) ^ C.card ≤ ∏ a ∈ C, (1 - p a) := by
  rw [← Finset.prod_const]
  exact Finset.prod_le_prod (fun _ _ => by linarith) fun a _ => by linarith [hp a]
private theorem one_sub_pow_le_bernoulliExpectation_empty {p : ℕ → ℝ} {δ : ℝ} (hp : ∀ a, p a ≤ δ) (h1 : δ ≤ 1) (C : Finset ℕ) :
    (1 - δ) ^ C.card ≤ exP p C (fun V => ind (V = ∅)) := by
  have key : ∀ S : Finset ℕ, exP p S (fun V => ind (V = ∅)) = ∏ a ∈ S, (1 - p a) := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · simp [exP, ind]
    · intro a S ha ih
      rw [(expectation_spec p).2.2.2.2.1 a S _ ha, ih, Finset.prod_insert ha]
      have h0 : (exP p S fun T => ind (insert a T = ∅)) = 0 := by
        have := (expectation_spec p).1 S 0
        simpa [ind] using this
      rw [h0, mul_zero, add_zero]
  rw [key]
  exact pow_le_prod hp h1 C
private theorem le_bernoulliExpectation_singleton_even {p : ℕ → ℝ} {δ : ℝ} (hp : ∀ a, 3 / 4 * δ ≤ p a ∧ p a ≤ δ)
    (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (a u : ℕ) :
    ((u / 2 : ℕ) : ℝ) * (3 / 4 * δ) * (1 - δ) ^ (u - 1) ≤
      exP p (Finset.Ico a (a + u)) (fun V => ind (∃ x, V = {x} ∧ Even x)) := by
  classical
  have hp0 : ∀ b, 0 ≤ p b := fun b => le_trans (by positivity) (hp b).1
  have hd : 0 ≤ 1 - δ := by linarith
  have hc0 : 0 ≤ 3 / 4 * δ * (1 - δ) ^ (u - 1) := by positivity
  have hcard : u / 2 ≤ ((Finset.Ico a (a + u)).filter (fun x => Even x)).card := by
    have hle : (Finset.range (u / 2)).card ≤ ((Finset.Ico a (a + u)).filter (fun x => Even x)).card := by
      apply Finset.card_le_card_of_injOn (fun i => a + a % 2 + 2 * i)
      · intro i hi
        simp only [Finset.mem_coe, Finset.mem_range] at hi
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico]
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        rw [Nat.even_iff]
        omega
      · intro i _ j _ h
        simp only at h
        omega
    simpa using hle
  have hterm : ∀ x ∈ (Finset.Ico a (a + u)).filter (fun x => Even x),
      3 / 4 * δ * (1 - δ) ^ (u - 1) ≤
        ((∏ b ∈ ({x} : Finset ℕ), p b) * ∏ b ∈ Finset.Ico a (a + u) \ {x}, (1 - p b)) *
          ind (∃ y, ({x} : Finset ℕ) = {y} ∧ Even y) := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [ind_pos' ⟨x, rfl, hx.2⟩, mul_one, Finset.prod_singleton]
    have hc : (Finset.Ico a (a + u) \ {x}).card = u - 1 := by
      rw [Finset.card_sdiff, Finset.singleton_inter_of_mem hx.1]
      simp
    have h2 := pow_le_prod (fun b => (hp b).2) h1 (Finset.Ico a (a + u) \ {x})
    rw [hc] at h2
    exact mul_le_mul (hp x).1 h2 (by positivity) (hp0 x)
  calc ((u / 2 : ℕ) : ℝ) * (3 / 4 * δ) * (1 - δ) ^ (u - 1)
      ≤ (((Finset.Ico a (a + u)).filter (fun x => Even x)).card : ℝ) * (3 / 4 * δ * (1 - δ) ^ (u - 1)) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hc0
    _ = ∑ x ∈ (Finset.Ico a (a + u)).filter (fun x => Even x), 3 / 4 * δ * (1 - δ) ^ (u - 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ x ∈ (Finset.Ico a (a + u)).filter (fun x => Even x),
          ((∏ b ∈ ({x} : Finset ℕ), p b) * ∏ b ∈ Finset.Ico a (a + u) \ {x}, (1 - p b)) *
            ind (∃ y, ({x} : Finset ℕ) = {y} ∧ Even y) := Finset.sum_le_sum hterm
    _ = ∑ T ∈ ((Finset.Ico a (a + u)).filter (fun x => Even x)).map ⟨fun x => {x}, Finset.singleton_injective⟩,
          ((∏ b ∈ T, p b) * ∏ b ∈ Finset.Ico a (a + u) \ T, (1 - p b)) * ind (∃ y, T = {y} ∧ Even y) := by
        rw [Finset.sum_map]
        rfl
    _ ≤ exP p (Finset.Ico a (a + u)) (fun V => ind (∃ x, V = {x} ∧ Even x)) := by
        unfold exP
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro T hT
          rw [Finset.mem_map] at hT
          obtain ⟨x, hx, rfl⟩ := hT
          rw [Finset.mem_filter] at hx
          simpa using hx.1
        · intro T hT _
          have h3 : ∀ b ∈ Finset.Ico a (a + u) \ T, 0 ≤ 1 - p b := fun b _ => by linarith [(hp b).2]
          have := ind_nonneg' (∃ y, T = {y} ∧ Even y)
          have h4 : 0 ≤ ∏ b ∈ T, p b := Finset.prod_nonneg (fun b _ => hp0 b)
          have h5 := Finset.prod_nonneg h3
          positivity
end

set_option autoImplicit false
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0
namespace UpperTheory.BernoulliSumsFrobeniusOrbits
theorem _root_.solution :
    ∀ (p : ℕ → ℝ) (δ : ℝ) (r u s : ℕ), (∀ a, 3 / 4 * δ ≤ p a ∧ p a ≤ δ) → 0 ≤ δ → δ ≤ 1 →
      markedLow δ r u ≤ exP p (Finset.Ico (s * ((6 * r + 1) * u)) ((s + 1) * ((6 * r + 1) * u))) (fun T => ind (Marked T r u s)) := by
  classical
  intro p δ r u s hp h0 h1
  have hp0 : ∀ b, 0 ≤ p b := fun b => le_trans (by positivity) (hp b).1
  have hd : 0 ≤ 1 - δ := by linarith
  set A : ℕ → Finset ℕ := fun j => cell r u s (j + 1) with hA
  set g : ℕ → Finset ℕ → ℝ := fun j V =>
    if Even j then ind (V = ∅) else ind (∃ x, V = {x} ∧ Even x) with hg
  have hg0 : ∀ j V, 0 ≤ g j V := by
    intro j V
    simp only [hg]
    split_ifs <;> exact ind_nonneg' _
  have hg1 : ∀ j V, g j V ≤ 1 := by
    intro j V
    simp only [hg]
    split_ifs <;> exact ind_le_one' _
  have hdisj : ∀ i ∈ Finset.range (6 * r + 1), ∀ j ∈ Finset.range (6 * r + 1), i ≠ j →
      Disjoint (A i) (A j) := by
    intro i _ j _ hij
    simp only [hA, Formalism.G0.cell, Nat.add_sub_cancel]
    exact GlobalTheory.RandomTops.ico_disjoint hij
  have hsub : ∀ j ∈ Finset.range (6 * r + 1),
      A j ⊆ Finset.Ico (s * ((6 * r + 1) * u)) ((s + 1) * ((6 * r + 1) * u)) := by
    intro j hj
    rw [Finset.mem_range] at hj
    exact GlobalTheory.RandomTops.cell_subset (by omega)
  have hmono : (exP p (Finset.Ico (s * ((6 * r + 1) * u)) ((s + 1) * ((6 * r + 1) * u)))
      fun T => ∏ j ∈ Finset.range (6 * r + 1), g j (T ∩ A j)) ≤
      exP p (Finset.Ico (s * ((6 * r + 1) * u)) ((s + 1) * ((6 * r + 1) * u)))
        (fun T => ind (Marked T r u s)) := by
    apply (expectation_spec p).2.2.2.1
    · intro a _
      exact ⟨hp0 a, le_trans (hp a).2 h1⟩
    · intro T _
      by_cases hM : Marked T r u s
      · rw [ind_pos' hM]
        exact Finset.prod_le_one (fun j _ => hg0 j _) (fun j _ => hg1 j _)
      · rw [ind_neg' hM]
        unfold Formalism.G0.Marked at hM
        obtain ⟨c, hc⟩ := Classical.not_forall.1 hM
        obtain ⟨hc1, hc⟩ := _root_.not_imp.1 hc
        obtain ⟨hc2, hc⟩ := _root_.not_imp.1 hc
        obtain ⟨j, rfl⟩ : ∃ j, c = j + 1 := ⟨c - 1, by omega⟩
        apply le_of_eq
        apply Finset.prod_eq_zero (i := j) (Finset.mem_range.2 (by omega))
        by_cases hj : Even j
        · have hne : ¬ Even (j + 1) := Nat.not_even_iff_odd.2 hj.add_one
          simp only [hg, hA, if_pos hj]
          apply ind_neg'
          intro h
          exact hc ⟨fun _ => h, fun he => absurd he hne⟩
        · have hev : Even (j + 1) := by
            rcases Nat.even_or_odd j with h | h
            · exact absurd h hj
            · exact h.add_one
          have hno : ¬ Odd (j + 1) := Nat.not_odd_iff_even.2 hev
          simp only [hg, hA, if_neg hj]
          apply ind_neg'
          intro h
          exact hc ⟨fun ho => absurd ho hno, fun _ => h⟩
  refine le_trans ?_ hmono
  rw [(expectation_spec p).2.2.2.2.2.2 (Finset.range (6 * r + 1)) A g _ hdisj hsub]
  have hlow : ∀ j ∈ Finset.range (6 * r + 1),
      (if Even j then (1 - δ) ^ u else ((u / 2 : ℕ) : ℝ) * (3 / 4 * δ) * (1 - δ) ^ (u - 1)) ≤
        exP p (A j) (g j) := by
    intro j _
    by_cases hj : Even j
    · rw [if_pos hj]
      have hcard : (A j).card = u := GlobalTheory.RandomTops.cell_card (by omega)
      have := one_sub_pow_le_bernoulliExpectation_empty (fun b => (hp b).2) h1 (A j)
      rw [hcard] at this
      simpa only [hg, if_pos hj] using this
    · rw [if_neg hj]
      have hAj : A j = Finset.Ico (s * ((6 * r + 1) * u) + j * u) (s * ((6 * r + 1) * u) + j * u + u) := by
        simp only [hA, Formalism.G0.cell, Nat.add_sub_cancel]
        congr 1
        ring
      rw [hAj]
      simpa only [hg, if_neg hj] using le_bernoulliExpectation_singleton_even hp h0 h1 (s * ((6 * r + 1) * u) + j * u) u
  have hprod := Finset.prod_le_prod (fun j _ => by split_ifs <;> positivity) hlow
  have h6 : 6 * r + 1 = 2 * (3 * r) + 1 := by ring
  rw [h6, GlobalTheory.RandomTops.prod_alternate] at hprod
  rw [h6]
  unfold markedLow
  rw [← pow_mul, mul_comm u] at hprod ⊢
  exact hprod
end UpperTheory.BernoulliSumsFrobeniusOrbits
