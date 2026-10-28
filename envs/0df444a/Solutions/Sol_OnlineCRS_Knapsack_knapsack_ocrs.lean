-- Prove2me | solution 1 for OnlineCRS.Knapsack.knapsack_ocrs
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-25T09:04:11.764993+00:00
-- url     : https://prove2.me/submissions/7af3938e-141e-4b94-8329-078861e053dc

import Mathlib
import Definitions.Def_OnlineCRS_Matroid_Basics
import Definitions.Def_OnlineCRS_Knapsack_Model


section
open Finset OnlineCRS.Knapsack
open scoped Pointwise BigOperators
namespace KnapsackProof
variable {α : Type} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
lemma scaled_bounds {s x : α → ℝ} {b : ℝ} (hb0 : 0 ≤ b) (hb : b ≤ 1/2)
    (hx : x ∈ b • knapsackPolytope s) :
    (∀ e, 0 ≤ x e ∧ x e ≤ 1) ∧ (∑ e, s e * x e) ≤ b := by
  obtain ⟨z, hz, rfl⟩ := Set.mem_smul_set.mp hx
  change (∀ e, 0 ≤ b * z e ∧ b * z e ≤ 1) ∧ (∑ e, s e * (b*z e)) ≤ b
  rcases hz with ⟨hz, hload⟩
  constructor
  · intro e
    constructor
    · exact mul_nonneg hb0 (hz e).1
    · have := mul_le_mul_of_nonneg_left (hz e).2 hb0
      nlinarith
  · calc
      (∑ e, s e * (b*z e)) = b * ∑ e, s e * z e := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
      _ ≤ b * 1 := mul_le_mul_of_nonneg_left hload hb0
      _ = b := mul_one b

lemma big_load_bounds {s x : α → ℝ} {b : ℝ} (hs : ∀ e, 0 ≤ s e)
    (hx : ∀ e, 0 ≤ x e) (hload : ∑ e, s e * x e ≤ b) :
    0 ≤ bigLoad s x ∧ bigLoad s x ≤ b := by
  constructor
  · exact Finset.sum_nonneg (fun e _ => mul_nonneg (hs e) (hx e))
  · exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun e _ _ => mul_nonneg (hs e) (hx e))) hload

lemma small_load_bound {s x : α → ℝ} {b : ℝ} (hload : ∑ e, s e * x e ≤ b) :
    (∑ e ∈ (bigElements s)ᶜ, s e * x e) ≤ b - bigLoad s x := by
  have h := Finset.sum_add_sum_compl (bigElements s) (fun e => s e * x e)
  unfold bigLoad
  linarith

lemma mix_bounds {s : α → ℝ} {b : ℝ} (hs : ∀ e, 0 ≤ s e)
    (hb0 : 0 ≤ b) (hb : b ≤ 1/2) (x : α → ℝ) :
    0 ≤ mixProbability s b x ∧ mixProbability s b x ≤ 1 := by
  classical
  unfold mixProbability
  split_ifs with h
  · obtain ⟨hx, hl⟩ := scaled_bounds hb0 hb h
    obtain ⟨hB0, hBb⟩ := big_load_bounds hs (fun e => (hx e).1) hl
    have hd : 0 < 2-2*b := by linarith
    unfold bigProbability
    constructor
    · exact div_nonneg (by linarith) hd.le
    · apply (div_le_one hd).mpr
      linarith
  · norm_num

lemma scalar_mix_bound {b B : ℝ} (hb : b ≤ 1/2)
    (hB0 : 0 ≤ B) (hBb : B ≤ b) :
    (1-2*b)/(2-2*b) ≤ ((1-2*b+2*B)/(2-2*b))*(1-2*B) := by
  have hd : 0 < 2-2*b := by linarith
  rw [div_mul_eq_mul_div]
  apply (div_le_div_iff_of_pos_right hd).mpr
  have : 0 ≤ B*(b-B) := mul_nonneg hB0 (sub_nonneg.mpr hBb)
  nlinarith

end KnapsackProof
end

section
open Finset OnlineCRS.Matroid OnlineCRS.Knapsack
namespace KnapsackProof
variable {α : Type} [Fintype α] [DecidableEq α]

theorem mem_big (s : α → ℝ) (e : α) : e ∈ bigElements s ↔ 1 / 2 < s e := by
  classical
  simp [bigElements]

theorem mem_big_family (s : α → ℝ) (I : Finset α) :
    I ∈ bigFamily s ↔ I ⊆ bigElements s ∧ knapsackFeasible s I := by
  classical
  simp [bigFamily]

theorem mem_small_family (s : α → ℝ) (I : Finset α) :
    I ∈ smallFamily s ↔ (∀ e ∈ I, e ∉ bigElements s) ∧ knapsackFeasible s I := by
  classical
  simp [smallFamily]

omit [Fintype α] in
theorem feasible_mono (s : α → ℝ) (hs : ∀ e, 0 ≤ s e)
    {I J : Finset α} (hJI : J ⊆ I) (hI : knapsackFeasible s I) :
    knapsackFeasible s J := by
  exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hJI (fun f _ _ => hs f)) hI

theorem big_greedy (s : α → ℝ) (hs : ∀ e, 0 ≤ s e) :
    IsGreedyFamily (knapsackFeasible s) (bigFamily s) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · simp [mem_big_family, knapsackFeasible]
  · intro I hI J hJI
    obtain ⟨hsub, hfeas⟩ := (mem_big_family s I).mp hI
    exact (mem_big_family s J).mpr ⟨hJI.trans hsub, feasible_mono s hs hJI hfeas⟩
  · intro I hI
    exact ((mem_big_family s I).mp hI).2

theorem small_greedy (s : α → ℝ) (hs : ∀ e, 0 ≤ s e) :
    IsGreedyFamily (knapsackFeasible s) (smallFamily s) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · simp [mem_small_family, knapsackFeasible]
  · intro I hI J hJI
    obtain ⟨hsub, hfeas⟩ := (mem_small_family s I).mp hI
    exact (mem_small_family s J).mpr
      ⟨fun e he => hsub e (hJI he), feasible_mono s hs hJI hfeas⟩
  · intro I hI
    exact ((mem_small_family s I).mp hI).2

theorem big_selectable (s : α → ℝ) (hs1 : ∀ e, s e ≤ 1)
    (A : Finset α) (e : α) (he : e ∈ bigElements s)
    (hA : ∀ f ∈ A, f ∈ bigElements s → f = e) :
    Selectable (bigFamily s) A e := by
  classical
  intro I hIA hI
  obtain ⟨hIB, _⟩ := (mem_big_family s I).mp hI
  have hsub : I ⊆ {e} := by
    intro f hf
    simpa using hA f (hIA hf) (hIB hf)
  have hins : insert e I = {e} := by
    ext f
    simp only [mem_insert, mem_singleton]
    exact ⟨fun h => h.elim id (fun hf => mem_singleton.mp (hsub hf)), fun h => Or.inl h⟩
  rw [hins, mem_big_family]
  exact ⟨by simpa using he, by simpa [knapsackFeasible] using hs1 e⟩

theorem small_selectable (s : α → ℝ) (hs : ∀ e, 0 ≤ s e)
    (A : Finset α) (e : α) (he : e ∉ bigElements s)
    (hload : ∑ f ∈ A.filter (fun f => f ∉ bigElements s ∧ f ≠ e), s f ≤ 1 / 2) :
    Selectable (smallFamily s) A e := by
  classical
  intro I hIA hI
  obtain ⟨hIS, _⟩ := (mem_small_family s I).mp hI
  refine (mem_small_family s (insert e I)).mpr ⟨?_, ?_⟩
  · intro f hf
    rcases mem_insert.mp hf with rfl | hf
    · exact he
    · exact hIS f hf
  · have herase : I.erase e ⊆ A.filter (fun f => f ∉ bigElements s ∧ f ≠ e) := by
      intro f hf
      obtain ⟨hne, hfI⟩ := mem_erase.mp hf
      exact mem_filter.mpr ⟨hIA hfI, hIS f hfI, hne⟩
    have hsum : ∑ f ∈ I.erase e, s f ≤ 1 / 2 :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg herase (fun f _ _ => hs f)) hload
    have hehalf : s e ≤ 1 / 2 := le_of_not_gt (fun h => he ((mem_big s e).mpr h))
    have hsets : insert e I = insert e (I.erase e) := by
      ext f
      simp only [mem_insert, mem_erase]
      tauto
    unfold knapsackFeasible
    rw [hsets, sum_insert (by simp)]
    linarith
end KnapsackProof
end

section
open Finset OnlineCRS.Matroid
namespace KnapsackProof
open scoped BigOperators
variable {α : Type} [Fintype α] [DecidableEq α]

lemma active_eq (x : α → ℝ) (A : Finset α) :
    activeProb x A = (∏ i ∈ A, x i) * ∏ i ∈ Aᶜ, (1-x i) := by
  classical
  have hc : Finset.univ.filter (fun i => i ∉ A) = Aᶜ := by ext i; simp
  simp only [activeProb, Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.univ_inter, hc]

lemma active_sum (x : α → ℝ) : ∑ A : Finset α, activeProb x A = 1 := by
  classical
  simp_rw [active_eq]
  rw [← Fintype.prod_add]
  simp

lemma active_nonneg {x : α → ℝ} (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (A : Finset α) :
    0 ≤ activeProb x A := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs
  · exact (hx i).1
  · exact sub_nonneg.mpr (hx i).2

lemma active_marginal_point (x : α → ℝ) (e : α) (A : Finset α) :
    activeProb x A * (if e ∈ A then 1 else 0) =
      x e * activeProb (Function.update x e 1) A := by
  classical
  rw [activeProb, activeProb]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ e)]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ e)]
  have h : (∏ i ∈ Finset.univ.erase e, if i ∈ A then Function.update x e 1 i
      else 1 - Function.update x e 1 i) =
      ∏ i ∈ Finset.univ.erase e, if i ∈ A then x i else 1 - x i := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
  rw [h]
  by_cases he : e ∈ A <;> simp [he]

lemma active_marginal (x : α → ℝ) (e : α) :
    (∑ A : Finset α, activeProb x A * (if e ∈ A then 1 else 0)) = x e := by
  classical
  simp_rw [active_marginal_point]
  rw [← Finset.mul_sum, active_sum, mul_one]

lemma active_load (x s : α → ℝ) (T : Finset α) :
    (∑ A : Finset α, activeProb x A * ∑ i ∈ T, if i ∈ A then s i else 0) =
      ∑ i ∈ T, s i * x i := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have h (A : Finset α) : activeProb x A * (if i ∈ A then s i else 0) =
      s i * (activeProb x A * (if i ∈ A then 1 else 0)) := by
    split_ifs <;> ring
  simp_rw [h]
  rw [← Finset.mul_sum, active_marginal]

lemma sel_nonneg {x : α → ℝ} (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (Fam : Finset (Finset α)) (e : α) : 0 ≤ selProb x Fam e := by
  unfold selProb
  apply Finset.sum_nonneg
  intro A _
  split_ifs
  · exact active_nonneg hx A
  · exact le_rfl

end KnapsackProof
end

section
open Finset OnlineCRS.Knapsack OnlineCRS.Matroid
namespace KnapsackProof
variable {α : Type} [Fintype α] [DecidableEq α]

lemma mixture_sum (s : α → ℝ) (b : ℝ) (x : α → ℝ)
    (f : Finset (Finset α) → ℝ) :
    (∑ Fam : Finset (Finset α), knapsackWeights s b x Fam * f Fam) =
      mixProbability s b x * f (bigFamily s) +
        (1-mixProbability s b x)*f (smallFamily s) := by
  classical
  unfold knapsackWeights
  simp_rw [add_mul, ite_mul, zero_mul]
  rw [Finset.sum_add_distrib]
  simp

lemma mixture_greedy {s : α → ℝ} {b : ℝ} (hs : ∀ e, 0 ≤ s e)
    (hb0 : 0 ≤ b) (hb : b ≤ 1/2) :
    IsRandGreedyOCRS (knapsackFeasible s) (knapsackWeights s b) := by
  classical
  intro x
  obtain ⟨hp0, hp1⟩ := mix_bounds hs hb0 hb x
  refine ⟨?_, ?_, ?_⟩
  · intro Fam
    unfold knapsackWeights
    exact add_nonneg (ite_nonneg hp0 (le_refl 0))
      (ite_nonneg (sub_nonneg.mpr hp1) (le_refl 0))
  · have h := mixture_sum s b x (fun _ => 1)
    simpa using h
  · intro Fam h
    by_cases hB : Fam = bigFamily s
    · subst Fam; exact big_greedy s hs
    · by_cases hS : Fam = smallFamily s
      · subst Fam; exact small_greedy s hs
      · simp [knapsackWeights, hB, hS] at h

end KnapsackProof
end

section
open Finset OnlineCRS.Matroid OnlineCRS.Knapsack
namespace KnapsackProof
variable {α : Type} [Fintype α] [DecidableEq α]

open Classical in
lemma deficit_bound (x : α → ℝ) (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1)
    (Fam : Finset (Finset α)) (e : α) (T : Finset α) (s : α → ℝ) (r : ℝ)
    (hpoint : ∀ A : Finset α,
      1-r*(∑ f ∈ T, if f ∈ A then s f else 0) ≤
        if Selectable Fam A e then 1 else 0) :
    1-r*(∑ f ∈ T, s f*x f) ≤ selProb x Fam e := by
  classical
  calc
    1-r*(∑ f ∈ T, s f*x f) =
        (∑ A : Finset α, activeProb x A) -
          r*(∑ A : Finset α, activeProb x A*(∑ f ∈ T, if f ∈ A then s f else 0)) := by
      rw [active_sum, active_load]
    _ = ∑ A : Finset α, activeProb x A *
        (1-r*(∑ f ∈ T, if f ∈ A then s f else 0)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro A _
      ring
    _ ≤ ∑ A : Finset α, activeProb x A*(if Selectable Fam A e then 1 else 0) :=
      Finset.sum_le_sum (fun A _ => mul_le_mul_of_nonneg_left (hpoint A) (active_nonneg hx A))
    _ = selProb x Fam e := by
      unfold selProb
      apply Finset.sum_congr rfl
      intro A _
      split_ifs <;> simp

lemma big_selection_bound (s x : α → ℝ) (hs : ∀ e, 0 ≤ s e ∧ s e ≤ 1)
    (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1) (e : α) (he : e ∈ bigElements s) :
    1-2*bigLoad s x ≤ selProb x (bigFamily s) e := by
  classical
  have hpoint (A : Finset α) :
      1-1*(∑ f ∈ bigElements s, if f ∈ A then (1:ℝ) else 0) ≤
        if Selectable (bigFamily s) A e then 1 else 0 := by
    have hnon : 0 ≤ ∑ f ∈ bigElements s, if f ∈ A then (1:ℝ) else 0 := by positivity
    by_cases h : ∃ f ∈ bigElements s, f ∈ A
    · obtain ⟨f, hfB, hfA⟩ := h
      have hone : (1:ℝ) ≤ ∑ f ∈ bigElements s, if f ∈ A then (1:ℝ) else 0 := by
        simpa [hfA] using (Finset.single_le_sum (f := fun f => if f ∈ A then (1:ℝ) else 0)
          (fun _ _ => by positivity) hfB)
      split_ifs <;> linarith
    · have hsel := big_selectable s (fun f => (hs f).2) A e he
        (fun f hfA hfB => False.elim (h ⟨f, hfB, hfA⟩))
      rw [if_pos hsel]
      linarith
  have hbound := deficit_bound x hx (bigFamily s) e (bigElements s) (fun _ => 1) 1 hpoint
  have hmass : (∑ f ∈ bigElements s, x f) ≤ 2*bigLoad s x := by
    unfold bigLoad
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro f hf
    have := (mem_big s f).mp hf
    have := mul_nonneg (by linarith : 0 ≤ 2*s f-1) (hx f).1
    nlinarith
  simp only [one_mul] at hbound
  linarith

lemma small_selection_bound (s x : α → ℝ) (hs : ∀ e, 0 ≤ s e ∧ s e ≤ 1)
    (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1) (b : ℝ)
    (hl : ∑ f, s f*x f ≤ b) (e : α) (he : e ∉ bigElements s) :
    1-2*b+2*bigLoad s x ≤ selProb x (smallFamily s) e := by
  classical
  have hpoint (A : Finset α) :
      1-2*(∑ f ∈ (bigElements s)ᶜ, if f ∈ A then s f else 0) ≤
        if Selectable (smallFamily s) A e then 1 else 0 := by
    let L := ∑ f ∈ (bigElements s)ᶜ, if f ∈ A then s f else 0
    have hnon : 0 ≤ L := by
      apply Finset.sum_nonneg
      intro f _
      split_ifs <;> [exact (hs f).1; exact le_rfl]
    by_cases hL : L ≤ 1/2
    · have hfull : (∑ f ∈ A.filter (fun f => f ∉ bigElements s), s f) = L := by
        dsimp [L]
        rw [← Finset.sum_filter]
        congr 1
        ext f
        simp [and_comm]
      have hsub : A.filter (fun f => f ∉ bigElements s ∧ f ≠ e) ⊆
          A.filter (fun f => f ∉ bigElements s) := by
        intro f hf
        simp only [mem_filter] at hf ⊢
        exact ⟨hf.1, hf.2.1⟩
      have hload : ∑ f ∈ A.filter (fun f => f ∉ bigElements s ∧ f ≠ e), s f ≤ 1/2 := by
        calc
          _ ≤ ∑ f ∈ A.filter (fun f => f ∉ bigElements s), s f :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun f _ _ => (hs f).1)
          _ = L := hfull
          _ ≤ 1/2 := hL
      rw [if_pos (small_selectable s (fun f => (hs f).1) A e he hload)]
      change 1-2*L ≤ 1
      linarith
    · change 1-2*L ≤ if Selectable (smallFamily s) A e then 1 else 0
      split_ifs <;> linarith
  have hbound := deficit_bound x hx (smallFamily s) e (bigElements s)ᶜ s 2 hpoint
  have hmass := small_load_bound (s := s) (x := x) hl
  linarith
end KnapsackProof
end

section
open Finset OnlineCRS.Matroid OnlineCRS.Knapsack
open scoped Pointwise
namespace KnapsackProof
variable {α : Type} [Fintype α] [DecidableEq α]

theorem constructed_selectable (s : α → ℝ) (hs : ∀ e, 0 ≤ s e ∧ s e ≤ 1)
    (b : ℝ) (hb0 : 0 ≤ b) (hb : b ≤ 1/2) :
    IsSelectableRand (knapsackFeasible s) (knapsackPolytope s)
      b ((1-2*b)/(2-2*b)) (knapsackWeights s b) := by
  classical
  refine ⟨mixture_greedy (fun e => (hs e).1) hb0 hb, ?_⟩
  intro x hx e
  obtain ⟨hbox, hload⟩ := scaled_bounds hb0 hb hx
  obtain ⟨hB0, hBb⟩ := big_load_bounds (fun e => (hs e).1) (fun e => (hbox e).1) hload
  obtain ⟨hp0, hp1⟩ := mix_bounds (fun e => (hs e).1) hb0 hb x
  rw [mixture_sum]
  have heq : mixProbability s b x = (1-2*b+2*bigLoad s x)/(2-2*b) := by
    simp [mixProbability, hx, bigProbability]
  have hd : 0 < 2-2*b := by linarith
  have hq : 1-mixProbability s b x = (1-2*bigLoad s x)/(2-2*b) := by
    rw [heq]
    apply (eq_div_iff hd.ne').mpr
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hd.ne']
    ring
  by_cases he : e ∈ bigElements s
  · have hsel := big_selection_bound s x hs hbox e he
    have hsmall := sel_nonneg hbox (smallFamily s) e
    calc
      (1-2*b)/(2-2*b) ≤ mixProbability s b x*(1-2*bigLoad s x) := by
        rw [heq]; exact scalar_mix_bound hb hB0 hBb
      _ ≤ mixProbability s b x*selProb x (bigFamily s) e := mul_le_mul_of_nonneg_left hsel hp0
      _ ≤ _ := le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hp1) hsmall)
  · have hsel := small_selection_bound s x hs hbox b hload e he
    have hbig := sel_nonneg hbox (bigFamily s) e
    calc
      (1-2*b)/(2-2*b) ≤ (1-mixProbability s b x)*(1-2*b+2*bigLoad s x) := by
        rw [hq]
        have h := scalar_mix_bound hb hB0 hBb
        convert h using 1; ring
      _ ≤ (1-mixProbability s b x)*selProb x (smallFamily s) e :=
        mul_le_mul_of_nonneg_left hsel (sub_nonneg.mpr hp1)
      _ ≤ _ := le_add_of_nonneg_left (mul_nonneg hp0 hbig)

end KnapsackProof

namespace OnlineCRS.Knapsack
theorem proved_root {α : Type} [Fintype α] [DecidableEq α]
    (s : α → ℝ) (hs : ∀ e, 0 ≤ s e ∧ s e ≤ 1)
    (b : ℝ) (hb0 : 0 ≤ b) (hb : b ≤ 1 / 2) :
    ∃ w : (α → ℝ) → Finset (Finset α) → ℝ,
      OnlineCRS.Matroid.IsSelectableRand (knapsackFeasible s) (knapsackPolytope s)
        b ((1 - 2 * b) / (2 - 2 * b)) w := by
  exact ⟨knapsackWeights s b, KnapsackProof.constructed_selectable s hs b hb0 hb⟩
end OnlineCRS.Knapsack
end

open OnlineCRS.Knapsack

theorem solution {α : Type} [Fintype α] [DecidableEq α]
    (s : α → ℝ) (hs : ∀ e, 0 ≤ s e ∧ s e ≤ 1)
    (b : ℝ) (hb0 : 0 ≤ b) (hb : b ≤ 1 / 2) :
    ∃ w : (α → ℝ) → Finset (Finset α) → ℝ,
      OnlineCRS.Matroid.IsSelectableRand (knapsackFeasible s) (knapsackPolytope s)
        b ((1 - 2 * b) / (2 - 2 * b)) w := by
  exact OnlineCRS.Knapsack.proved_root s hs b hb0 hb

theorem OnlineCRS.Knapsack.knapsack_ocrs {α : Type} [Fintype α] [DecidableEq α]
    (s : α → ℝ) (hs : ∀ e, 0 ≤ s e ∧ s e ≤ 1)
    (b : ℝ) (hb0 : 0 ≤ b) (hb : b ≤ 1 / 2) :
    ∃ w : (α → ℝ) → Finset (Finset α) → ℝ,
      OnlineCRS.Matroid.IsSelectableRand (knapsackFeasible s) (knapsackPolytope s)
        b ((1 - 2 * b) / (2 - 2 * b)) w := by
  exact _root_.solution s hs b hb0 hb
