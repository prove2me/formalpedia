-- Prove2me | solution 1 for OnlinePrimalDual.GroupSteiner.lemma11_1_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T09:32:07.471201+00:00
-- url     : https://prove2.me/submissions/f002f1f6-d4ec-4129-9447-a02714057080

import Mathlib
import Definitions.Def_OnlinePrimalDual_GroupSteiner_RandomCover
import Definitions.Def_OnlinePrimalDual_GroupSteiner_marg
import Definitions.Def_OnlinePrimalDual_GroupSteiner_RoundedTree
import Definitions.Def_OnlinePrimalDual_GroupSteiner_roundRun_v2

namespace ZG88
open OnlinePrimalDual.GroupSteiner

variable {E : Type*} [Fintype E] [DecidableEq E]

def ind (e : E) (C : Finset E) : ℝ := if e ∈ C then 1 else 0

noncomputable def mg (q : Finset E → ℝ) (e : E) : ℝ := ∑ C, q C * ind e C

def Inv (tr : RoundedTree E) (cw : E → ℝ) (q : Finset E → ℝ) : Prop :=
  (∀ C, 0 ≤ q C) ∧ (∑ C, q C = 1) ∧ (∀ f, mg q f = min (cw f) 1) ∧
  (∀ C, q C ≠ 0 → ∀ f p, tr.parent f = some p → f ∈ C → p ∈ C)

lemma edgeStep_expect (tr : RoundedTree E) (w w' δ : E → ℝ) (e : E) (q : Finset E → ℝ)
    (φ : Finset E → ℝ) :
    ∑ C', edgeStep tr w w' δ e q C' * φ C' =
      ∑ C, q C * (coinProbClamped tr w w' δ e C * φ (insert e C) +
        (1 - coinProbClamped tr w w' δ e C) * φ C) := by
  unfold edgeStep
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro C _
  simp only [mul_add, add_mul, Finset.sum_add_distrib, mul_ite, ite_mul, mul_one, mul_zero,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

lemma mg_step_ne (tr : RoundedTree E) (w w' δ : E → ℝ) (e f : E) (q : Finset E → ℝ)
    (hf : f ≠ e) : mg (edgeStep tr w w' δ e q) f = mg q f := by
  unfold mg
  rw [edgeStep_expect]
  apply Finset.sum_congr rfl
  intro C _
  have : ind f (insert e C) = ind f C := by
    unfold ind; simp [Finset.mem_insert, hf]
  rw [this]; ring

lemma mg_step_self (tr : RoundedTree E) (w w' δ : E → ℝ) (e : E) (q : Finset E → ℝ) :
    mg (edgeStep tr w w' δ e q) e =
      mg q e + ∑ C, q C * (coinProbClamped tr w w' δ e C * (1 - ind e C)) := by
  unfold mg
  rw [edgeStep_expect, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro C _
  have : ind e (insert e C) = 1 := by unfold ind; simp
  rw [this]; ring

lemma step_supp (tr : RoundedTree E) (w w' δ : E → ℝ) (e : E) (q : Finset E → ℝ)
    (C' : Finset E) (h : edgeStep tr w w' δ e q C' ≠ 0) :
    ∃ C, q C ≠ 0 ∧ ((coinProbClamped tr w w' δ e C ≠ 0 ∧ C' = insert e C) ∨ C' = C) := by
  unfold edgeStep at h
  obtain ⟨C, _, hC⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨C, left_ne_zero_of_mul hC, ?_⟩
  have h2 := right_ne_zero_of_mul hC
  by_cases hCC : C' = C
  · exact Or.inr hCC
  · left
    simp only [hCC, if_false, mul_zero, add_zero] at h2
    refine ⟨left_ne_zero_of_mul h2, ?_⟩
    by_contra hne
    simp [hne] at h2

lemma as_mem (q : Finset E → ℝ) (hnn : ∀ C, 0 ≤ q C) (hsum : ∑ C, q C = 1) (p : E)
    (hp : mg q p = 1) (C : Finset E) (hC : q C ≠ 0) : p ∈ C := by
  by_contra hpC
  have h0 : ∑ C, q C * (1 - ind p C) = 0 := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hsum]
    unfold mg at hp; rw [hp]; ring
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun C _ => ?_)).1 h0 C (Finset.mem_univ _)
  · unfold ind at hall; simp [hpC] at hall; exact hC hall
  · apply mul_nonneg (hnn C); unfold ind; split_ifs <;> norm_num

lemma clamp_eq (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : max 0 (min 1 x) = x := by
  rw [min_eq_right h1, max_eq_right h0]

lemma step (tr : RoundedTree E) (w w' δ : E → ℝ) (e : E) (cw : E → ℝ) (q : Finset E → ℝ)
    (hI : Inv tr cw q) (hδ : 0 ≤ δ e) (hw' : w' e = w e + δ e) (hcwe : cw e = w e)
    (hpar : ∀ p, tr.parent e = some p → cw p = w' p ∧ w' e ≤ w' p) :
    Inv tr (Function.update cw e (w' e)) (edgeStep tr w w' δ e q) := by
  obtain ⟨hnn, hsum, hmg, hsupp⟩ := hI
  have hasm : ∀ p, 1 ≤ cw p → ∀ C, q C ≠ 0 → p ∈ C := fun p hp =>
    as_mem q hnn hsum p (by rw [hmg, min_eq_right hp])
  refine ⟨edgeStep_nonneg tr w w' δ e q hnn, by rw [edgeStep_sum]; exact hsum, ?_, ?_⟩
  · intro f
    by_cases hf : f = e
    · subst hf
      rw [Function.update_self, mg_step_self, hmg, hcwe]
      rcases le_or_gt (δ f) 0 with hd | hd
      · have hd0 : δ f = 0 := le_antisymm hd hδ
        have hc : ∀ C, coinProbClamped tr w w' δ f C = 0 := by
          intro C; unfold coinProbClamped coinProb; simp [hd]
        simp [hc, hw', hd0]
      rcases lt_or_ge 1 (w' f) with h1 | h1
      · have hc : ∀ C, coinProbClamped tr w w' δ f C = 1 := by
          intro C; unfold coinProbClamped coinProb
          simp [not_le.2 hd, h1]
        simp only [hc, one_mul, mul_sub, mul_one, Finset.sum_sub_distrib, hsum]
        have := hmg f
        unfold mg at this; rw [this, hcwe, min_eq_right h1.le]; ring
      have hwlt : w f < 1 := by linarith
      -- the "constant coin" cases
      have hconst : ∀ κ : ℝ, κ = δ f / (1 - w f) →
          (∀ C, coinProbClamped tr w w' δ f C = κ) →
          min (w f) 1 + ∑ C, q C * (coinProbClamped tr w w' δ f C * (1 - ind f C)) =
            min (w' f) 1 := by
        intro κ hκ hc
        simp only [hc]
        have : ∑ C, q C * (κ * (1 - ind f C)) = κ * (∑ C, q C) - κ * mg q f := by
          unfold mg
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl; intro C _; ring
        rw [this, hsum, hmg, hcwe, min_eq_left hwlt.le, min_eq_left h1, hκ, hw']
        field_simp [(by linarith : (1 - w f) ≠ 0)]
      have hκ01 : 0 ≤ δ f / (1 - w f) ∧ δ f / (1 - w f) ≤ 1 := by
        constructor
        · exact div_nonneg hδ (by linarith)
        · rw [div_le_one (by linarith)]; linarith
      rcases hpe : tr.parent f with _ | p
      · apply hconst _ rfl
        intro C; unfold coinProbClamped coinProb
        simp only [not_le.2 hd, not_lt.2 h1, if_false, hpe]
        exact clamp_eq _ hκ01.1 hκ01.2
      obtain ⟨hcwp, hle⟩ := hpar p hpe
      rcases lt_or_ge 1 (w' p) with hp1 | hp1
      · apply hconst _ rfl
        intro C; unfold coinProbClamped coinProb
        simp only [not_le.2 hd, not_lt.2 h1, if_false, hpe, hp1, if_true]
        exact clamp_eq _ hκ01.1 hκ01.2
      -- parent case
      have hpos : 0 < w' p - w f := by linarith
      have hκ'01 : 0 ≤ δ f / (w' p - w f) ∧ δ f / (w' p - w f) ≤ 1 := by
        constructor
        · exact div_nonneg hδ hpos.le
        · rw [div_le_one hpos]; linarith
      have hc : ∀ C, coinProbClamped tr w w' δ f C = δ f / (w' p - w f) * ind p C := by
        intro C; unfold coinProbClamped coinProb ind
        simp only [not_le.2 hd, not_lt.2 h1, not_lt.2 hp1, if_false, hpe]
        split_ifs
        · rw [mul_one]; exact clamp_eq _ hκ'01.1 hκ'01.2
        · simp
      simp only [hc]
      have : ∑ C, q C * (δ f / (w' p - w f) * ind p C * (1 - ind f C)) =
          δ f / (w' p - w f) * (mg q p - mg q f) := by
        unfold mg
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro C _
        by_cases hq : q C = 0
        · simp [hq]
        by_cases hfC : f ∈ C
        · have := hsupp C hq f p hpe hfC; simp [ind, hfC, this]
        · by_cases hpC : p ∈ C <;> simp [ind, hfC, hpC, mul_comm]
      rw [this, hmg, hmg, hcwe, hcwp, min_eq_left hwlt.le, min_eq_left h1, min_eq_left hp1, hw']
      field_simp
    · rw [Function.update_of_ne hf, mg_step_ne tr w w' δ e f q hf, hmg]
  · intro C' hC' f p hfp hfC'
    obtain ⟨C, hqC, ⟨hc, rfl⟩ | rfl⟩ := step_supp tr w w' δ e q C' hC'
    · rcases Finset.mem_insert.1 hfC' with rfl | hfC
      · apply Finset.mem_insert_of_mem
        obtain ⟨hcwp, hle⟩ := hpar p hfp
        unfold coinProbClamped coinProb at hc
        rw [hfp] at hc
        split_ifs at hc with h1 h2
        · simp at hc
        · exact hasm p (by rw [hcwp]; linarith) C hqC
        · dsimp only at hc
          split_ifs at hc with h3 h4
          · exact hasm p (by rw [hcwp]; linarith) C hqC
          · exact h4
          · simp at hc
      · exact Finset.mem_insert_of_mem (hsupp C hqC f p hfp hfC)
    · exact hsupp _ hqC f p hfp hfC'

lemma iter (tr : RoundedTree E) (ord : List E) (hord_nodup : ord.Nodup) (hord_mem : ∀ e, e ∈ ord)
    (hord : ∀ e p, tr.parent e = some p → ord.idxOf p < ord.idxOf e)
    (w δ : E → ℝ) (hδ : ∀ e, 0 ≤ δ e)
    (hflow : ∀ e p, tr.parent e = some p → (w + δ) e ≤ (w + δ) p)
    (q : Finset E → ℝ) (hI : Inv tr w q) : Inv tr (w + δ) (iterStep tr ord w δ q) := by
  unfold iterStep
  suffices H : ∀ l₂ l₁ (q : Finset E → ℝ), l₁ ++ l₂ = ord →
      Inv tr (fun f => if f ∈ l₁ then (w + δ) f else w f) q →
      Inv tr (fun f => if f ∈ l₁ ++ l₂ then (w + δ) f else w f)
        (l₂.foldl (fun q e => edgeStep tr w (w + δ) δ e q) q) by
    have := H ord [] q (by simp) (by simpa using hI)
    have hfun : (fun f => if f ∈ [] ++ ord then (w + δ) f else w f) = w + δ := by
      funext f; simp [hord_mem f]
    rwa [hfun] at this
  intro l₂
  induction l₂ with
  | nil => intro l₁ q _ h; simpa using h
  | cons e rest ih =>
    intro l₁ q hl hI
    simp only [List.foldl_cons]
    have hl' : (l₁ ++ [e]) ++ rest = ord := by simpa using hl
    have := ih (l₁ ++ [e]) (edgeStep tr w (w + δ) δ e q) hl'
    simp only [List.append_assoc, List.singleton_append] at this
    apply this
    have he : e ∉ l₁ := by
      intro h
      have hd := List.disjoint_of_nodup_append (hl ▸ hord_nodup)
      exact hd h List.mem_cons_self
    have hfun : (fun f => if f ∈ l₁ ++ [e] then (w + δ) f else w f) =
        Function.update (fun f => if f ∈ l₁ then (w + δ) f else w f) e ((w + δ) e) := by
      funext f
      by_cases hf : f = e
      · subst hf; simp
      · simp [hf]
    rw [hfun]
    apply step tr w (w + δ) δ e _ q hI (hδ e) rfl (by simp [he])
    intro p hp
    have hpl : p ∈ l₁ := by
      by_contra hpn
      have h1 := hord e p hp
      rw [← hl, List.idxOf_append_of_notMem hpn, List.idxOf_append_of_notMem he,
        List.idxOf_cons_self] at h1
      omega
    exact ⟨by simp [hpl], hflow e p hp⟩

omit [Fintype E] [DecidableEq E] in
lemma fracWeight_append (A : List (E → ℝ)) (δ : E → ℝ) :
    fracWeight (A ++ [δ]) = fracWeight A + δ := by
  funext e; simp [fracWeight]

lemma main (tr : RoundedTree E)
    (ord : List E) (hord_nodup : ord.Nodup) (hord_mem : ∀ e, e ∈ ord)
    (hord : ∀ e p, tr.parent e = some p → ord.idxOf p < ord.idxOf e)
    (δs : List (E → ℝ)) (hδ : ∀ δ ∈ δs, ∀ e, 0 ≤ δ e)
    (hflow : ∀ T : ℕ, ∀ e p, tr.parent e = some p →
      fracWeight (δs.take T) e ≤ fracWeight (δs.take T) p) :
    Inv tr (fracWeight δs) (roundPMF tr ord δs) := by
  unfold roundPMF
  suffices H : ∀ B A (st : (E → ℝ) × (Finset E → ℝ)), A ++ B = δs → st.1 = fracWeight A →
      Inv tr st.1 st.2 →
      Inv tr (fracWeight δs) (B.foldl (fun (st : (E → ℝ) × (Finset E → ℝ)) δ =>
        (st.1 + δ, iterStep tr ord st.1 δ st.2)) st).2 by
    apply H δs [] _ (by simp)
    · funext e; simp [fracWeight]
    · refine ⟨?_, ?_, ?_, ?_⟩
      · intro C; dsimp only; split_ifs <;> norm_num
      · simp [Finset.sum_ite_eq']
      · intro f; simp only [mg, ind, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_eq_zero]; · simp
        intro C _; split_ifs with h1 h2 <;> first | rfl | (subst h2; simp at h1)
      · intro C hC f p _ hf
        dsimp only at hC
        split_ifs at hC with h
        · subst h; simp at hf
        · exact absurd rfl hC
  intro B
  induction B with
  | nil => intro A st hA h1 h2; simp at hA; subst hA; rw [← h1]; exact h2
  | cons δ rest ih =>
    intro A st hA h1 h2
    simp only [List.foldl_cons]
    apply ih (A ++ [δ]) _ (by simpa using hA)
    · simp [h1, fracWeight_append]
    · have hmem : δ ∈ δs := by rw [← hA]; simp
      have htake : δs.take (A.length + 1) = A ++ [δ] := by
        rw [← hA, List.take_append]; simp
      apply iter tr ord hord_nodup hord_mem hord st.1 δ (hδ δ hmem)
      · intro e p hp
        have := hflow (A.length + 1) e p hp
        rw [htake, fracWeight_append, ← h1] at this
        exact this
      · exact h2

end ZG88

open OnlinePrimalDual.GroupSteiner in
theorem solution {E : Type*} [Fintype E] [DecidableEq E] (tr : RoundedTree E)
    (ord : List E) (hord_nodup : ord.Nodup) (hord_mem : ∀ e, e ∈ ord)
    (hord : ∀ e p, tr.parent e = some p → ord.idxOf p < ord.idxOf e)
    (δs : List (E → ℝ)) (hδ : ∀ δ ∈ δs, ∀ e, 0 ≤ δ e)
    (hflow : ∀ T : ℕ, ∀ e p, tr.parent e = some p →
      fracWeight (δs.take T) e ≤ fracWeight (δs.take T) p) :
    (∀ e, fracWeight δs e ≤ 1 → (roundCover tr ord δs).marg e = fracWeight δs e) ∧
    (∀ e, 1 < fracWeight δs e → (roundCover tr ord δs).marg e = 1) := by
  have H := (ZG88.main tr ord hord_nodup hord_mem hord δs hδ hflow).2.2.1
  have hm : ∀ e, (roundCover tr ord δs).marg e = min (fracWeight δs e) 1 := by
    intro e
    rw [← H e]
    unfold RandomCover.marg ZG88.mg ZG88.ind roundCover
    simp [Finset.sum_filter]
  exact ⟨fun e he => by rw [hm, min_eq_left he], fun e he => by rw [hm, min_eq_right he.le]⟩
