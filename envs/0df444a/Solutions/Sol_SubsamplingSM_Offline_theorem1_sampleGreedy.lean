-- Prove2me | solution 1 for SubsamplingSM.Offline.theorem1_sampleGreedy
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T22:42:54.506029+00:00
-- url     : https://prove2.me/submissions/5db25164-d2b9-458c-ac6f-f458441faf25

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular
import Definitions.Def_SubsamplingSM_Offline_IsMonotoneSetFn
import Definitions.Def_SubsamplingSM_Offline_IsLinearSetFn
import Definitions.Def_SubsamplingSM_Offline_IsPExtendible
import Definitions.Def_SubsamplingSM_Offline_maxIndepSize
import Definitions.Def_SubsamplingSM_Offline_sampleGreedy
import Definitions.Def_SubsamplingSM_Offline_expectSample
import Definitions.Def_SubsamplingSM_Offline_sgQueries

set_option autoImplicit false

namespace SubsamplingSM.Offline.SGP
open Finset

section basic
variable {α : Type*} [LinearOrder α]

theorem marg_mem (f : Finset α → ℝ) {S : Finset α} {u : α} (h : u ∈ S) :
    marg f S u = 0 := by
  simp [marg, Finset.insert_eq_of_mem h]

theorem mem_cands {f : Finset α → ℝ} {I : Finset α → Prop} {T S : Finset α} {u : α} :
    u ∈ cands f I T S ↔ u ∈ T ∧ I (insert u S) ∧ 0 < marg f S u := by
  unfold cands
  simp only [Finset.mem_filter]

theorem not_mem_of_cands {f : Finset α → ℝ} {I : Finset α → Prop} {T S : Finset α} {u : α}
    (h : u ∈ cands f I T S) : u ∉ S := by
  intro hu
  have := (mem_cands.1 h).2.2
  rw [marg_mem f hu] at this
  exact lt_irrefl _ this

theorem pick_spec (f : Finset α → ℝ) (S C : Finset α) (hC : C.Nonempty) :
    pick f S C hC ∈ C ∧ marg f S (pick f S C hC) = C.sup' hC (marg f S) := by
  unfold pick
  exact Finset.mem_filter.1 (Finset.min'_mem _ _)

theorem pick_subset (f : Finset α → ℝ) (S C C' : Finset α) (hC : C.Nonempty)
    (hC' : C'.Nonempty) (hsub : C' ⊆ C) (hu : pick f S C hC ∈ C') :
    pick f S C' hC' = pick f S C hC := by
  obtain ⟨_, hval⟩ := pick_spec f S C hC
  have hsup : C'.sup' hC' (marg f S) = C.sup' hC (marg f S) := by
    apply le_antisymm
    · exact Finset.sup'_le hC' _ (fun x hx => Finset.le_sup' (marg f S) (hsub hx))
    · rw [← hval]; exact Finset.le_sup' (marg f S) hu
  have hA : (C'.filter (fun u => marg f S u = C'.sup' hC' (marg f S))) ⊆
      (C.filter (fun u => marg f S u = C.sup' hC (marg f S))) := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hsub hx.1, hx.2.trans hsup⟩
  have hmem : pick f S C hC ∈ C'.filter (fun u => marg f S u = C'.sup' hC' (marg f S)) := by
    rw [Finset.mem_filter]
    exact ⟨hu, hval.trans hsup.symm⟩
  apply le_antisymm
  · exact Finset.min'_le _ _ hmem
  · exact Finset.min'_subset _ hA

theorem step_cases (f : Finset α → ℝ) (I : Finset α → Prop) (T S : Finset α) :
    greedyStep f I T S = S ∨
      ∃ u ∈ cands f I T S, greedyStep f I T S = insert u S := by
  unfold greedyStep
  split_ifs with h
  · exact Or.inr ⟨_, (pick_spec f S _ h).1, rfl⟩
  · exact Or.inl rfl

theorem subset_step (f : Finset α → ℝ) (I : Finset α → Prop) (T S : Finset α) :
    S ⊆ greedyStep f I T S := by
  rcases step_cases f I T S with h | ⟨u, _, h⟩
  · rw [h]
  · rw [h]; exact Finset.subset_insert u S

theorem step_card (f : Finset α → ℝ) (I : Finset α → Prop) (T S : Finset α)
    (h : greedyStep f I T S ≠ S) : (greedyStep f I T S).card = S.card + 1 := by
  rcases step_cases f I T S with h' | ⟨u, hu, h'⟩
  · exact absurd h' h
  · rw [h', Finset.card_insert_of_notMem (not_mem_of_cands hu)]

theorem step_I (f : Finset α → ℝ) (I : Finset α → Prop) (T S : Finset α) (hS : I S) :
    I (greedyStep f I T S) := by
  rcases step_cases f I T S with h | ⟨u, hu, h⟩
  · rw [h]; exact hS
  · rw [h]; exact (mem_cands.1 hu).2.1

theorem step_sub (f : Finset α → ℝ) (I : Finset α → Prop) (T S X : Finset α)
    (hS : S ⊆ X ∪ T) : greedyStep f I T S ⊆ X ∪ T := by
  rcases step_cases f I T S with h | ⟨u, hu, h⟩
  · rw [h]; exact hS
  · rw [h]
    exact Finset.insert_subset (Finset.mem_union_right _ (mem_cands.1 hu).1) hS

theorem step_of_empty (f : Finset α → ℝ) (I : Finset α → Prop) (T S : Finset α)
    (h : cands f I T S = ∅) : greedyStep f I T S = S := by
  unfold greedyStep
  rw [dif_neg]
  rw [h]; exact Finset.not_nonempty_empty

end basic

section iter
variable {α : Type*} [Fintype α] [LinearOrder α]

theorem iter_fixed (f : Finset α → ℝ) (I : Finset α → Prop) (T X : Finset α) :
    greedyStep f I T ((greedyStep f I T)^[Fintype.card α] X) =
      (greedyStep f I T)^[Fintype.card α] X := by
  have key : ∀ j : ℕ, (greedyStep f I T)^[j+1] X ≠ (greedyStep f I T)^[j] X →
      j + 1 ≤ ((greedyStep f I T)^[j+1] X).card := by
    intro j
    induction j with
    | zero =>
      intro h
      have h' : greedyStep f I T X ≠ X := by simpa using h
      have := step_card f I T X h'
      simp only [zero_add, Function.iterate_one]
      omega
    | succ j ih =>
      intro h
      have hne : (greedyStep f I T)^[j+1] X ≠ (greedyStep f I T)^[j] X := by
        intro he
        apply h
        have e1 : (greedyStep f I T)^[j+1+1] X =
            greedyStep f I T ((greedyStep f I T)^[j+1] X) :=
          Function.iterate_succ_apply' _ (j+1) X
        rw [e1, he]
        exact (Function.iterate_succ_apply' _ j X).symm.trans he
      have h1 := ih hne
      have h2 : ((greedyStep f I T)^[j+1+1] X).card =
          ((greedyStep f I T)^[j+1] X).card + 1 := by
        rw [Function.iterate_succ_apply' _ (j+1) X]
        apply step_card
        rw [← Function.iterate_succ_apply' (greedyStep f I T) (j+1) X]
        exact h
      omega
  by_contra hc
  have h3 := key (Fintype.card α) (by rw [Function.iterate_succ_apply']; exact hc)
  have h4 := Finset.card_le_univ ((greedyStep f I T)^[Fintype.card α + 1] X)
  omega

/-- the greedy run from `S` on pool `P` -/
noncomputable def G (f : Finset α → ℝ) (I : Finset α → Prop) (P S : Finset α) : Finset α :=
  (greedyStep f I P)^[Fintype.card α] S

theorem G_step (f : Finset α → ℝ) (I : Finset α → Prop) (P S : Finset α) :
    G f I P (greedyStep f I P S) = G f I P S := by
  unfold G
  rw [← Function.iterate_succ_apply, Function.iterate_succ_apply', iter_fixed]

theorem G_of_empty (f : Finset α → ℝ) (I : Finset α → Prop) (P S : Finset α)
    (h : cands f I P S = ∅) : G f I P S = S :=
  Function.iterate_fixed (step_of_empty f I P S h) _

theorem subset_G (f : Finset α → ℝ) (I : Finset α → Prop) (P S : Finset α) :
    S ⊆ G f I P S := by
  unfold G
  generalize Fintype.card α = m
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (subset_step f I P _)

theorem G_sub (f : Finset α → ℝ) (I : Finset α → Prop) (P S : Finset α) :
    G f I P S ⊆ S ∪ P := by
  unfold G
  generalize Fintype.card α = m
  induction m with
  | zero => exact Finset.subset_union_left
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact step_sub f I P _ S ih

theorem G_I (f : Finset α → ℝ) (I : Finset α → Prop) (P S : Finset α) (hS : I S) :
    I (G f I P S) := by
  unfold G
  generalize Fintype.card α = m
  induction m with
  | zero => exact hS
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact step_I f I P _ ih

theorem sampleGreedy_eq (f : Finset α → ℝ) (I : Finset α → Prop) (T : Finset α) :
    sampleGreedy f I T = G f I T ∅ := rfl

end iter

section weights
variable {α : Type*} [DecidableEq α]

def w (q : ℝ) (R T : Finset α) : ℝ := q ^ T.card * (1 - q) ^ (R.card - T.card)

def E (q : ℝ) (R : Finset α) (X : Finset α → ℝ) : ℝ := ∑ T ∈ R.powerset, w q R T * X T

theorem E_insert (q : ℝ) {R : Finset α} {u : α} (hu : u ∉ R) (X : Finset α → ℝ) :
    E q (insert u R) X = q * E q R (fun T => X (insert u T)) + (1 - q) * E q R X := by
  unfold E
  rw [Finset.sum_powerset_insert hu, Finset.mul_sum, Finset.mul_sum, add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro T hT
    have hTR := Finset.mem_powerset.1 hT
    have huT : u ∉ T := fun h => hu (hTR h)
    unfold w
    rw [Finset.card_insert_of_notMem huT, Finset.card_insert_of_notMem hu]
    have : R.card + 1 - (T.card + 1) = R.card - T.card := by omega
    rw [this, pow_succ]
    ring
  · apply Finset.sum_congr rfl
    intro T hT
    have hTR := Finset.mem_powerset.1 hT
    have hle := Finset.card_le_card hTR
    unfold w
    rw [Finset.card_insert_of_notMem hu]
    have : R.card + 1 - T.card = R.card - T.card + 1 := by omega
    rw [this, pow_succ]
    ring

theorem w_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (R T : Finset α) : 0 ≤ w q R T :=
  mul_nonneg (pow_nonneg hq0 _) (pow_nonneg (by linarith) _)

theorem E_const (q : ℝ) (R : Finset α) (c : ℝ) : E q R (fun _ => c) = c := by
  induction R using Finset.induction_on with
  | empty => simp [E, w]
  | insert u R hu ih =>
    rw [E_insert q hu, ih]
    ring

theorem E_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (R : Finset α) (X Y : Finset α → ℝ) (c : ℝ)
    (h : ∀ T, T ⊆ R → X T ≤ Y T + c) : E q R X ≤ E q R Y + c := by
  have hc := E_const q R c
  unfold E at hc ⊢
  rw [← hc, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro T hT
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (h T (Finset.mem_powerset.1 hT)) (w_nonneg hq0 hq1 R T)

end weights

theorem E_univ {α : Type*} [Fintype α] [DecidableEq α] (q : ℝ) (X : Finset α → ℝ) :
    expectSample q X = E q Finset.univ X := by
  simp only [expectSample, E, w, bernW, Finset.powerset_univ, Finset.card_univ]

section submod
variable {α : Type*} [DecidableEq α]

/-- telescoping bound: adding `Y` to `X ⊇ S` gains at most `|Y| c` when every marginal
over `S` of an element of `Y` is at most `c ≥ 0`. -/
theorem union_le {f : Finset α → ℝ} (hf : IsSubmodular f) {S X : Finset α} (hSX : S ⊆ X)
    (Y : Finset α) {c : ℝ} (hc : 0 ≤ c) (hY : ∀ y ∈ Y, marg f S y ≤ c) :
    f (X ∪ Y) ≤ f X + Y.card * c := by
  induction Y using Finset.induction_on with
  | empty => simp
  | insert y Y hy ih =>
    have ih' := ih (fun z hz => hY z (Finset.mem_insert_of_mem hz))
    rw [Finset.union_insert, Finset.card_insert_of_notMem hy]
    push_cast
    by_cases hm : y ∈ X ∪ Y
    · rw [Finset.insert_eq_of_mem hm]; nlinarith
    · have h1 := hf S (X ∪ Y) y (hSX.trans Finset.subset_union_left) hm
      have h2 := hY y (Finset.mem_insert_self y Y)
      unfold marg at h2
      nlinarith

end submod


section weights2
variable {β : Type*} [DecidableEq β]

theorem E_congr (q : ℝ) (R : Finset β) (X Y : Finset β → ℝ)
    (h : ∀ T, T ⊆ R → X T = Y T) : E q R X = E q R Y := by
  unfold E
  exact Finset.sum_congr rfl (fun T hT => by rw [h T (Finset.mem_powerset.1 hT)])

theorem E_add (q : ℝ) (R : Finset β) (X : Finset β → ℝ) (c : ℝ) :
    E q R (fun T => X T + c) = E q R X + c := by
  have hc := E_const q R c
  unfold E at hc ⊢
  conv_rhs => rw [← hc]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun T _ => by ring)

theorem E_mul (q : ℝ) (R : Finset β) (X : Finset β → ℝ) (c : ℝ) :
    E q R (fun T => c * X T) = c * E q R X := by
  unfold E
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun T _ => by ring)

theorem E_ind (q : ℝ) {R : Finset β} {v : β} (hv : v ∈ R) :
    E q R (fun T => if v ∈ T then (1 : ℝ) else 0) = q := by
  rw [← Finset.insert_erase hv, E_insert q (Finset.notMem_erase v R),
    E_congr q (R.erase v) (fun T => if v ∈ insert v T then (1 : ℝ) else 0) (fun _ => 1)
      (fun T _ => by simp),
    E_congr q (R.erase v) (fun T => if v ∈ T then (1 : ℝ) else 0) (fun _ => 0)
      (fun T hT => by
        have : v ∉ T := fun h => Finset.notMem_erase v R (hT h)
        simp [this]),
    E_const, E_const]
  ring

theorem E_card (q : ℝ) (R : Finset β) : E q R (fun T => (T.card : ℝ)) = q * R.card := by
  induction R using Finset.induction_on with
  | empty => simp [E, w]
  | insert u R hu ih =>
    rw [E_insert q hu, E_congr q R (fun T => ((insert u T).card : ℝ)) (fun T => (T.card : ℝ) + 1)
      (fun T hT => by
        rw [Finset.card_insert_of_notMem (fun h => hu (hT h))]; push_cast; ring),
      E_add, ih, Finset.card_insert_of_notMem hu]
    push_cast
    ring

theorem union_erase_of_mem {X O : Finset β} {u : β} (h : u ∈ X) : X ∪ O.erase u = X ∪ O := by
  ext x
  simp only [Finset.mem_union, Finset.mem_erase]
  constructor
  · rintro (h1 | ⟨_, h1⟩)
    · exact Or.inl h1
    · exact Or.inr h1
  · rintro (h1 | h1)
    · exact Or.inl h1
    · by_cases hx : x = u
      · exact Or.inl (hx ▸ h)
      · exact Or.inr ⟨hx, h1⟩

theorem union_erase_singleton {X O : Finset β} {u : β} (h : u ∈ O) :
    X ∪ O.erase u ∪ {u} = X ∪ O := by
  ext x
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
  constructor
  · rintro ((h1 | ⟨_, h1⟩) | h1)
    · exact Or.inl h1
    · exact Or.inr h1
    · exact Or.inr (h1 ▸ h)
  · rintro (h1 | h1)
    · exact Or.inl (Or.inl h1)
    · by_cases hx : x = u
      · exact Or.inr hx
      · exact Or.inl (Or.inr ⟨hx, h1⟩)

theorem ins_union_sdiff {S O Y : Finset β} (u : β) (hYS : ∀ y ∈ Y, y ∉ S) :
    insert u S ∪ O \ Y = insert u ((S ∪ O) \ Y) := by
  rw [Finset.insert_union]
  congr 1
  ext x
  simp only [Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact ⟨Or.inl h, fun hy => hYS x hy h⟩
    · exact ⟨Or.inr h1, h2⟩
  · rintro ⟨h1 | h1, h2⟩
    · exact Or.inl h1
    · exact Or.inr ⟨h1, h2⟩

theorem submod_union {f : Finset β → ℝ} (hf : IsSubmodular f) (O : Finset β) :
    IsSubmodular (fun X => f (X ∪ O)) := by
  intro A B e hAB heB
  show f (insert e B ∪ O) - f (B ∪ O) ≤ f (insert e A ∪ O) - f (A ∪ O)
  by_cases heO : e ∈ O
  · have h1 : insert e B ∪ O = B ∪ O := by
      rw [Finset.insert_union, Finset.insert_eq_of_mem (Finset.mem_union_right _ heO)]
    have h2 : insert e A ∪ O = A ∪ O := by
      rw [Finset.insert_union, Finset.insert_eq_of_mem (Finset.mem_union_right _ heO)]
    rw [h1, h2]
    simp
  · rw [Finset.insert_union, Finset.insert_union]
    exact hf (A ∪ O) (B ∪ O) e (Finset.union_subset_union hAB (subset_refl O))
      (by simp [heB, heO])

end weights2

section sampling
variable {ι β : Type*} [DecidableEq β]

theorem sampling (Ω : Finset ι) (μ : ι → ℝ) (hμ : ∀ i ∈ Ω, 0 ≤ μ i) (hμ1 : ∑ i ∈ Ω, μ i = 1)
    (g : Finset β → ℝ) (hg : IsSubmodular g) (hg0 : ∀ X, 0 ≤ g X) (q : ℝ) (N : Finset β) :
    ∀ (A : ι → Finset β) (c : ℝ), (∀ i ∈ Ω, A i ⊆ N) → 0 ≤ c → c ≤ q →
      (∀ v ∈ N, c ≤ ∑ i ∈ Ω, μ i * (if v ∈ A i then (1 : ℝ) else 0)) →
      (∀ v ∈ N, ∑ i ∈ Ω, μ i * (if v ∈ A i then (1 : ℝ) else 0) ≤ q) →
      (1 - q) * g ∅ + c * g N ≤ ∑ i ∈ Ω, μ i * g (A i) := by
  induction N using Finset.strongInduction with
  | H N ih =>
  intro A c hA hc0 hcq hlo hhi
  rcases N.eq_empty_or_nonempty with hN | hN
  · subst hN
    have hAe : ∀ i ∈ Ω, A i = ∅ := fun i hi => Finset.subset_empty.1 (hA i hi)
    rw [Finset.sum_congr rfl (fun i hi => by rw [hAe i hi]), ← Finset.sum_mul, hμ1]
    nlinarith [hg0 ∅]
  · obtain ⟨u, huN, humin⟩ := Finset.exists_min_image N
      (fun v => ∑ i ∈ Ω, μ i * (if v ∈ A i then (1 : ℝ) else 0)) hN
    have hPe : ∀ v ∈ N.erase u, ∑ i ∈ Ω, μ i * (if v ∈ (A i).erase u then (1 : ℝ) else 0) =
        ∑ i ∈ Ω, μ i * (if v ∈ A i then (1 : ℝ) else 0) := by
      intro v hv
      have hvu : v ≠ u := Finset.ne_of_mem_erase hv
      exact Finset.sum_congr rfl (fun i _ => by simp [hvu])
    have ih' := ih (N.erase u) (Finset.erase_ssubset huN) (fun i => (A i).erase u)
      (∑ i ∈ Ω, μ i * (if u ∈ A i then (1 : ℝ) else 0))
      (fun i hi => Finset.erase_subset_erase u (hA i hi)) (le_trans hc0 (hlo u huN)) (hhi u huN)
      (fun v hv => by rw [hPe v hv]; exact humin v (Finset.mem_of_mem_erase hv))
      (fun v hv => by rw [hPe v hv]; exact hhi v (Finset.mem_of_mem_erase hv))
    have hpt : ∀ i ∈ Ω, g ((A i).erase u) + (if u ∈ A i then (1 : ℝ) else 0) *
        (g N - g (N.erase u)) ≤ g (A i) := by
      intro i hi
      by_cases h : u ∈ A i
      · have hs := hg ((A i).erase u) (N.erase u) u (Finset.erase_subset_erase u (hA i hi))
          (Finset.notMem_erase u N)
        rw [Finset.insert_erase huN, Finset.insert_erase h] at hs
        rw [if_pos h]
        linarith
      · rw [if_neg h, Finset.erase_eq_of_notMem h]
        simp
    have hsum : ∑ i ∈ Ω, μ i * g ((A i).erase u) +
        (∑ i ∈ Ω, μ i * (if u ∈ A i then (1 : ℝ) else 0)) * (g N - g (N.erase u)) ≤
          ∑ i ∈ Ω, μ i * g (A i) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i hi
      calc μ i * g ((A i).erase u) + μ i * (if u ∈ A i then (1 : ℝ) else 0) *
            (g N - g (N.erase u))
          = μ i * (g ((A i).erase u) + (if u ∈ A i then (1 : ℝ) else 0) *
            (g N - g (N.erase u))) := by ring
        _ ≤ μ i * g (A i) := mul_le_mul_of_nonneg_left (hpt i hi) (hμ i hi)
    have hcN := mul_le_mul_of_nonneg_right (hlo u huN) (hg0 N)
    linarith

end sampling

section claims
variable {α : Type*} [Fintype α] [LinearOrder α]

theorem cands_sub (f : Finset α → ℝ) (I : Finset α → Prop) {R S T T0 : Finset α}
    (hT : T ⊆ R) (hT0 : T0 ⊆ S) : cands f I (T ∪ T0) S ⊆ cands f I R S := by
  intro x hx
  obtain ⟨hxP, hxI, hxm⟩ := mem_cands.1 hx
  rcases Finset.mem_union.1 hxP with h | h
  · exact mem_cands.2 ⟨hT h, hxI, hxm⟩
  · rw [marg_mem f (hT0 h)] at hxm
    exact absurd hxm (lt_irrefl 0)

theorem G_heads (f : Finset α → ℝ) (I : Finset α → Prop) {R S T T0 : Finset α} {u : α}
    (hC : (cands f I R S).Nonempty) (hu : pick f S (cands f I R S) hC = u)
    (hT : T ⊆ R) (hT0 : T0 ⊆ S) :
    G f I (insert u T ∪ T0) S = G f I (T ∪ insert u T0) (insert u S) := by
  have huC : u ∈ cands f I R S := by rw [← hu]; exact (pick_spec f S _ hC).1
  obtain ⟨huR, hIu, hpos⟩ := mem_cands.1 huC
  have hsubP : cands f I (insert u T ∪ T0) S ⊆ cands f I R S :=
    cands_sub f I (Finset.insert_subset huR hT) hT0
  have huP : u ∈ cands f I (insert u T ∪ T0) S :=
    mem_cands.2 ⟨Finset.mem_union_left _ (Finset.mem_insert_self u T), hIu, hpos⟩
  have hne : (cands f I (insert u T ∪ T0) S).Nonempty := ⟨u, huP⟩
  have hstep : greedyStep f I (insert u T ∪ T0) S = insert u S := by
    unfold greedyStep
    rw [dif_pos hne, pick_subset f S _ _ hC hne hsubP (by rw [hu]; exact huP), hu]
  have hP : insert u T ∪ T0 = T ∪ insert u T0 := by
    rw [Finset.insert_union, Finset.union_insert]
  rw [← G_step f I (insert u T ∪ T0) S, hstep, hP]

set_option maxHeartbeats 1000000 in
theorem claimA (f : Finset α → ℝ) (I : Finset α → Prop) (p : ℕ) (hf : IsSubmodular f)
    (hI : IsPExtendible I p) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hqp : 1 - q = q * p) :
    ∀ n : ℕ, ∀ R S T0 O : Finset α, R.card = n → Disjoint S R → T0 ⊆ S → O ⊆ R →
      I (S ∪ O) →
      E q R (fun T => f (G f I (T ∪ T0) S ∪ O)) + p * f S ≤
        (p + 1) * E q R (fun T => f (G f I (T ∪ T0) S)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro R S T0 O hn hSR hT0 hO hSO
  have hIS : I S := hI.1.2 S (S ∪ O) Finset.subset_union_left hSO
  have hIy : ∀ y ∈ O, I (insert y S) := fun y hy =>
    hI.1.2 _ _ (Finset.insert_subset (Finset.mem_union_right _ hy) Finset.subset_union_left) hSO
  by_cases hC : (cands f I R S).Nonempty
  swap
  · have hC' : cands f I R S = ∅ := Finset.not_nonempty_iff_eq_empty.1 hC
    have hG : ∀ T, T ⊆ R → G f I (T ∪ T0) S = S := fun T hT =>
      G_of_empty f I _ S (Finset.subset_empty.1 (hC' ▸ cands_sub f I hT hT0))
    rw [E_congr q R (fun T => f (G f I (T ∪ T0) S ∪ O)) (fun _ => f (S ∪ O)) (fun T hT => by rw [hG T hT]),
      E_congr q R (fun T => f (G f I (T ∪ T0) S)) (fun _ => f S) (fun T hT => by rw [hG T hT]), E_const, E_const]
    have h0 : f (S ∪ O) ≤ f S + O.card * 0 := union_le hf le_rfl O le_rfl (fun y hy => by
      by_contra hneg
      push_neg at hneg
      have hy' : y ∈ cands f I R S := mem_cands.2 ⟨hO hy, hIy y hy, hneg⟩
      rw [hC'] at hy'
      exact Finset.notMem_empty y hy')
    linarith
  obtain ⟨u, hu⟩ : ∃ u, pick f S (cands f I R S) hC = u := ⟨_, rfl⟩
  have huC : u ∈ cands f I R S := by rw [← hu]; exact (pick_spec f S _ hC).1
  have hΔ : marg f S u = (cands f I R S).sup' hC (marg f S) := by
    rw [← hu]; exact (pick_spec f S _ hC).2
  obtain ⟨huR, hIu, hpos⟩ := mem_cands.1 huC
  have huS : u ∉ S := not_mem_of_cands huC
  have huR' : u ∉ R.erase u := Finset.notMem_erase u R
  have hcard : (R.erase u).card < n := by
    rw [Finset.card_erase_of_mem huR]; have := Finset.card_pos.2 ⟨u, huR⟩; omega
  have hSR' : Disjoint S (R.erase u) :=
    Finset.disjoint_of_subset_right (Finset.erase_subset u R) hSR
  have hSuR' : Disjoint (insert u S) (R.erase u) := by
    rw [Finset.disjoint_insert_left]; exact ⟨huR', hSR'⟩
  have hT0u : insert u T0 ⊆ insert u S := Finset.insert_subset_insert u hT0
  have hmarg : f (insert u S) = f S + marg f S u := by unfold marg; ring
  have hle_marg : ∀ y ∈ O, marg f S y ≤ marg f S u := by
    intro y hy
    by_cases hy' : 0 < marg f S y
    · rw [hΔ]; exact Finset.le_sup' (marg f S) (mem_cands.2 ⟨hO hy, hIy y hy, hy'⟩)
    · push_neg at hy'; linarith
  have hheads : ∀ T, T ⊆ R.erase u →
      G f I (insert u T ∪ T0) S = G f I (T ∪ insert u T0) (insert u S) := fun T hT =>
    G_heads f I hC hu (hT.trans (Finset.erase_subset u R)) hT0
  have hGu : ∀ T, u ∈ G f I (T ∪ insert u T0) (insert u S) := fun T =>
    subset_G f I _ _ (Finset.mem_insert_self u S)
  have hEG : E q (R.erase u) (fun T => f (G f I (insert u T ∪ T0) S)) =
      E q (R.erase u) (fun T => f (G f I (T ∪ insert u T0) (insert u S))) :=
    E_congr q _ _ _ (fun T hT => by rw [hheads T hT])
  rw [← Finset.insert_erase huR, E_insert q huR', E_insert q huR', hEG]
  have h1q : 0 ≤ 1 - q := by linarith
  by_cases huO : u ∈ O
  · have A1 := ih _ hcard (R.erase u) (insert u S) (insert u T0) (O.erase u) rfl hSuR' hT0u
      (Finset.erase_subset_erase u hO) (by
        rw [Finset.insert_union, ← Finset.union_insert, Finset.insert_erase huO]; exact hSO)
    have A2 := ih _ hcard (R.erase u) S T0 (O.erase u) rfl hSR' hT0
      (Finset.erase_subset_erase u hO)
      (hI.1.2 _ _ (Finset.union_subset_union (subset_refl S) (Finset.erase_subset u O)) hSO)
    have hEh : E q (R.erase u) (fun T => f (G f I (insert u T ∪ T0) S ∪ O)) =
        E q (R.erase u) (fun T => f (G f I (T ∪ insert u T0) (insert u S) ∪ O.erase u)) :=
      E_congr q _ _ _ (fun T hT => by
        rw [hheads T hT, union_erase_of_mem (hGu T)])
    have hEt : E q (R.erase u) (fun T => f (G f I (T ∪ T0) S ∪ O)) ≤
        E q (R.erase u) (fun T => f (G f I (T ∪ T0) S ∪ O.erase u)) + marg f S u :=
      E_le hq0 hq1 _ _ _ _ (fun T _ => by
        have h := union_le hf ((subset_G f I (T ∪ T0) S).trans
          (Finset.subset_union_left (s₂ := O.erase u))) {u}
          (le_of_lt hpos) (fun y hy => by rw [Finset.mem_singleton.1 hy])
        rw [Finset.card_singleton, Nat.cast_one, one_mul, union_erase_singleton huO] at h
        exact h)
    rw [hEh]
    rw [hmarg] at A1
    have e1 : (1 - q) * marg f S u = q * p * marg f S u := by rw [hqp]
    have B1 := mul_le_mul_of_nonneg_left A1 hq0
    have B2 := mul_le_mul_of_nonneg_left hEt h1q
    have B3 := mul_le_mul_of_nonneg_left A2 h1q
    linarith
  · obtain ⟨Y, hY, hYc, hIY⟩ := hI.2 S (S ∪ O) u hIS hSO Finset.subset_union_left huS hIu
    have hYO : Y ⊆ O := fun y hy => by
      have h := hY hy
      rw [Finset.mem_sdiff, Finset.mem_union] at h
      tauto
    have hYS : ∀ y ∈ Y, y ∉ S := fun y hy => (Finset.mem_sdiff.1 (hY hy)).2
    have hOR' : O ⊆ R.erase u := fun x hx =>
      Finset.mem_erase.2 ⟨fun h => huO (h ▸ hx), hO hx⟩
    have A1 := ih _ hcard (R.erase u) (insert u S) (insert u T0) (O \ Y) rfl hSuR' hT0u
      (Finset.sdiff_subset.trans hOR') (by rw [ins_union_sdiff u hYS]; exact hIY)
    have A2 := ih _ hcard (R.erase u) S T0 O rfl hSR' hT0 hOR' hSO
    have hEh : E q (R.erase u) (fun T => f (G f I (insert u T ∪ T0) S ∪ O)) ≤
        E q (R.erase u) (fun T => f (G f I (T ∪ insert u T0) (insert u S) ∪ O \ Y)) +
          p * marg f S u :=
      E_le hq0 hq1 _ _ _ _ (fun T hT => by
        rw [hheads T hT]
        have hS' : S ⊆ G f I (T ∪ insert u T0) (insert u S) ∪ O \ Y :=
          ((Finset.subset_insert u S).trans (subset_G f I _ _)).trans Finset.subset_union_left
        have h := union_le hf hS' Y (le_of_lt hpos) (fun y hy => hle_marg y (hYO hy))
        rw [Finset.union_assoc, Finset.sdiff_union_of_subset hYO] at h
        have : (Y.card : ℝ) * marg f S u ≤ p * marg f S u :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hYc) (le_of_lt hpos)
        linarith)
    rw [hmarg] at A1
    have B1 := mul_le_mul_of_nonneg_left A1 hq0
    have B1' := mul_le_mul_of_nonneg_left hEh hq0
    have B2 := mul_le_mul_of_nonneg_left A2 h1q
    linarith

set_option maxHeartbeats 1000000 in
theorem claimB (f : Finset α → ℝ) (I : Finset α → Prop) (p : ℕ) (hlin : IsLinearSetFn f)
    (hI : IsPExtendible I p) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hqp : q * p = 1) :
    ∀ n : ℕ, ∀ R S T0 O : Finset α, R.card = n → Disjoint S R → T0 ⊆ S → O ⊆ R →
      I (S ∪ O) →
      ((p : ℝ) - 1) * f S + f (S ∪ O) ≤ p * E q R (fun T => f (G f I (T ∪ T0) S)) := by
  have hf : IsSubmodular f := fun A B e h1 h2 => le_of_eq (hlin A B e h1 h2)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro R S T0 O hn hSR hT0 hO hSO
  have hIS : I S := hI.1.2 S (S ∪ O) Finset.subset_union_left hSO
  have hIy : ∀ y ∈ O, I (insert y S) := fun y hy =>
    hI.1.2 _ _ (Finset.insert_subset (Finset.mem_union_right _ hy) Finset.subset_union_left) hSO
  by_cases hC : (cands f I R S).Nonempty
  swap
  · have hC' : cands f I R S = ∅ := Finset.not_nonempty_iff_eq_empty.1 hC
    have hG : ∀ T, T ⊆ R → G f I (T ∪ T0) S = S := fun T hT =>
      G_of_empty f I _ S (Finset.subset_empty.1 (hC' ▸ cands_sub f I hT hT0))
    rw [E_congr q R (fun T => f (G f I (T ∪ T0) S)) (fun _ => f S) (fun T hT => by rw [hG T hT]), E_const]
    have h0 : f (S ∪ O) ≤ f S + O.card * 0 := union_le hf le_rfl O le_rfl (fun y hy => by
      by_contra hneg
      push_neg at hneg
      have hy' : y ∈ cands f I R S := mem_cands.2 ⟨hO hy, hIy y hy, hneg⟩
      rw [hC'] at hy'
      exact Finset.notMem_empty y hy')
    linarith
  obtain ⟨u, hu⟩ : ∃ u, pick f S (cands f I R S) hC = u := ⟨_, rfl⟩
  have huC : u ∈ cands f I R S := by rw [← hu]; exact (pick_spec f S _ hC).1
  have hΔ : marg f S u = (cands f I R S).sup' hC (marg f S) := by
    rw [← hu]; exact (pick_spec f S _ hC).2
  obtain ⟨huR, hIu, hpos⟩ := mem_cands.1 huC
  have huS : u ∉ S := not_mem_of_cands huC
  have huR' : u ∉ R.erase u := Finset.notMem_erase u R
  have hcard : (R.erase u).card < n := by
    rw [Finset.card_erase_of_mem huR]; have := Finset.card_pos.2 ⟨u, huR⟩; omega
  have hSR' : Disjoint S (R.erase u) :=
    Finset.disjoint_of_subset_right (Finset.erase_subset u R) hSR
  have hSuR' : Disjoint (insert u S) (R.erase u) := by
    rw [Finset.disjoint_insert_left]; exact ⟨huR', hSR'⟩
  have hT0u : insert u T0 ⊆ insert u S := Finset.insert_subset_insert u hT0
  have hmarg : f (insert u S) = f S + marg f S u := by unfold marg; ring
  have hle_marg : ∀ y ∈ O, marg f S y ≤ marg f S u := by
    intro y hy
    by_cases hy' : 0 < marg f S y
    · rw [hΔ]; exact Finset.le_sup' (marg f S) (mem_cands.2 ⟨hO hy, hIy y hy, hy'⟩)
    · push_neg at hy'; linarith
  have hheads : ∀ T, T ⊆ R.erase u →
      G f I (insert u T ∪ T0) S = G f I (T ∪ insert u T0) (insert u S) := fun T hT =>
    G_heads f I hC hu (hT.trans (Finset.erase_subset u R)) hT0
  have hEG : E q (R.erase u) (fun T => f (G f I (insert u T ∪ T0) S)) =
      E q (R.erase u) (fun T => f (G f I (T ∪ insert u T0) (insert u S))) :=
    E_congr q _ _ _ (fun T hT => by rw [hheads T hT])
  rw [← Finset.insert_erase huR, E_insert q huR', hEG]
  have h1q : 0 ≤ 1 - q := by linarith
  by_cases huO : u ∈ O
  · have hSO' : insert u S ∪ O.erase u = S ∪ O := by
      rw [Finset.insert_union, ← Finset.union_insert, Finset.insert_erase huO]
    have A1 := ih _ hcard (R.erase u) (insert u S) (insert u T0) (O.erase u) rfl hSuR' hT0u
      (Finset.erase_subset_erase u hO) (by rw [hSO']; exact hSO)
    have A2 := ih _ hcard (R.erase u) S T0 (O.erase u) rfl hSR' hT0
      (Finset.erase_subset_erase u hO)
      (hI.1.2 _ _ (Finset.union_subset_union (subset_refl S) (Finset.erase_subset u O)) hSO)
    have hnot : u ∉ S ∪ O.erase u := by simp [huS]
    have hL := hlin S (S ∪ O.erase u) u Finset.subset_union_left hnot
    rw [← Finset.union_insert, Finset.insert_erase huO] at hL
    have hL' : f (S ∪ O.erase u) = f (S ∪ O) - marg f S u := by unfold marg; linarith
    rw [hSO', hmarg] at A1
    rw [hL'] at A2
    have e1 : q * p * marg f S u = marg f S u := by rw [hqp, one_mul]
    have B1 := mul_le_mul_of_nonneg_left A1 hq0
    have B2 := mul_le_mul_of_nonneg_left A2 h1q
    linarith
  · obtain ⟨Y, hY, hYc, hIY⟩ := hI.2 S (S ∪ O) u hIS hSO Finset.subset_union_left huS hIu
    have hYO : Y ⊆ O := fun y hy => by
      have h := hY hy
      rw [Finset.mem_sdiff, Finset.mem_union] at h
      tauto
    have hYS : ∀ y ∈ Y, y ∉ S := fun y hy => (Finset.mem_sdiff.1 (hY hy)).2
    have hOR' : O ⊆ R.erase u := fun x hx =>
      Finset.mem_erase.2 ⟨fun h => huO (h ▸ hx), hO hx⟩
    have A1 := ih _ hcard (R.erase u) (insert u S) (insert u T0) (O \ Y) rfl hSuR' hT0u
      (Finset.sdiff_subset.trans hOR') (by rw [ins_union_sdiff u hYS]; exact hIY)
    have A2 := ih _ hcard (R.erase u) S T0 O rfl hSR' hT0 hOR' hSO
    have hnot : u ∉ S ∪ O \ Y := by simp [huS, huO]
    have hL := hlin S (S ∪ O \ Y) u Finset.subset_union_left hnot
    rw [Finset.insert_union] at A1
    have hU := union_le hf (Finset.subset_union_left (s₂ := O \ Y)) Y (le_of_lt hpos)
      (fun y hy => hle_marg y (hYO hy))
    rw [Finset.union_assoc, Finset.sdiff_union_of_subset hYO] at hU
    have hYp : (Y.card : ℝ) * marg f S u ≤ p * marg f S u :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hYc) (le_of_lt hpos)
    rw [hmarg] at A1
    have hh : ((p : ℝ) - 1) * f S + f (S ∪ O) ≤
        p * E q (R.erase u) (fun T => f (G f I (T ∪ insert u T0) (insert u S))) := by
      linarith [hmarg]
    have B1 := mul_le_mul_of_nonneg_left hh hq0
    have B2 := mul_le_mul_of_nonneg_left A2 h1q
    linarith

/-! ## oracle-call accounting -/

def Inv (f : Finset α → ℝ) (I : Finset α → Prop) (T : Finset α) (st : SGCountState α) : Prop :=
  (st.done = false → st.count = st.S.card * testCost T) ∧
    (st.done = true → st.count = (st.S.card + 1) * testCost T) ∧ I st.S

theorem sgq_done (f : Finset α → ℝ) (I : Finset α → Prop) (T : Finset α) (st : SGCountState α)
    (h : st.done = true) : sgQueryStep f I T st = st := by
  unfold sgQueryStep; rw [if_pos h]

theorem sgq_ne (f : Finset α → ℝ) (I : Finset α → Prop) (T : Finset α) (st : SGCountState α)
    (h : st.done = false) (hne : (cands f I T st.S).Nonempty) :
    sgQueryStep f I T st =
      ⟨insert (pick f st.S (cands f I T st.S) hne) st.S, st.count + testCost T, false⟩ := by
  unfold sgQueryStep; rw [if_neg (by rw [h]; exact Bool.false_ne_true), dif_pos hne]

theorem sgq_empty (f : Finset α → ℝ) (I : Finset α → Prop) (T : Finset α) (st : SGCountState α)
    (h : st.done = false) (hne : ¬ (cands f I T st.S).Nonempty) :
    sgQueryStep f I T st = ⟨st.S, st.count + testCost T, true⟩ := by
  unfold sgQueryStep; rw [if_neg (by rw [h]; exact Bool.false_ne_true), dif_neg hne]

theorem inv_step (f : Finset α → ℝ) (I : Finset α → Prop) (T : Finset α) (st : SGCountState α)
    (h : Inv f I T st) : Inv f I T (sgQueryStep f I T st) := by
  unfold Inv at h
  obtain ⟨hf1, ht1, hI1⟩ := h
  cases hd : st.done
  · have h1 := hf1 hd
    by_cases hne : (cands f I T st.S).Nonempty
    · have hx := pick_spec f st.S _ hne
      rw [sgq_ne f I T st hd hne]
      unfold Inv
      refine ⟨fun _ => ?_, fun h => absurd h (by simp), (mem_cands.1 hx.1).2.1⟩
      dsimp only
      rw [Finset.card_insert_of_notMem (not_mem_of_cands hx.1), h1]
      ring
    · rw [sgq_empty f I T st hd hne]
      unfold Inv
      refine ⟨fun h => absurd h (by simp), fun _ => ?_, hI1⟩
      dsimp only
      rw [h1]
      ring
  · rw [sgq_done f I T st hd]
    exact ⟨hf1, ht1, hI1⟩

theorem inv_iter (f : Finset α → ℝ) (I : Finset α → Prop) (T : Finset α) (hI0 : I ∅) (j : ℕ) :
    Inv f I T ((sgQueryStep f I T)^[j] ⟨∅, 0, false⟩) := by
  induction j with
  | zero => unfold Inv; simp [hI0]
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact inv_step f I T _ ih

theorem sgq_le (f : Finset α → ℝ) (I : Finset α → Prop) (T : Finset α) (hI0 : I ∅) :
    sgQueries f I T ≤ (maxIndepSize I + 1) * testCost T := by
  have h := inv_iter f I T hI0 (Fintype.card α + 1)
  unfold sgQueries
  generalize (sgQueryStep f I T)^[Fintype.card α + 1] ⟨∅, 0, false⟩ = st at h ⊢
  unfold Inv at h
  obtain ⟨h1, h2, h3⟩ := h
  have hk : st.S.card ≤ maxIndepSize I := by
    unfold maxIndepSize
    classical
    exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.2 ⟨Finset.mem_univ _, h3⟩)
  cases hd : st.done
  · rw [h1 hd]; exact Nat.mul_le_mul_right _ (by omega)
  · rw [h2 hd]; exact Nat.mul_le_mul_right _ (by omega)

theorem testCost_le (T : Finset α) : testCost T ≤ 3 * T.card := by
  unfold testCost
  split_ifs with h
  · simp
  · have := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 h); omega

end claims

end SubsamplingSM.Offline.SGP

open SubsamplingSM.Offline in
theorem solution {α : Type*} [Fintype α] [LinearOrder α]
    (p : ℕ) (hp : 1 ≤ p) (I : Finset α → Prop) (hI : IsPExtendible I p)
    (f : Finset α → ℝ) (hf : ∀ S, 0 ≤ f S) :
    (∀ T : Finset α, I (sampleGreedy f I T)) ∧
    (IsSubmodular f → ∀ O : Finset α, I O →
      f O ≤ (((p : ℝ) + 1) ^ 2 / (p : ℝ)) *
        expectSample (1 / ((p : ℝ) + 1)) (fun T => f (sampleGreedy f I T))) ∧
    (IsSubmodular f → IsMonotoneSetFn f → ∀ O : Finset α, I O →
      f O ≤ ((p : ℝ) + 1) *
        expectSample (1 / ((p : ℝ) + 1)) (fun T => f (sampleGreedy f I T))) ∧
    (IsLinearSetFn f → ∀ O : Finset α, I O →
      f O ≤ (p : ℝ) * expectSample (1 / (p : ℝ)) (fun T => f (sampleGreedy f I T))) ∧
    (∀ q ∈ ({1 / ((p : ℝ) + 1), 1 / (p : ℝ)} : Set ℝ),
      expectSample q (fun T => (sgQueries f I T : ℝ)) ≤
        6 * (Fintype.card α : ℝ) * ((max (maxIndepSize I) 1 : ℕ) : ℝ) / (p : ℝ)) := by
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.2 (by omega)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hI0 : I ∅ := hI.1.1
  have hf0 := hf ∅
  -- shared facts for q = 1/(p+1)
  have hqinv : ((p : ℝ) + 1) * (1 / ((p : ℝ) + 1)) = 1 := mul_one_div_cancel (by positivity)
  have hq0 : (0 : ℝ) ≤ 1 / ((p : ℝ) + 1) := by positivity
  have hqp : 1 - 1 / ((p : ℝ) + 1) = 1 / ((p : ℝ) + 1) * p := by
    linear_combination (-1 : ℝ) * hqinv
  have hq1 : 1 / ((p : ℝ) + 1) ≤ 1 := by
    have := mul_nonneg hq0 (le_of_lt hp0); linarith
  have hAtop : IsSubmodular f → ∀ O : Finset α, I O →
      SGP.E (1 / ((p : ℝ) + 1)) Finset.univ (fun T => f (SGP.G f I T ∅ ∪ O)) ≤
        ((p : ℝ) + 1) * SGP.E (1 / ((p : ℝ) + 1)) Finset.univ (fun T => f (SGP.G f I T ∅)) := by
    intro hsub O hO
    have hA := SGP.claimA f I p hsub hI hq0 hq1 hqp _ Finset.univ ∅ ∅ O rfl
      (Finset.disjoint_empty_left _) (Finset.empty_subset _) (Finset.subset_univ _)
      (by rw [Finset.empty_union]; exact hO)
    simp only [Finset.union_empty] at hA
    have := mul_nonneg (le_of_lt hp0) hf0
    linarith
  refine ⟨fun T => SGP.G_I f I T ∅ hI0, ?_, ?_, ?_, ?_⟩
  · intro hsub O hO
    have hA := hAtop hsub O hO
    have hsamp := SGP.sampling (Finset.univ.powerset) (SGP.w (1 / ((p : ℝ) + 1)) Finset.univ)
      (fun T _ => SGP.w_nonneg hq0 hq1 _ _)
      (by have := SGP.E_const (1 / ((p : ℝ) + 1)) (Finset.univ : Finset α) 1; simpa [SGP.E] using this)
      (fun X => f (X ∪ O)) (SGP.submod_union hsub O) (fun X => hf _) (1 / ((p : ℝ) + 1))
      Finset.univ (fun T => SGP.G f I T ∅) 0 (fun _ _ => Finset.subset_univ _) le_rfl hq0
      (fun v _ => Finset.sum_nonneg (fun T _ => mul_nonneg (SGP.w_nonneg hq0 hq1 _ _)
        (by split_ifs <;> norm_num)))
      (fun v _ => by
        refine le_trans ?_ (le_of_eq (SGP.E_ind (1 / ((p : ℝ) + 1)) (Finset.mem_univ v)))
        unfold SGP.E
        apply Finset.sum_le_sum
        intro T _
        beta_reduce
        apply mul_le_mul_of_nonneg_left _ (SGP.w_nonneg hq0 hq1 _ _)
        by_cases h1 : v ∈ SGP.G f I T ∅
        · have h2 : v ∈ T := by
            have := SGP.G_sub f I T ∅ h1; simpa using this
          rw [if_pos h1, if_pos h2]
        · rw [if_neg h1]; split_ifs <;> norm_num)
    have hEGO : (1 - 1 / ((p : ℝ) + 1)) * f O ≤
        SGP.E (1 / ((p : ℝ) + 1)) Finset.univ (fun T => f (SGP.G f I T ∅ ∪ O)) := by
      simpa [SGP.E] using hsamp
    rw [SGP.E_univ]
    simp only [SGP.sampleGreedy_eq]
    rw [hqp] at hEGO
    have key : 1 / ((p : ℝ) + 1) * p * f O ≤
        ((p : ℝ) + 1) * SGP.E (1 / ((p : ℝ) + 1)) Finset.univ (fun T => f (SGP.G f I T ∅)) := by
      linarith
    have key2 := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ (p : ℝ) + 1)
    have hid : ((p : ℝ) + 1) * (1 / ((p : ℝ) + 1) * p * f O) = p * f O := by
      linear_combination (p * f O) * hqinv
    rw [hid] at key2
    rw [div_mul_eq_mul_div, le_div_iff₀ hp0]
    nlinarith
  · intro hsub hmono O hO
    have hA := hAtop hsub O hO
    have hm := SGP.E_le hq0 hq1 Finset.univ (fun _ => f O) (fun T => f (SGP.G f I T ∅ ∪ O)) 0
      (fun T _ => by
        have := hmono O (SGP.G f I T ∅ ∪ O) Finset.subset_union_right
        linarith)
    rw [SGP.E_const] at hm
    rw [SGP.E_univ]
    simp only [SGP.sampleGreedy_eq]
    linarith
  · intro hlin O hO
    have hsub : IsSubmodular f := fun A B e h1 h2 => le_of_eq (hlin A B e h1 h2)
    have hqp' : 1 / (p : ℝ) * p = 1 := one_div_mul_cancel (ne_of_gt hp0)
    have hq0' : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
    have hq1' : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one hp0]; exact hp1
    have hB := SGP.claimB f I p hlin hI hq0' hq1' hqp' _ Finset.univ ∅ ∅ O rfl
      (Finset.disjoint_empty_left _) (Finset.empty_subset _) (Finset.subset_univ _)
      (by rw [Finset.empty_union]; exact hO)
    simp only [Finset.union_empty, Finset.empty_union] at hB
    rw [SGP.E_univ]
    simp only [SGP.sampleGreedy_eq]
    have := mul_nonneg (sub_nonneg.2 hp1) hf0
    linarith
  · intro q hq
    have hqb : 0 ≤ q ∧ q ≤ 1 ∧ q ≤ 1 / (p : ℝ) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl
      · exact ⟨hq0, hq1, one_div_le_one_div_of_le hp0 (by linarith)⟩
      · refine ⟨by positivity, ?_, le_rfl⟩
        rw [div_le_one hp0]; exact hp1
    obtain ⟨hq0q, hq1q, hqpq⟩ := hqb
    rw [SGP.E_univ]
    have hpt : ∀ T : Finset α, T ⊆ Finset.univ → (sgQueries f I T : ℝ) ≤
        ((6 * max (maxIndepSize I) 1 : ℕ) : ℝ) * (T.card : ℝ) + 0 := by
      intro T _
      have h1 := SGP.sgq_le f I T hI0
      have h2 := SGP.testCost_le T
      have h3 : maxIndepSize I + 1 ≤ 2 * max (maxIndepSize I) 1 := by
        have := le_max_left (maxIndepSize I) 1
        have := le_max_right (maxIndepSize I) 1
        omega
      have h4 : sgQueries f I T ≤ 6 * max (maxIndepSize I) 1 * T.card := by
        calc sgQueries f I T ≤ (maxIndepSize I + 1) * testCost T := h1
          _ ≤ (2 * max (maxIndepSize I) 1) * (3 * T.card) := Nat.mul_le_mul h3 h2
          _ = 6 * max (maxIndepSize I) 1 * T.card := by ring
      rw [add_zero]
      exact_mod_cast h4
    have hE := SGP.E_le hq0q hq1q Finset.univ (fun T => (sgQueries f I T : ℝ))
      (fun T => ((6 * max (maxIndepSize I) 1 : ℕ) : ℝ) * (T.card : ℝ)) 0 hpt
    rw [SGP.E_mul, SGP.E_card, add_zero, Finset.card_univ] at hE
    have hn : (0 : ℝ) ≤ 6 * (Fintype.card α : ℝ) * ((max (maxIndepSize I) 1 : ℕ) : ℝ) := by
      positivity
    calc SGP.E q Finset.univ (fun T => (sgQueries f I T : ℝ))
        ≤ ((6 * max (maxIndepSize I) 1 : ℕ) : ℝ) * (q * (Fintype.card α : ℝ)) := hE
      _ = (6 * (Fintype.card α : ℝ) * ((max (maxIndepSize I) 1 : ℕ) : ℝ)) * q := by
          push_cast; ring
      _ ≤ (6 * (Fintype.card α : ℝ) * ((max (maxIndepSize I) 1 : ℕ) : ℝ)) * (1 / (p : ℝ)) :=
          mul_le_mul_of_nonneg_left hqpq hn
      _ = 6 * (Fintype.card α : ℝ) * ((max (maxIndepSize I) 1 : ℕ) : ℝ) / (p : ℝ) := by ring
