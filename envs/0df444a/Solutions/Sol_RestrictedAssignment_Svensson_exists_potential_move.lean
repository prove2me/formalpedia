-- Prove2me | solution 1 for RestrictedAssignment.Svensson.exists_potential_move
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:48:50.61695+00:00
-- url     : https://prove2.me/submissions/30519276-34e6-4ff4-b8b1-f15f5384c1ea

import Mathlib
import Definitions.Def_RestrictedAssignment_Svensson_configLP
import Definitions.Def_RestrictedAssignment_Svensson_extendSchedule

namespace RestrictedAssignment.Svensson

open Finset Classical

set_option linter.unusedSectionVars false

variable {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]

noncomputable def aux_ep_zeta (p : J → ℝ) (j : J) : ℝ :=
  if IsBig p j then 11/17 else if IsMedium p j then 9/17 else p j

noncomputable def aux_ep_Z (p : J → ℝ) (σ : J → Option M) (i : M) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => σ j = some i), aux_ep_zeta p j

theorem aux_ep_split (p : J → ℝ) (L : Finset J) (f : J → ℝ) :
    ∑ j ∈ L, f j = ∑ j ∈ L.filter (IsBig p), f j + ∑ j ∈ L.filter (IsMedium p), f j
      + ∑ j ∈ L.filter (IsSmall p), f j := by
  rw [← Finset.sum_filter_add_sum_filter_not L (IsBig p)]
  rw [← Finset.sum_filter_add_sum_filter_not (L.filter (fun j => ¬ IsBig p j)) (IsMedium p)]
  rw [Finset.filter_filter, Finset.filter_filter]
  have h1 : L.filter (fun j => ¬ IsBig p j ∧ IsMedium p j) = L.filter (IsMedium p) := by
    apply Finset.filter_congr
    intro j _
    simp only [IsBig, IsMedium, not_le]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨h.2, h⟩
  have h2 : L.filter (fun j => ¬ IsBig p j ∧ ¬ IsMedium p j) = L.filter (IsSmall p) := by
    apply Finset.filter_congr
    intro j _
    simp only [IsBig, IsMedium, IsSmall, not_le, not_and, not_lt]
    constructor
    · rintro ⟨h1, h2⟩
      by_contra h
      push_neg at h
      linarith [h2 h]
    · intro h
      exact ⟨by linarith, fun h' => by linarith⟩
  rw [h1, h2]; ring

theorem aux_ep_data (p : J → ℝ) (L : Finset J) (hp1 : ∀ j ∈ L, p j ≤ 1) :
    ∑ j ∈ L, aux_ep_zeta p j = 11/17 * ((L.filter (IsBig p)).card : ℝ)
        + 9/17 * ((L.filter (IsMedium p)).card : ℝ) + ∑ j ∈ L.filter (IsSmall p), p j ∧
    ∑ j ∈ L, p j ≤ ((L.filter (IsBig p)).card : ℝ)
        + 11/17 * ((L.filter (IsMedium p)).card : ℝ) + ∑ j ∈ L.filter (IsSmall p), p j := by
  constructor
  · rw [aux_ep_split p L]
    have e1 : ∑ j ∈ L.filter (IsBig p), aux_ep_zeta p j = ∑ j ∈ L.filter (IsBig p), (11/17 : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_filter] at hj
      simp [aux_ep_zeta, hj.2]
    have e2 : ∑ j ∈ L.filter (IsMedium p), aux_ep_zeta p j
        = ∑ j ∈ L.filter (IsMedium p), (9/17 : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_filter] at hj
      have : ¬ IsBig p j := by unfold IsBig IsMedium at *; linarith [hj.2.2]
      simp [aux_ep_zeta, hj.2, this]
    have e3 : ∑ j ∈ L.filter (IsSmall p), aux_ep_zeta p j = ∑ j ∈ L.filter (IsSmall p), p j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_filter] at hj
      have h1 : ¬ IsBig p j := by unfold IsBig IsSmall at *; linarith [hj.2]
      have h2 : ¬ IsMedium p j := by unfold IsMedium IsSmall at *; intro h; linarith [hj.2, h.1]
      simp [aux_ep_zeta, h1, h2]
    rw [e1, e2, e3, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    ring
  · rw [aux_ep_split p L]
    have e1 : ∑ j ∈ L.filter (IsBig p), p j ≤ ∑ j ∈ L.filter (IsBig p), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [Finset.mem_filter] at hj
      exact hp1 j hj.1
    have e2 : ∑ j ∈ L.filter (IsMedium p), p j ≤ ∑ j ∈ L.filter (IsMedium p), (11/17 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [Finset.mem_filter] at hj
      unfold IsMedium at hj
      linarith [hj.2.2]
    rw [Finset.sum_const, nsmul_eq_mul] at e1 e2
    linarith

theorem aux_ep_num1 (a b : ℕ) (Pb Pm Ps q Z : ℝ) (ha : a ≤ 1) (hPb : Pb ≤ a)
    (hPm : Pm ≤ 11/17 * b) (hPs : 0 ≤ Ps) (hload : 33/17 < Pb + Pm + Ps + q) (hq : q ≤ 9/17)
    (hZ : Z = 11/17 * a + 9/17 * b + Ps) :
    18/17 < Z ∧ (q < 7/17 → 20/17 ≤ Z) := by
  subst hZ
  interval_cases a
  · rcases b with _ | _ | _ | b
    · push_cast at *; constructor <;> intros <;> linarith
    · push_cast at *; constructor <;> intros <;> linarith
    · push_cast at *; constructor <;> intros <;> linarith
    · push_cast at *
      have : (0:ℝ) ≤ b := by positivity
      constructor <;> intros <;> linarith
  · rcases b with _ | b
    · push_cast at *; constructor <;> intros <;> linarith
    · push_cast at *
      have : (0:ℝ) ≤ b := by positivity
      constructor <;> intros <;> linarith

theorem aux_ep_num2 (b : ℕ) (Pm Ps q Z : ℝ)
    (hPm : Pm ≤ 11/17 * b) (hPs : 0 ≤ Ps) (hload : 33/17 < Pm + Ps + q) (hq : q < 14/17)
    (hZ : Z = 9/17 * b + Ps) : 1 < Z := by
  subst hZ
  rcases b with _ | _ | b
  · push_cast at *; linarith
  · push_cast at *; linarith
  · push_cast at *
    have : (0:ℝ) ≤ b := by positivity
    linarith

theorem aux_ep_num3 (b : ℕ) (Pm Ps pj Z : ℝ) (hpj : 0 ≤ pj)
    (hPm : Pm ≤ 11/17 * b) (hPs : pj ≤ Ps) (hload : 16/17 < Pm + Ps)
    (hZ : Z = 9/17 * b + Ps) : 14/17 < Z ∧ (16/17 < Z ∨ 9/17 + pj ≤ Z) := by
  subst hZ
  rcases b with _ | _ | b
  · push_cast at *; exact ⟨by linarith, Or.inl (by linarith)⟩
  · push_cast at *; exact ⟨by linarith, Or.inr (by linarith)⟩
  · push_cast at *
    have : (0:ℝ) ≤ b := by positivity
    exact ⟨by linarith, Or.inl (by linarith)⟩

theorem aux_ep_p_le_one (Γ : J → Finset M) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hLP : CLPFeasible Γ p 1) (j : J) : p j ≤ 1 := by
  by_contra h
  push_neg at h
  obtain ⟨x, hx0, hx1, hx2⟩ := hLP
  have h3 := hx2 j
  have h0 : ∑ i, ∑ C ∈ (configs Γ p 1 i).filter (fun C => j ∈ C), x i C = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro C hC
    exfalso
    rw [Finset.mem_filter] at hC
    have hC1 := hC.1
    simp only [configs, Finset.mem_filter, Finset.mem_univ, true_and] at hC1
    have : p j ≤ ∑ k ∈ C, p k := Finset.single_le_sum (fun k _ => hp k) hC.2
    linarith [hC1.2]
  linarith

theorem aux_ep_Γ_nonempty (Γ : J → Finset M) (p : J → ℝ) (hLP : CLPFeasible Γ p 1) (j : J) :
    (Γ j).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  obtain ⟨x, hx0, hx1, hx2⟩ := hLP
  have h3 := hx2 j
  have h0 : ∑ i, ∑ C ∈ (configs Γ p 1 i).filter (fun C => j ∈ C), x i C = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro C hC
    exfalso
    rw [Finset.mem_filter] at hC
    have hC1 := hC.1
    simp only [configs, Finset.mem_filter, Finset.mem_univ, true_and] at hC1
    have := hC1.1 j hC.2
    rw [h] at this
    simp at this
  linarith

theorem aux_ep_pload_nonneg (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (σ : J → Option M) (i : M) :
    0 ≤ pload p σ i :=
  Finset.sum_nonneg (fun j _ => hp j)

theorem aux_ep_pload_update (p : J → ℝ) (σ : J → Option M) (j : J) (i : M) (hne : σ j ≠ some i) :
    pload p (Function.update σ j (some i)) i = pload p σ i + p j := by
  unfold pload
  have : Finset.univ.filter (fun x => Function.update σ j (some i) x = some i)
      = insert j (Finset.univ.filter (fun x => σ x = some i)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases hxj : x = j
    · subst hxj; simp
    · rw [Function.update_of_ne hxj]; simp [hxj]
  rw [this, Finset.sum_insert (by simp [hne])]; ring

theorem aux_ep_pload_update_ne (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (σ : J → Option M) (j : J)
    (i i' : M) (hii : i' ≠ i) :
    pload p (Function.update σ j (some i)) i' ≤ pload p σ i' := by
  unfold pload
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    by_cases hxj : x = j
    · subst hxj; simp at hx; exact absurd hx.symm hii
    · rwa [Function.update_of_ne hxj] at hx
  · intro x _ _; exact hp x

theorem aux_ep_valid_update (Γ : J → Finset M) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j)
    (σ : J → Option M) (hσ : Valid Γ p σ) (j : J) (i : M)
    (hi : i ∈ Γ j) (hne : σ j ≠ some i)
    (hbig : ¬ IsBig p j ∨ ¬ (∃ j', σ j' = some i ∧ IsBig p j'))
    (hload : pload p σ i + p j ≤ 1 + R) : Valid Γ p (Function.update σ j (some i)) := by
  obtain ⟨h1, h2⟩ := hσ
  refine ⟨?_, ?_⟩
  · intro j' i' h
    by_cases hj : j' = j
    · subst hj; simp at h; subst h; exact hi
    · rw [Function.update_of_ne hj] at h; exact h1 j' i' h
  · intro i'
    constructor
    · by_cases hii : i' = i
      · subst hii
        rcases hbig with hb | hb
        · calc _ ≤ (Finset.univ.filter (fun j' => σ j' = some i' ∧ IsBig p j')).card := by
                apply Finset.card_le_card
                intro x hx
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
                by_cases hxj : x = j
                · subst hxj; exact absurd hx.2 hb
                · rw [Function.update_of_ne hxj] at hx; exact hx
            _ ≤ 1 := (h2 i').1
        · calc _ ≤ ({j} : Finset J).card := by
                apply Finset.card_le_card
                intro x hx
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
                by_cases hxj : x = j
                · simp [hxj]
                · rw [Function.update_of_ne hxj] at hx; exact absurd ⟨x, hx⟩ hb
            _ = 1 := Finset.card_singleton j
      · calc _ ≤ (Finset.univ.filter (fun j' => σ j' = some i' ∧ IsBig p j')).card := by
              apply Finset.card_le_card
              intro x hx
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
              by_cases hxj : x = j
              · subst hxj; simp at hx; exact absurd hx.1.symm hii
              · rw [Function.update_of_ne hxj] at hx; exact hx
          _ ≤ 1 := (h2 i').1
    · by_cases hii : i' = i
      · subst hii; rw [aux_ep_pload_update p σ j i' hne]; linarith
      · exact (aux_ep_pload_update_ne p hp σ j i i' hii).trans (h2 i').2

theorem aux_ep_val_small_le (Γ : J → Finset M) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j)
    (s : AlgState J M) (j : J) (i : M) (h : IsPotentialMoveOf Γ p s j i .small) :
    moveVal Γ p s j i ≤ toLex (p j, pload p s.σ i) := by
  by_cases hv : IsValidMove Γ p s j i
  · rw [moveVal, if_pos hv, Prod.Lex.toLex_le_toLex]
    rcases (hp j).lt_or_eq with h' | h'
    · left; exact h'
    · right; exact ⟨h', aux_ep_pload_nonneg p hp s.σ i⟩
  · rw [moveVal, if_neg hv, if_pos h]

theorem aux_ep_val_lt2 (Γ : J → Finset M) (p : J → ℝ) (s : AlgState J M) (j : J) (i : M)
    (hpm : IsPotentialMove Γ p s j i) (hv : ¬ IsValidMove Γ p s j i)
    (a b : ℝ) (hle : moveVal Γ p s j i ≤ toLex (a, b)) (ha : a < 2) :
    IsPotentialMoveOf Γ p s j i .small ∧ p j ≤ a := by
  rw [moveVal, if_neg hv] at hle
  by_cases h1 : IsPotentialMoveOf Γ p s j i .small
  · rw [if_pos h1, Prod.Lex.toLex_le_toLex] at hle
    refine ⟨h1, ?_⟩
    rcases hle with h | h
    · exact h.le
    · exact h.1.le
  · exfalso
    rw [if_neg h1] at hle
    by_cases h2 : IsPotentialMoveOf Γ p s j i .medLargeToBig
    · rw [if_pos h2, Prod.Lex.toLex_le_toLex] at hle
      rcases hle with h | ⟨h, _⟩ <;> dsimp only at h <;> linarith
    rw [if_neg h2] at hle
    by_cases h3 : IsPotentialMoveOf Γ p s j i .hugeToSmall
    · rw [if_pos h3, Prod.Lex.toLex_le_toLex] at hle
      rcases hle with h | ⟨h, _⟩ <;> dsimp only at h <;> linarith
    rw [if_neg h3] at hle
    by_cases h4 : IsPotentialMoveOf Γ p s j i .hugeToBig
    · rw [if_pos h4, Prod.Lex.toLex_le_toLex] at hle
      rcases hle with h | ⟨h, _⟩ <;> dsimp only at h <;> linarith
    rw [if_neg h4] at hle
    by_cases h5 : IsPotentialMoveOf Γ p s j i .hugeToMedium
    · rw [if_pos h5, Prod.Lex.toLex_le_toLex] at hle
      rcases hle with h | ⟨h, _⟩ <;> dsimp only at h <;> linarith
    obtain ⟨t, ht⟩ := hpm
    cases t <;> contradiction

theorem aux_ep_decomp_append {α : Type} (T T1 T2 : List α) (N B : α)
    (h : T ++ [N] = T1 ++ B :: T2) :
    (T1 = T ∧ B = N ∧ T2 = []) ∨ (∃ T2', T2 = T2' ++ [N] ∧ T = T1 ++ B :: T2') := by
  rcases List.eq_nil_or_concat T2 with h2 | ⟨L, b, h2⟩
  · subst h2
    left
    have := List.append_inj' h rfl
    simp only [List.cons.injEq, and_true] at this
    exact ⟨this.1.symm, this.2.symm, rfl⟩
  · subst h2
    right
    refine ⟨L, ?_, ?_⟩
    · have hh : T ++ [N] = (T1 ++ B :: L) ++ [b] := by rw [h]; simp
      have := List.append_inj' hh rfl
      simp only [List.cons.injEq, and_true] at this
      rw [this.2]; simp
    · have hh : T ++ [N] = (T1 ++ B :: L) ++ [b] := by rw [h]; simp
      exact (List.append_inj' hh rfl).1

theorem aux_ep_decomp_take {α : Type} (T T1 T2 : List α) (B : α) (k : ℕ)
    (h : T.take k = T1 ++ B :: T2) : T = T1 ++ B :: (T2 ++ T.drop k) := by
  conv_lhs => rw [← List.take_append_drop k T]
  rw [h]; simp

theorem aux_ep_decomp_idx {α : Type} (T : List α) (k : ℕ) (hk : k < T.length) :
    T = T.take k ++ T[k] :: T.drop (k+1) := by
  conv_lhs => rw [← List.take_append_drop k T]
  rw [List.drop_eq_getElem_cons hk]

def aux_ep_S1 (p : J → ℝ) (σ : J → Option M) (i : M) (q : ℝ) : Prop :=
  q ≤ 9/17 ∧ 18/17 < aux_ep_Z p σ i ∧ (q < 7/17 → 20/17 ≤ aux_ep_Z p σ i)

def aux_ep_S3 (Γ : J → Finset M) (p : J → ℝ) (σ : J → Option M) (Tpre : List (Blocker J M))
    (i : M) (T2 : List (Blocker J M)) : Prop :=
  ∃ j' i', σ j' = some i ∧ IsSmall p j' ∧ i' ∈ Γ j' ∧ σ j' ≠ some i' ∧
    ¬ InMS (⟨σ, Tpre⟩ : AlgState J M) i' ∧
    14/17 < aux_ep_Z p σ i ∧ (16/17 < aux_ep_Z p σ i ∨ 9/17 + p j' ≤ aux_ep_Z p σ i) ∧
    ∀ B' T3, T2 = B' :: T3 → B'.kind = BlockerKind.small ∧
      ∃ i₂, B'.machine = some i₂ ∧ ∃ q ≤ p j', aux_ep_S1 p σ i₂ q

def aux_ep_root (jnew : J) : Blocker J M := ⟨{jnew}, none, BlockerKind.small⟩

structure aux_ep_Inv (Γ : J → Finset M) (p : J → ℝ) (jnew : J) (s : AlgState J M) : Prop where
  valid : Valid Γ p s.σ
  root : ∃ T', s.T = aux_ep_root jnew :: T' ∧ ∀ B ∈ T', ∃ i, B.machine = some i
  disj : s.T.Pairwise (fun B B' => Disjoint B.jobs B'.jobs)
  mach : ∀ B ∈ s.T, ∀ i, B.machine = some i → ∀ j ∈ B.jobs, s.σ j = some i
  big : ∀ B ∈ s.T, B.kind = BlockerKind.big → B.jobs.Nonempty ∧ ∀ j ∈ B.jobs, IsBig p j
  med : ∀ T1 B T2, s.T = T1 ++ B :: T2 → B.kind = BlockerKind.medium →
      B.jobs.Nonempty ∧ (∀ j ∈ B.jobs, IsMedium p j) ∧
      ∀ i, B.machine = some i → R < ∑ k ∈ Si Γ p ⟨s.σ, T1⟩ i ∪ B.jobs, p k
  small : ∀ T1 B T2, s.T = T1 ++ B :: T2 → B.kind = BlockerKind.small → ∀ i, B.machine = some i →
      (∀ j, s.σ j = some i → ∃ B' ∈ T1 ++ [B], j ∈ B'.jobs) ∧
      ¬ InMS (⟨s.σ, T1⟩ : AlgState J M) i ∧
      (1 < aux_ep_Z p s.σ i ∨ aux_ep_S3 Γ p s.σ (T1 ++ [B]) i T2)

theorem aux_ep_pm_facts (Γ : J → Finset M) (p : J → ℝ) (s : AlgState J M) (j : J) (i : M)
    (h : IsPotentialMove Γ p s j i) : InJT s j ∧ IsMove Γ s j i ∧ ¬ InMS s i := by
  obtain ⟨t, ht⟩ := h
  have hMT : ¬ InMT s i → ¬ InMS s i := fun h1 ⟨B, hB, _, hBm⟩ => h1 ⟨B, hB, hBm⟩
  cases t with
  | small =>
    obtain ⟨h1, h2, h3⟩ := ht
    refine ⟨h1, h2, ?_⟩
    rcases h3 with ⟨_, h⟩ | ⟨_, h, _⟩ | ⟨_, _, h, _⟩
    · exact h
    · exact hMT h
    · exact h
  | medLargeToBig =>
    obtain ⟨h1, h2, h3, _⟩ := ht
    refine ⟨h1, h2, ?_⟩
    rcases h3 with ⟨_, h⟩ | ⟨_, _, h⟩
    · exact hMT h
    · exact h
  | hugeToSmall => obtain ⟨h1, h2, _, h, _⟩ := ht; exact ⟨h1, h2, hMT h⟩
  | hugeToBig => obtain ⟨h1, h2, _, h, _⟩ := ht; exact ⟨h1, h2, hMT h⟩
  | hugeToMedium => obtain ⟨h1, h2, _, h, _⟩ := ht; exact ⟨h1, h2, hMT h⟩

theorem aux_ep_ms_mono (σ σ' : J → Option M) (T T' : List (Blocker J M))
    (h : ∀ B ∈ T, B ∈ T') (i : M) :
    InMS (⟨σ, T⟩ : AlgState J M) i → InMS (⟨σ', T'⟩ : AlgState J M) i :=
  fun ⟨B, hB, h1, h2⟩ => ⟨B, h B hB, h1, h2⟩

theorem aux_ep_jt_mono (σ σ' : J → Option M) (T T' : List (Blocker J M))
    (h : ∀ B ∈ T, B ∈ T') (j : J) :
    InJT (⟨σ, T⟩ : AlgState J M) j → InJT (⟨σ', T'⟩ : AlgState J M) j :=
  fun ⟨B, hB, h1⟩ => ⟨B, h B hB, h1⟩

theorem aux_ep_jobmach (Γ : J → Finset M) (p : J → ℝ) (jnew : J) (s : AlgState J M)
    (hI : aux_ep_Inv Γ p jnew s) (hnone : s.σ jnew = none) (B : Blocker J M) (hB : B ∈ s.T)
    (j : J) (hj : j ∈ B.jobs) (i : M) (hσ : s.σ j = some i) : B.machine = some i := by
  obtain ⟨T0, hT0, hT0m⟩ := hI.root
  have hB' := hB
  rw [hT0] at hB'
  rcases List.mem_cons.mp hB' with h | h
  · subst h
    simp only [aux_ep_root, Finset.mem_singleton] at hj
    subst hj
    rw [hnone] at hσ
    cases hσ
  · obtain ⟨i', hi'⟩ := hT0m B h
    have := hI.mach B hB i' hi' j hj
    rw [hσ, Option.some.injEq] at this
    rw [hi', this]

theorem aux_ep_not_S (Γ : J → Finset M) (p : J → ℝ) (σ : J → Option M)
    (T T1 : List (Blocker J M)) (hT1 : ∀ B ∈ T1, B ∈ T) (j : J) (i : M)
    (hmv : IsMove Γ (⟨σ, T⟩ : AlgState J M) j i) (hms : ¬ InMS (⟨σ, T⟩ : AlgState J M) i) :
    ¬ InS Γ p (⟨σ, T1⟩ : AlgState J M) j := by
  intro h
  exact hms (aux_ep_ms_mono σ σ T1 T hT1 i (h.2 i hmv))

theorem aux_ep_inv_init (Γ : J → Finset M) (p : J → ℝ) (σ0 : J → Option M) (jnew : J)
    (hσ0 : Valid Γ p σ0) : aux_ep_Inv Γ p jnew (initState σ0 jnew) := by
  have hmem : ∀ T1 B T2, (initState σ0 jnew).T = T1 ++ B :: T2 → B = aux_ep_root jnew := by
    intro T1 B T2 h
    have : B ∈ (initState σ0 jnew).T := by rw [h]; simp
    simpa [initState, aux_ep_root] using this
  refine ⟨hσ0, ⟨[], rfl, by simp⟩, by simp [initState], ?_, ?_, ?_, ?_⟩
  · intro B hB i hi
    simp only [initState, List.mem_singleton] at hB
    subst hB; cases hi
  · intro B hB hk
    simp only [initState, List.mem_singleton] at hB
    subst hB; cases hk
  · intro T1 B T2 h hk
    rw [hmem T1 B T2 h] at hk; cases hk
  · intro T1 B T2 h _ i hi
    rw [hmem T1 B T2 h] at hi; cases hi


theorem aux_ep_pres_valid (Γ : J → Finset M) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (jnew : J)
    (σ : J → Option M) (T : List (Blocker J M))
    (hI : aux_ep_Inv Γ p jnew ⟨σ, T⟩) (hnone : σ jnew = none)
    (j : J) (i : M) (hpm : IsPotentialMove Γ p ⟨σ, T⟩ j i)
    (hv : IsValidMove Γ p ⟨σ, T⟩ j i) (k : ℕ) (hk : k < T.length)
    (hjk : j ∈ (T[k]).jobs) (hloop : Function.update σ j (some i) jnew = none) :
    aux_ep_Inv Γ p jnew ⟨Function.update σ j (some i), T.take k⟩ := by
  set σ' := Function.update σ j (some i) with hσ'
  obtain ⟨hJT, hmv, hms⟩ := aux_ep_pm_facts Γ p _ j i hpm
  obtain ⟨T0, hT0, hT0m⟩ := hI.root
  dsimp only at hT0
  have hjne : j ≠ jnew := by
    rintro rfl
    simp [hσ'] at hloop
  -- j is not in any remaining blocker
  have hf2 : ∀ B ∈ T.take k, j ∉ B.jobs := by
    have hdisj := hI.disj
    dsimp only at hdisj
    rw [← List.take_append_drop k T, List.pairwise_append] at hdisj
    have hmemd : T[k] ∈ T.drop k := by
      rw [List.drop_eq_getElem_cons hk]; exact List.mem_cons_self
    intro B hB hjB
    exact Finset.disjoint_left.mp (hdisj.2.2 B hB _ hmemd) hjB hjk
  have hsub : ∀ B ∈ T.take k, B ∈ T := fun B hB => List.mem_of_mem_take hB
  -- k ≥ 1
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := by
    rcases k with _ | k'
    · exfalso
      have : T[0] = aux_ep_root jnew := by simp [hT0]
      rw [this] at hjk
      simp [aux_ep_root] at hjk
      exact hjne hjk
    · exact ⟨k', rfl⟩
  have hσ'ne : ∀ x, x ≠ j → σ' x = σ x := fun x hx => Function.update_of_ne hx _ _
  -- machines of remaining small blockers keep their job sets
  have hf4 : ∀ B ∈ T.take (k'+1), B.kind = BlockerKind.small → ∀ i₂, B.machine = some i₂ →
      ∀ x, σ' x = some i₂ ↔ σ x = some i₂ := by
    intro B hB hBk i₂ hBm x
    by_cases hx : x = j
    · subst hx
      have hii : i ≠ i₂ := by
        rintro rfl
        exact hms ⟨B, hsub B hB, hBk, hBm⟩
      obtain ⟨T1, T2, hdec⟩ := List.append_of_mem hB
      have hT := aux_ep_decomp_take T T1 T2 B (k'+1) hdec
      have ha := (hI.small T1 B _ hT hBk i₂ hBm).1
      simp only [hσ', Function.update_self, Option.some.injEq]
      constructor
      · intro h; exact absurd h hii
      · intro h
        obtain ⟨B', hB', hxB'⟩ := ha x h
        have : B' ∈ T.take (k'+1) := by
          rw [hdec]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hB' ⊢
          rcases hB' with h' | h'
          · left; exact h'
          · right; left; exact h'
        exact absurd hxB' (hf2 B' this)
    · rw [hσ'ne x hx]
  have hZ : ∀ B ∈ T.take (k'+1), B.kind = BlockerKind.small → ∀ i₂, B.machine = some i₂ →
      aux_ep_Z p σ' i₂ = aux_ep_Z p σ i₂ := by
    intro B hB hBk i₂ hBm
    unfold aux_ep_Z
    exact Finset.sum_congr (Finset.filter_congr (fun x _ => hf4 B hB hBk i₂ hBm x)) (fun _ _ => rfl)
  refine ⟨hv.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨T0.take k', ?_, ?_⟩
    · rw [hT0, List.take_succ_cons]
    · intro B hB; exact hT0m B (List.mem_of_mem_take hB)
  · exact List.Pairwise.sublist (List.take_sublist _ _) hI.disj
  · intro B hB i₂ hBm x hx
    dsimp only at hB ⊢
    have hxj : x ≠ j := fun h => hf2 B hB (h ▸ hx)
    rw [hσ'ne x hxj]
    exact hI.mach B (hsub B hB) i₂ hBm x hx
  · intro B hB hBk
    exact hI.big B (hsub B hB) hBk
  · intro T1 B T2 hdec hBk
    dsimp only at hdec
    have hT := aux_ep_decomp_take T T1 T2 B (k'+1) hdec
    obtain ⟨h1, h2, h3⟩ := hI.med T1 B _ hT hBk
    refine ⟨h1, h2, ?_⟩
    intro i₂ hBm
    have h3' := h3 i₂ hBm
    have hT1 : ∀ B' ∈ T1, B' ∈ T := by
      intro B' hB'; rw [hT]; exact List.mem_append_left _ hB'
    have hsubS : Si Γ p ⟨σ, T1⟩ i₂ ∪ B.jobs ⊆ Si Γ p ⟨σ', T1⟩ i₂ ∪ B.jobs := by
      apply Finset.union_subset_union _ (subset_refl _)
      intro x hx
      simp only [Si, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      have hxj : x ≠ j := by
        rintro rfl
        exact aux_ep_not_S Γ p σ T T1 hT1 x i hmv hms hx.2
      refine ⟨by rw [hσ'ne x hxj]; exact hx.1, hx.2.1, ?_⟩
      intro i' hmv'
      apply hx.2.2 i'
      refine ⟨hmv'.1, ?_⟩
      have := hmv'.2
      dsimp only at this ⊢
      rwa [hσ'ne x hxj] at this
    calc R < _ := h3'
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsubS (fun x _ _ => hp x)
  · intro T1 B T2 hdec hBk i₂ hBm
    dsimp only at hdec ⊢
    have hT := aux_ep_decomp_take T T1 T2 B (k'+1) hdec
    have hBmem : B ∈ T.take (k'+1) := by rw [hdec]; simp
    obtain ⟨ha, hb, hc⟩ := hI.small T1 B _ hT hBk i₂ hBm
    have hpre : ∀ B' ∈ T1 ++ [B], B' ∈ T.take (k'+1) := by
      intro B' hB'
      rw [hdec]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hB' ⊢
      rcases hB' with h' | h'
      · left; exact h'
      · right; left; exact h'
    refine ⟨?_, hb, ?_⟩
    · intro x hx
      exact ha x ((hf4 B hBmem hBk i₂ hBm x).mp hx)
    · rcases hc with hc | ⟨j', i', h1, h2, h3, h4, h5, h6, h7, h8⟩
      · left; rw [hZ B hBmem hBk i₂ hBm]; exact hc
      · right
        have hj'j : j' ≠ j := by
          rintro rfl
          obtain ⟨B', hB', hjB'⟩ := ha _ h1
          exact hf2 B' (hpre B' hB') hjB'
        refine ⟨j', i', (hf4 B hBmem hBk i₂ hBm j').mpr h1, h2, h3, by rw [hσ'ne j' hj'j]; exact h4,
          h5, by rw [hZ B hBmem hBk i₂ hBm]; exact h6, by rw [hZ B hBmem hBk i₂ hBm]; exact h7, ?_⟩
        intro B' T3 hT3
        obtain ⟨g1, i₃, g2, q, g3, g4, g5, g6⟩ := h8 B' (T3 ++ T.drop (k'+1)) (by rw [hT3]; rfl)
        have hB'mem : B' ∈ T.take (k'+1) := by rw [hdec, hT3]; simp
        refine ⟨g1, i₃, g2, q, g3, g4, ?_, ?_⟩
        · rw [hZ B' hB'mem g1 i₃ g2]; exact g5
        · rw [hZ B' hB'mem g1 i₃ g2]; exact g6

theorem aux_ep_pres_append (Γ : J → Finset M) (p : J → ℝ) (jnew : J)
    (σ : J → Option M) (T : List (Blocker J M))
    (hI : aux_ep_Inv Γ p jnew ⟨σ, T⟩) (N : Blocker J M) (i : M)
    (hNm : N.machine = some i) (hNj : ∀ j ∈ N.jobs, σ j = some i)
    (hNd : ∀ B ∈ T, Disjoint B.jobs N.jobs)
    (hNb : N.kind = BlockerKind.big → N.jobs.Nonempty ∧ ∀ j ∈ N.jobs, IsBig p j)
    (hNmed : N.kind = BlockerKind.medium → N.jobs.Nonempty ∧ (∀ j ∈ N.jobs, IsMedium p j) ∧
      R < ∑ k ∈ Si Γ p ⟨σ, T⟩ i ∪ N.jobs, p k)
    (hNs : N.kind = BlockerKind.small →
      (∀ j, σ j = some i → ∃ B' ∈ T ++ [N], j ∈ B'.jobs) ∧ ¬ InMS (⟨σ, T⟩ : AlgState J M) i ∧
      (1 < aux_ep_Z p σ i ∨ aux_ep_S3 Γ p σ (T ++ [N]) i []))
    (hsucc : ∀ j' i', IsPotentialMoveOf Γ p ⟨σ, T⟩ j' i' .small → IsSmall p j' →
      N.kind = BlockerKind.small ∧ ∃ i₂, N.machine = some i₂ ∧ ∃ q ≤ p j', aux_ep_S1 p σ i₂ q) :
    aux_ep_Inv Γ p jnew ⟨σ, T ++ [N]⟩ := by
  obtain ⟨T0, hT0, hT0m⟩ := hI.root
  dsimp only at hT0
  have hmemT : ∀ B ∈ T, B ∈ T ++ [N] := fun B hB => List.mem_append_left _ hB
  refine ⟨hI.valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨T0 ++ [N], by dsimp only; rw [hT0]; rfl, ?_⟩
    intro B hB
    rcases List.mem_append.mp hB with h | h
    · exact hT0m B h
    · rw [List.mem_singleton] at h; subst h; exact ⟨i, hNm⟩
  · dsimp only
    rw [List.pairwise_append]
    refine ⟨hI.disj, List.pairwise_singleton _ _, ?_⟩
    intro B hB B' hB'
    rw [List.mem_singleton] at hB'; subst hB'
    exact hNd B hB
  · intro B hB i₂ hBm x hx
    dsimp only at hB ⊢
    rcases List.mem_append.mp hB with h | h
    · exact hI.mach B h i₂ hBm x hx
    · rw [List.mem_singleton] at h; subst h
      rw [hNm, Option.some.injEq] at hBm; subst hBm
      exact hNj x hx
  · intro B hB hBk
    dsimp only at hB
    rcases List.mem_append.mp hB with h | h
    · exact hI.big B h hBk
    · rw [List.mem_singleton] at h; subst h; exact hNb hBk
  · intro T1 B T2 hdec hBk
    dsimp only at hdec ⊢
    rcases aux_ep_decomp_append T T1 T2 N B hdec with ⟨h1, h2, h3⟩ | ⟨T2', h1, h2⟩
    · subst h1 h2 h3
      obtain ⟨g1, g2, g3⟩ := hNmed hBk
      refine ⟨g1, g2, ?_⟩
      intro i₂ hBm
      rw [hNm, Option.some.injEq] at hBm; subst hBm
      exact g3
    · exact hI.med T1 B T2' h2 hBk
  · intro T1 B T2 hdec hBk i₂ hBm
    dsimp only at hdec ⊢
    rcases aux_ep_decomp_append T T1 T2 N B hdec with ⟨h1, h2, h3⟩ | ⟨T2', h1, h2⟩
    · subst h1 h2 h3
      rw [hNm, Option.some.injEq] at hBm; subst hBm
      exact hNs hBk
    · obtain ⟨ha, hb, hc⟩ := hI.small T1 B T2' h2 hBk i₂ hBm
      refine ⟨ha, hb, ?_⟩
      rcases hc with hc | ⟨j', i', g1, g2, g3, g4, g5, g6, g7, g8⟩
      · left; exact hc
      · right
        refine ⟨j', i', g1, g2, g3, g4, g5, g6, g7, ?_⟩
        intro B' T3 hT3
        rcases T2' with _ | ⟨B'', T3'⟩
        · -- B was the last blocker of T; the new blocker N is its successor
          simp only [List.nil_append] at h1
          rw [h1] at hT3
          simp only [List.cons.injEq] at hT3
          obtain ⟨rfl, -⟩ := hT3
          apply hsucc j' i' _ g2
          refine ⟨?_, ⟨g3, g4⟩, Or.inl ⟨g2, ?_⟩⟩
          · obtain ⟨B₀, hB₀, hjB₀⟩ := ha j' g1
            refine ⟨B₀, ?_, hjB₀⟩
            dsimp only; rw [h2]
            simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hB₀ ⊢
            exact hB₀
          · have : T = T1 ++ [B] := by rw [h2]
            rw [this]; exact g5
        · rw [h1] at hT3
          simp only [List.cons_append, List.cons.injEq] at hT3
          obtain ⟨hB, -⟩ := hT3
          rw [← hB]
          exact g8 B'' T3' rfl

theorem aux_ep_invalid_load (Γ : J → Finset M) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j)
    (s : AlgState J M) (hσ : Valid Γ p s.σ) (j : J) (i : M)
    (hpm : IsPotentialMove Γ p s j i) (hv : ¬ IsValidMove Γ p s j i)
    (hbig : ¬ IsBig p j ∨ ¬ HasBig p s i) : 1 + R < pload p s.σ i + p j := by
  obtain ⟨_, hmv, _⟩ := aux_ep_pm_facts Γ p s j i hpm
  by_contra h
  push_neg at h
  exact hv ⟨hpm, aux_ep_valid_update Γ p hp s.σ hσ j i hmv.1 hmv.2 hbig h⟩

theorem aux_ep_Zinfo (Γ : J → Finset M) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1)
    (σ : J → Option M) (hσ : Valid Γ p σ) (i : M) :
    ∃ a b : ℕ, ∃ Ps : ℝ, a ≤ 1 ∧ 0 ≤ Ps ∧
      aux_ep_Z p σ i = 11/17 * (a : ℝ) + 9/17 * (b : ℝ) + Ps ∧
      pload p σ i ≤ (a : ℝ) + 11/17 * (b : ℝ) + Ps ∧
      ((¬ ∃ j', σ j' = some i ∧ IsBig p j') → a = 0) ∧
      (∀ j', σ j' = some i → IsSmall p j' → p j' ≤ Ps) := by
  set L := Finset.univ.filter (fun j => σ j = some i) with hL
  obtain ⟨h1, h2⟩ := aux_ep_data p L (fun j _ => hp1 j)
  refine ⟨(L.filter (IsBig p)).card, (L.filter (IsMedium p)).card,
    ∑ j ∈ L.filter (IsSmall p), p j, ?_, Finset.sum_nonneg (fun j _ => hp j), h1, h2, ?_, ?_⟩
  · calc (L.filter (IsBig p)).card
        ≤ (Finset.univ.filter (fun j => σ j = some i ∧ IsBig p j)).card := by
          apply Finset.card_le_card
          intro x hx
          simp only [hL, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          exact hx
      _ ≤ 1 := (hσ.2 i).1
  · intro hnb
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hx hxb
    simp only [hL, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact hnb ⟨x, hx, hxb⟩
  · intro j' hj' hs
    apply Finset.single_le_sum (fun k _ => hp k)
    simp only [hL, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hj', hs⟩

theorem aux_ep_S1_of (Γ : J → Finset M) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1)
    (σ : J → Option M) (hσ : Valid Γ p σ) (i : M) (j : J) (hjs : IsSmall p j)
    (hload : 1 + R < pload p σ i + p j) : aux_ep_S1 p σ i (p j) := by
  obtain ⟨a, b, Ps, ha, hPs, hZ, hpl, -, -⟩ := aux_ep_Zinfo Γ p hp hp1 σ hσ i
  unfold IsSmall at hjs
  unfold R at hload
  have := aux_ep_num1 a b a (pload p σ i - Ps - a) Ps (p j) (aux_ep_Z p σ i) ha le_rfl
    (by linarith) hPs (by linarith) hjs hZ
  exact ⟨hjs, this⟩

theorem aux_ep_S2_of (Γ : J → Finset M) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1)
    (σ : J → Option M) (hσ : Valid Γ p σ) (i : M) (q : ℝ)
    (hnb : ¬ ∃ j', σ j' = some i ∧ IsBig p j') (hq : q < 14/17)
    (hload : 1 + R < pload p σ i + q) : 1 < aux_ep_Z p σ i := by
  obtain ⟨a, b, Ps, ha, hPs, hZ, hpl, h0, -⟩ := aux_ep_Zinfo Γ p hp hp1 σ hσ i
  have ha0 := h0 hnb
  subst ha0
  unfold R at hload
  push_cast at hZ hpl
  exact aux_ep_num2 b (pload p σ i - Ps) Ps q (aux_ep_Z p σ i) (by linarith) hPs (by linarith) hq
    (by linarith)

theorem aux_ep_S3Z_of (Γ : J → Finset M) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1)
    (σ : J → Option M) (hσ : Valid Γ p σ) (i : M) (j' : J)
    (hnb : ¬ ∃ j', σ j' = some i ∧ IsBig p j') (hj' : σ j' = some i) (hj's : IsSmall p j')
    (hload : 16/17 < pload p σ i) :
    14/17 < aux_ep_Z p σ i ∧ (16/17 < aux_ep_Z p σ i ∨ 9/17 + p j' ≤ aux_ep_Z p σ i) := by
  obtain ⟨a, b, Ps, ha, hPs, hZ, hpl, h0, hsm⟩ := aux_ep_Zinfo Γ p hp hp1 σ hσ i
  have ha0 := h0 hnb
  subst ha0
  push_cast at hZ hpl
  exact aux_ep_num3 b (pload p σ i - Ps) Ps (p j') (aux_ep_Z p σ i) (hp j') (by linarith)
    (hsm j' hj' hj's) (by linarith) (by linarith)

theorem aux_ep_pres_step (Γ : J → Finset M) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hp1 : ∀ j, p j ≤ 1) (jnew : J) (s s' : AlgState J M) (hI : aux_ep_Inv Γ p jnew s)
    (hst : Step Γ p jnew s s') (hloop : s'.σ jnew = none) : aux_ep_Inv Γ p jnew s' := by
  obtain ⟨σ, T⟩ := s
  obtain ⟨hnone, j, i, hpm, hmin, k, hk, hjk, rfl⟩ := hst
  dsimp only at hnone hk hjk
  rw [List.get_eq_getElem] at hjk
  obtain ⟨hJT, hmv, hms⟩ := aux_ep_pm_facts Γ p _ j i hpm
  by_cases hv : IsValidMove Γ p ⟨σ, T⟩ j i
  · rw [if_pos hv] at hloop ⊢
    exact aux_ep_pres_valid Γ p hp jnew σ T hI hnone j i hpm hv k hk hjk hloop
  rw [if_neg hv]
  have hchosen : ∀ j' i', IsPotentialMoveOf Γ p ⟨σ, T⟩ j' i' .small → IsSmall p j' →
      IsPotentialMoveOf Γ p ⟨σ, T⟩ j i .small ∧ p j ≤ p j' := by
    intro j' i' h1 h2
    have := (hmin j' i' ⟨_, h1⟩).trans (aux_ep_val_small_le Γ p hp _ j' i' h1)
    exact aux_ep_val_lt2 Γ p _ j i hpm hv _ _ this (by unfold IsSmall at h2; linarith)
  have hvalid : Valid Γ p σ := hI.valid
  by_cases hB : IsPotentialMoveOf Γ p ⟨σ, T⟩ j i .small ∨
      IsPotentialMoveOf Γ p ⟨σ, T⟩ j i .hugeToSmall
  · rw [if_pos hB]
    have hS1 : IsSmall p j → aux_ep_S1 p σ i (p j) := by
      intro hjs
      have hnb : ¬ IsBig p j := by unfold IsSmall IsBig at *; intro h; linarith
      exact aux_ep_S1_of Γ p hp hp1 σ hvalid i j hjs
        (aux_ep_invalid_load Γ p hp _ hvalid j i hpm hv (Or.inl hnb))
    apply aux_ep_pres_append Γ p jnew σ T hI _ i rfl
    · intro x hx
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact hx.1
    · intro B hB' 
      rw [Finset.disjoint_left]
      intro x hxB hxN
      simp only [jobsT, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hxN
      exact hxN.2 ⟨B, hB', hxB⟩
    · intro h; cases h
    · intro h; cases h
    · intro _
      refine ⟨?_, hms, ?_⟩
      · intro x hx
        by_cases hxT : InJT (⟨σ, T⟩ : AlgState J M) x
        · obtain ⟨B', hB', hxB'⟩ := hxT
          exact ⟨B', List.mem_append_left _ hB', hxB'⟩
        · refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
          simp only [jobsT, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hx, hxT⟩
      · by_cases hsm : IsPotentialMoveOf Γ p ⟨σ, T⟩ j i .small
        · by_cases hjs : IsSmall p j
          · left
            have := (hS1 hjs).2.1
            linarith
          · left
            obtain ⟨_, _, h3⟩ := hsm
            obtain ⟨hnb, hq⟩ : ¬ HasBig p (⟨σ, T⟩ : AlgState J M) i ∧ p j < 14/17 := by
              rcases h3 with ⟨h, _⟩ | ⟨h, _, h'⟩ | ⟨h, _, _, h'⟩
              · exact absurd h hjs
              · unfold IsMedium at h; exact ⟨h', by linarith [h.2]⟩
              · unfold IsLarge at h; exact ⟨h', h.2⟩
            exact aux_ep_S2_of Γ p hp hp1 σ hvalid i (p j) hnb hq
              (aux_ep_invalid_load Γ p hp _ hvalid j i hpm hv (Or.inr hnb))
        · right
          have hhs := hB.resolve_left hsm
          obtain ⟨_, _, hhuge, hnMT, hnb, hsum⟩ := hhs
          have hload := aux_ep_invalid_load Γ p hp _ hvalid j i hpm hv (Or.inr hnb)
          dsimp only at hload
          obtain ⟨j', hj'i, hj'n⟩ : ∃ j', σ j' = some i ∧
              j' ∉ Si Γ p ⟨σ, T⟩ i ∪ Mi p ⟨σ, T⟩ i := by
            by_contra hcon
            push_neg at hcon
            have : pload p σ i ≤ ∑ k ∈ Si Γ p ⟨σ, T⟩ i ∪ Mi p ⟨σ, T⟩ i, p k := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro x hx
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
                exact hcon x hx
              · intro x _ _; exact hp x
            linarith
          rw [Finset.mem_union, not_or] at hj'n
          have hj'nb : ¬ IsBig p j' := fun h => hnb ⟨j', hj'i, h⟩
          have hj'nm : ¬ IsMedium p j' := fun h => hj'n.2 (by
            simp only [Mi, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hj'i, h⟩)
          have hj's : IsSmall p j' := by
            unfold IsBig IsMedium IsSmall at *
            by_contra h
            push_neg at h hj'nb
            exact hj'nm ⟨h, hj'nb⟩
          have hj'nS : ¬ InS Γ p (⟨σ, T⟩ : AlgState J M) j' := fun h => hj'n.1 (by
            simp only [Si, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hj'i, h⟩)
          obtain ⟨i', hmv', hms'⟩ : ∃ i', IsMove Γ (⟨σ, T⟩ : AlgState J M) j' i' ∧
              ¬ InMS (⟨σ, T⟩ : AlgState J M) i' := by
            by_contra hcon
            push_neg at hcon
            exact hj'nS ⟨hj's, hcon⟩
          have hii' : i' ≠ i := by
            rintro rfl
            exact hmv'.2 hj'i
          have hZ3 := aux_ep_S3Z_of Γ p hp hp1 σ hvalid i j' hnb hj'i hj's
            (by unfold R at hload; linarith [hp1 j])
          refine ⟨j', i', hj'i, hj's, hmv'.1, hmv'.2, ?_, hZ3.1, hZ3.2, ?_⟩
          · rintro ⟨B', hB', hk', hm'⟩
            rcases List.mem_append.mp hB' with h | h
            · exact hms' ⟨B', h, hk', hm'⟩
            · rw [List.mem_singleton] at h
              subst h
              simp only [Option.some.injEq] at hm'
              exact hii' hm'.symm
          · intro B' T3 h; cases h
    · intro j' i' h1 h2
      obtain ⟨h3, h4⟩ := hchosen j' i' h1 h2
      have hjs : IsSmall p j := by unfold IsSmall at *; linarith
      exact ⟨rfl, i, rfl, p j, h4, hS1 hjs⟩
  rw [if_neg hB]
  by_cases hC : IsPotentialMoveOf Γ p ⟨σ, T⟩ j i .medLargeToBig ∨
      IsPotentialMoveOf Γ p ⟨σ, T⟩ j i .hugeToBig
  · rw [if_pos hC]
    have hcond : ¬ InMT (⟨σ, T⟩ : AlgState J M) i ∨ ¬ InMB (⟨σ, T⟩ : AlgState J M) i := by
      rcases hC with ⟨_, _, h3, _⟩ | ⟨_, _, _, h, _⟩
      · rcases h3 with ⟨_, h⟩ | ⟨_, h, _⟩
        · left; exact h
        · right; exact h
      · left; exact h
    have hhb : HasBig p (⟨σ, T⟩ : AlgState J M) i := by
      rcases hC with ⟨_, _, _, h⟩ | ⟨_, _, _, _, h, _⟩
      · exact h
      · exact h
    apply aux_ep_pres_append Γ p jnew σ T hI _ i rfl
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact hx.1
    · intro B hB'
      rw [Finset.disjoint_left]
      intro x hxB hxN
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hxN
      have hBm := aux_ep_jobmach Γ p jnew _ hI hnone B hB' x hxB i hxN.1
      rcases hBk : B.kind with _ | _ | _
      · exact hms ⟨B, hB', hBk, hBm⟩
      · rcases hcond with h | h
        · exact h ⟨B, hB', hBm⟩
        · exact h ⟨B, hB', hBk, hBm⟩
      · obtain ⟨T1, T2, hdec⟩ := List.append_of_mem hB'
        have := (hI.med T1 B T2 hdec hBk).2.1 x hxB
        unfold IsMedium IsBig at *
        linarith [this.2, hxN.2]
    · intro _
      obtain ⟨x, hx1, hx2⟩ := hhb
      refine ⟨⟨x, ?_⟩, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hx1, hx2⟩
      · intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        exact hy.2
    · intro h; cases h
    · intro h; cases h
    · intro j' i' h1 h2
      exact absurd (Or.inl (hchosen j' i' h1 h2).1) hB
  rw [if_neg hC]
  have hHM : IsPotentialMoveOf Γ p ⟨σ, T⟩ j i .hugeToMedium := by
    obtain ⟨t, ht⟩ := hpm
    cases t with
    | small => exact absurd (Or.inl ht) hB
    | hugeToSmall => exact absurd (Or.inr ht) hB
    | medLargeToBig => exact absurd (Or.inl ht) hC
    | hugeToBig => exact absurd (Or.inr ht) hC
    | hugeToMedium => exact ht
  obtain ⟨_, _, _, hnMT, hle, hlt⟩ := hHM
  apply aux_ep_pres_append Γ p jnew σ T hI _ i rfl
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact hx.1
  · intro B hB'
    rw [Finset.disjoint_left]
    intro x hxB hxN
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hxN
    have hBm := aux_ep_jobmach Γ p jnew _ hI hnone B hB' x hxB i hxN.1
    exact hnMT ⟨B, hB', hBm⟩
  · intro h; cases h
  · intro _
    refine ⟨?_, ?_, ?_⟩
    · by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      have hMi : Mi p (⟨σ, T⟩ : AlgState J M) i = ∅ := hne
      rw [hMi, Finset.union_empty] at hlt
      linarith
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      exact hy.2
    · have := hp1 j
      unfold R at hlt ⊢
      show 16/17 < ∑ k ∈ Si Γ p ⟨σ, T⟩ i ∪ Mi p ⟨σ, T⟩ i, p k
      linarith
  · intro h; cases h
  · intro j' i' h1 h2
    exact absurd (Or.inl (hchosen j' i' h1 h2).1) hB

theorem aux_ep_inv_reach (Γ : J → Finset M) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hp1 : ∀ j, p j ≤ 1) (σ0 : J → Option M) (jnew : J) (hσ0 : Valid Γ p σ0)
    (s : AlgState J M) (hs : Reachable Γ p σ0 jnew s) (hloop : s.σ jnew = none) :
    aux_ep_Inv Γ p jnew s := by
  induction hs with
  | refl => exact aux_ep_inv_init Γ p σ0 jnew hσ0
  | tail _ hst ih => exact aux_ep_pres_step Γ p hp hp1 jnew _ _ (ih hst.1) hst hloop

theorem aux_ep_small_iff (p : J → ℝ) (j : J) : IsSmall p j ↔ ¬ IsBig p j ∧ ¬ IsMedium p j := by
  unfold IsSmall IsBig IsMedium
  constructor
  · intro h; exact ⟨by linarith, fun h' => by linarith [h'.1]⟩
  · rintro ⟨h1, h2⟩
    push_neg at h1
    by_contra h
    push_neg at h
    exact h2 ⟨h, h1⟩

theorem aux_ep_z_JT (Γ : J → Finset M) (p : J → ℝ) (s : AlgState J M) (j : J) (h : InJT s j) :
    zStar Γ p s j = aux_ep_zeta p j := by
  unfold zStar aux_ep_zeta
  by_cases hb : IsBig p j
  · simp [h, hb]
  · by_cases hm : IsMedium p j
    · simp [h, hb, hm]
    · have hs : IsSmall p j := (aux_ep_small_iff p j).mpr ⟨hb, hm⟩
      simp [h, hb, hm, hs]

theorem aux_ep_z_S (Γ : J → Finset M) (p : J → ℝ) (s : AlgState J M) (j : J)
    (h : InS Γ p s j) : zStar Γ p s j = p j := by
  have hs := h.1
  obtain ⟨hb, hm⟩ := (aux_ep_small_iff p j).mp hs
  unfold zStar
  simp [hb, hm, hs, h]

theorem aux_ep_z_nonneg (Γ : J → Finset M) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (s : AlgState J M)
    (j : J) : 0 ≤ zStar Γ p s j := by
  unfold zStar
  split_ifs <;> first | exact hp j | norm_num

theorem aux_ep_z_le (Γ : J → Finset M) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (s : AlgState J M)
    (j : J) : zStar Γ p s j ≤ p j := by
  unfold zStar
  split_ifs with h1 h2 h3
  · exact h1.2
  · exact le_of_lt h2.2.1
  · exact le_refl _
  · exact hp j

theorem aux_ep_z_le11 (Γ : J → Finset M) (p : J → ℝ) (s : AlgState J M) (j : J)
    (hs : ¬ IsSmall p j) : zStar Γ p s j ≤ 11/17 := by
  unfold zStar
  split_ifs with h1 h2 h3
  · exact le_refl _
  · norm_num
  · exact absurd h3.2 hs
  · norm_num

theorem aux_ep_num4 (b : ℕ) (x y : ℝ) (hb : 1 ≤ b) (hx : 0 ≤ x) (hxy : R < x + y)
    (hy : y ≤ 11/17 * b) : 14/17 < x + 9/17 * b := by
  unfold R at hxy
  rcases b with _ | _ | b
  · omega
  · push_cast at *; linarith
  · push_cast at *
    have : (0:ℝ) ≤ b := by positivity
    linarith

theorem aux_ep_claim47 (Γ : J → Finset M) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hp1 : ∀ j, p j ≤ 1) (jnew : J) (σ : J → Option M) (T : List (Blocker J M))
    (hI : aux_ep_Inv Γ p jnew ⟨σ, T⟩)
    (hno : ∀ j i, ¬ IsPotentialMove Γ p ⟨σ, T⟩ j i) (i : M) (C : Finset J)
    (hC : C ∈ configs Γ p 1 i) :
    ∑ j ∈ C, zStar Γ p ⟨σ, T⟩ j ≤ yStar Γ p ⟨σ, T⟩ i := by
  have hC' := hC
  simp only [configs, Finset.mem_filter, Finset.mem_univ, true_and] at hC'
  obtain ⟨hCΓ, hCp⟩ := hC'
  have hznn := fun j => aux_ep_z_nonneg Γ p hp ⟨σ, T⟩ j
  unfold yStar
  by_cases hMS : InMS (⟨σ, T⟩ : AlgState J M) i
  · rw [if_pos hMS]
    calc ∑ j ∈ C, zStar Γ p ⟨σ, T⟩ j ≤ ∑ j ∈ C, p j :=
          Finset.sum_le_sum (fun j _ => aux_ep_z_le Γ p hp _ j)
      _ ≤ 1 := hCp
  rw [if_neg hMS]
  dsimp only
  set Ls := Finset.univ.filter (fun j => σ j = some i) with hLs
  have hK1 : ∀ j ∈ C, σ j ≠ some i → IsSmall p j → zStar Γ p ⟨σ, T⟩ j = 0 := by
    intro j hj hne hs
    by_cases hJT : InJT (⟨σ, T⟩ : AlgState J M) j
    · exfalso; exact hno j i ⟨.small, hJT, ⟨hCΓ j hj, hne⟩, Or.inl ⟨hs, hMS⟩⟩
    · by_cases hS : InS Γ p (⟨σ, T⟩ : AlgState J M) j
      · exfalso; exact hMS (hS.2 i ⟨hCΓ j hj, hne⟩)
      · unfold zStar; simp [hJT, hS]
  have hK2 : ∀ j1 ∈ C, ∀ j2 ∈ C, ¬ IsSmall p j1 → ¬ IsSmall p j2 → j1 = j2 := by
    intro j1 h1 j2 h2 hs1 hs2
    by_contra hne
    unfold IsSmall at hs1 hs2
    push_neg at hs1 hs2
    have : p j1 + p j2 ≤ ∑ j ∈ C, p j := by
      rw [← Finset.sum_pair hne]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      · intro x _ _; exact hp x
    linarith
  set Cs := C.filter (fun j => IsSmall p j ∧ σ j = some i) with hCs
  have hsplit : ∑ j ∈ C, zStar Γ p ⟨σ, T⟩ j = ∑ j ∈ Cs, zStar Γ p ⟨σ, T⟩ j
      + ∑ j ∈ C.filter (fun j => ¬ IsSmall p j), zStar Γ p ⟨σ, T⟩ j := by
    rw [← Finset.sum_filter_add_sum_filter_not C (IsSmall p)]
    congr 1
    symm
    apply Finset.sum_subset
    · intro x hx
      simp only [hCs, Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, hx.2.1⟩
    · intro x hx hxn
      simp only [hCs, Finset.mem_filter, not_and] at hx hxn
      exact hK1 x hx.1 (hxn hx.1 hx.2) hx.2
  have hCsL : Cs ⊆ Ls := by
    intro x hx
    simp only [hCs, hLs, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.2.2
  rcases (C.filter (fun j => ¬ IsSmall p j)).eq_empty_or_nonempty with he | ⟨j', hj'⟩
  · rw [hsplit, he, Finset.sum_empty, add_zero]
    exact Finset.sum_le_sum_of_subset_of_nonneg hCsL (fun x _ _ => hznn x)
  have hsingle : C.filter (fun j => ¬ IsSmall p j) = {j'} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, hxs⟩
      rw [Finset.mem_filter] at hj'
      exact hK2 x hx j' hj'.1 hxs hj'.2
    · rintro rfl
      exact Finset.mem_filter.mp hj'
  rw [hsplit, hsingle, Finset.sum_singleton]
  rw [Finset.mem_filter] at hj'
  obtain ⟨hj'C, hj's⟩ := hj'
  have hrepl : ∀ jX, σ jX = some i → ¬ IsSmall p jX →
      zStar Γ p ⟨σ, T⟩ j' ≤ zStar Γ p ⟨σ, T⟩ jX →
      ∑ j ∈ Cs, zStar Γ p ⟨σ, T⟩ j + zStar Γ p ⟨σ, T⟩ j' ≤ ∑ j ∈ Ls, zStar Γ p ⟨σ, T⟩ j := by
    intro jX hjX hjXs hle
    have hmem : jX ∈ Ls := by simp only [hLs, Finset.mem_filter, Finset.mem_univ, true_and]; exact hjX
    have hsub : Cs ⊆ Ls.erase jX := by
      intro x hx
      rw [Finset.mem_erase]
      refine ⟨?_, hCsL hx⟩
      rintro rfl
      simp only [hCs, Finset.mem_filter] at hx
      exact hjXs hx.2.1
    calc _ ≤ ∑ j ∈ Ls.erase jX, zStar Γ p ⟨σ, T⟩ j + zStar Γ p ⟨σ, T⟩ jX :=
          add_le_add (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hznn x)) hle
      _ = _ := Finset.sum_erase_add _ _ hmem
  by_cases hj'i : σ j' = some i
  · exact hrepl j' hj'i hj's le_rfl
  by_cases hz0 : zStar Γ p ⟨σ, T⟩ j' = 0
  · rw [hz0, add_zero]
    exact Finset.sum_le_sum_of_subset_of_nonneg hCsL (fun x _ _ => hznn x)
  have hJT' : InJT (⟨σ, T⟩ : AlgState J M) j' := by
    by_contra h
    apply hz0
    unfold zStar
    simp [h, hj's]
  have hmv' : IsMove Γ (⟨σ, T⟩ : AlgState J M) j' i := ⟨hCΓ j' hj'C, hj'i⟩
  have hz11 := aux_ep_z_le11 Γ p ⟨σ, T⟩ j' hj's
  have hCsb : ∑ j ∈ Cs, zStar Γ p ⟨σ, T⟩ j ≤ 1 - p j' := by
    have hsub : Cs ⊆ C.erase j' := by
      intro x hx
      rw [Finset.mem_erase]
      simp only [hCs, Finset.mem_filter] at hx
      refine ⟨?_, hx.1⟩
      rintro rfl
      exact hj's hx.2.1
    have h1 : ∑ j ∈ Cs, zStar Γ p ⟨σ, T⟩ j ≤ ∑ j ∈ Cs, p j :=
      Finset.sum_le_sum (fun j _ => aux_ep_z_le Γ p hp _ j)
    have h2 : ∑ j ∈ Cs, p j ≤ ∑ j ∈ C.erase j', p j :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hp x)
    have h3 := Finset.sum_erase_add C p hj'C
    linarith
  by_cases hMB : InMB (⟨σ, T⟩ : AlgState J M) i
  · obtain ⟨B, hB, hBk, hBm⟩ := hMB
    obtain ⟨⟨jB, hjB⟩, hallbig⟩ := hI.big B hB hBk
    have hσjB := hI.mach B hB i hBm jB hjB
    have hbB := hallbig jB hjB
    have hzjB : zStar Γ p ⟨σ, T⟩ jB = 11/17 := by
      rw [aux_ep_z_JT Γ p _ jB ⟨B, hB, hjB⟩]
      simp [aux_ep_zeta, hbB]
    have hjBs : ¬ IsSmall p jB := fun h => ((aux_ep_small_iff p jB).mp h).1 hbB
    exact hrepl jB hσjB hjBs (by rw [hzjB]; exact hz11)
  have hMedB : ∀ B ∈ T, B.machine = some i → B.kind = BlockerKind.medium := by
    intro B hB hBm
    rcases hk : B.kind with _ | _ | _
    · exact absurd ⟨B, hB, hk, hBm⟩ hMS
    · exact absurd ⟨B, hB, hk, hBm⟩ hMB
    · rfl
  by_cases hhuge : IsHuge p j'
  · have hbound : ∑ j ∈ Cs, zStar Γ p ⟨σ, T⟩ j + zStar Γ p ⟨σ, T⟩ j' ≤ 14/17 := by
      unfold IsHuge at hhuge
      linarith
    by_cases hMT : InMT (⟨σ, T⟩ : AlgState J M) i
    · obtain ⟨B, hB, hBm⟩ := hMT
      have hBk := hMedB B hB hBm
      obtain ⟨T1, T2, hdec⟩ := List.append_of_mem hB
      obtain ⟨hne, hallm, hR⟩ := hI.med T1 B T2 hdec hBk
      have hR' := hR i hBm
      have hT1 : ∀ B' ∈ T1, B' ∈ T := by
        intro B' hB'; rw [show T = T1 ++ B :: T2 from hdec]; exact List.mem_append_left _ hB'
      have hsubL : Si Γ p ⟨σ, T1⟩ i ∪ B.jobs ⊆ Ls := by
        intro x hx
        simp only [hLs, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases Finset.mem_union.mp hx with h | h
        · simp only [Si, Finset.mem_filter, Finset.mem_univ, true_and] at h
          exact h.1
        · exact hI.mach B hB i hBm x h
      have hzS : ∀ x ∈ Si Γ p ⟨σ, T1⟩ i, zStar Γ p ⟨σ, T⟩ x = p x := by
        intro x hx
        simp only [Si, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        apply aux_ep_z_S
        exact ⟨hx.2.1, fun i' hi' => aux_ep_ms_mono σ σ T1 T hT1 i' (hx.2.2 i' hi')⟩
      have hzB : ∀ x ∈ B.jobs, zStar Γ p ⟨σ, T⟩ x = 9/17 := by
        intro x hx
        rw [aux_ep_z_JT Γ p _ x ⟨B, hB, hx⟩]
        have hm := hallm x hx
        have hnb : ¬ IsBig p x := by unfold IsBig IsMedium at *; linarith [hm.2]
        simp [aux_ep_zeta, hnb, hm]
      have hdisj : Disjoint (Si Γ p ⟨σ, T1⟩ i) B.jobs := by
        rw [Finset.disjoint_left]
        intro x hx hxB
        simp only [Si, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        have h1 := hx.2.1
        have h2 := hallm x hxB
        unfold IsSmall IsMedium at *
        linarith [h2.1]
      have hsumB : ∑ k ∈ B.jobs, p k ≤ 11/17 * (B.jobs.card : ℝ) := by
        have : ∑ k ∈ B.jobs, p k ≤ ∑ k ∈ B.jobs, (11/17 : ℝ) :=
          Finset.sum_le_sum (fun k hk => le_of_lt (hallm k hk).2)
        rw [Finset.sum_const, nsmul_eq_mul] at this
        linarith
      have hcard : 1 ≤ B.jobs.card := Finset.card_pos.mpr hne
      rw [Finset.sum_union hdisj] at hR'
      have heq : ∑ x ∈ Si Γ p ⟨σ, T1⟩ i ∪ B.jobs, zStar Γ p ⟨σ, T⟩ x
          = ∑ x ∈ Si Γ p ⟨σ, T1⟩ i, p x + 9/17 * (B.jobs.card : ℝ) := by
        rw [Finset.sum_union hdisj, Finset.sum_congr rfl hzS, Finset.sum_congr rfl hzB,
          Finset.sum_const, nsmul_eq_mul]
        ring
      refine le_of_lt ?_
      calc _ ≤ 14/17 := hbound
        _ < ∑ x ∈ Si Γ p ⟨σ, T1⟩ i, p x + 9/17 * (B.jobs.card : ℝ) :=
          aux_ep_num4 B.jobs.card _ _ hcard (Finset.sum_nonneg (fun x _ => hp x)) hR' hsumB
        _ = _ := heq.symm
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsubL (fun x _ _ => hznn x)
    · have hF4 : 1 + R < p j' + ∑ k ∈ Si Γ p ⟨σ, T⟩ i, p k := by
        by_contra hle
        push_neg at hle
        by_cases h2 : p j' + ∑ k ∈ Si Γ p ⟨σ, T⟩ i ∪ Mi p ⟨σ, T⟩ i, p k ≤ 1 + R
        · by_cases hHB : HasBig p (⟨σ, T⟩ : AlgState J M) i
          · exact hno j' i ⟨.hugeToBig, hJT', hmv', hhuge, hMT, hHB, h2⟩
          · exact hno j' i ⟨.hugeToSmall, hJT', hmv', hhuge, hMT, hHB, h2⟩
        · push_neg at h2
          exact hno j' i ⟨.hugeToMedium, hJT', hmv', hhuge, hMT, hle, h2⟩
      have hzS : ∀ x ∈ Si Γ p ⟨σ, T⟩ i, zStar Γ p ⟨σ, T⟩ x = p x := by
        intro x hx
        simp only [Si, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        exact aux_ep_z_S Γ p _ x hx.2
      have hSiL : Si Γ p ⟨σ, T⟩ i ⊆ Ls := by
        intro x hx
        simp only [Si, hLs, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact hx.1
      have := hp1 j'
      unfold R at hF4
      refine le_of_lt ?_
      calc _ ≤ 14/17 := hbound
        _ < ∑ k ∈ Si Γ p ⟨σ, T⟩ i, p k := by linarith
        _ = ∑ k ∈ Si Γ p ⟨σ, T⟩ i, zStar Γ p ⟨σ, T⟩ k := (Finset.sum_congr rfl hzS).symm
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hSiL (fun x _ _ => hznn x)
  · by_cases hlarge : IsLarge p j'
    · exfalso
      by_cases hHB : HasBig p (⟨σ, T⟩ : AlgState J M) i
      · exact hno j' i ⟨.medLargeToBig, hJT', hmv', Or.inr ⟨hlarge, hMB, hMS⟩, hHB⟩
      · exact hno j' i ⟨.small, hJT', hmv', Or.inr (Or.inr ⟨hlarge, hMB, hMS, hHB⟩)⟩
    · have hmed : IsMedium p j' := by
        unfold IsSmall IsHuge IsLarge IsMedium at *
        push_neg at hj's hhuge
        refine ⟨hj's, ?_⟩
        by_contra h
        push_neg at h
        exact hlarge ⟨h, hhuge⟩
      have hMT : InMT (⟨σ, T⟩ : AlgState J M) i := by
        by_contra hMT
        by_cases hHB : HasBig p (⟨σ, T⟩ : AlgState J M) i
        · exact hno j' i ⟨.medLargeToBig, hJT', hmv', Or.inl ⟨hmed, hMT⟩, hHB⟩
        · exact hno j' i ⟨.small, hJT', hmv', Or.inr (Or.inl ⟨hmed, hMT, hHB⟩)⟩
      obtain ⟨B, hB, hBm⟩ := hMT
      have hBk := hMedB B hB hBm
      obtain ⟨T1, T2, hdec⟩ := List.append_of_mem hB
      obtain ⟨⟨jM, hjM⟩, hallm, -⟩ := hI.med T1 B T2 hdec hBk
      have hσjM := hI.mach B hB i hBm jM hjM
      have hmM := hallm jM hjM
      have hzjM : zStar Γ p ⟨σ, T⟩ jM = 9/17 := by
        rw [aux_ep_z_JT Γ p _ jM ⟨B, hB, hjM⟩]
        have hnb : ¬ IsBig p jM := by unfold IsBig IsMedium at *; linarith [hmM.2]
        simp [aux_ep_zeta, hnb, hmM]
      have hzj' : zStar Γ p ⟨σ, T⟩ j' = 9/17 := by
        rw [aux_ep_z_JT Γ p _ j' hJT']
        have hnb : ¬ IsBig p j' := by unfold IsBig IsMedium at *; linarith [hmed.2]
        simp [aux_ep_zeta, hnb, hmed]
      have hjMs : ¬ IsSmall p jM := fun h => ((aux_ep_small_iff p jM).mp h).2 hmM
      exact hrepl jM hσjM hjMs (by rw [hzj', hzjM])

theorem aux_ep_ms_cons (σ : J → Option M) (B : Blocker J M) (L : List (Blocker J M)) (i : M) :
    InMS (⟨σ, B :: L⟩ : AlgState J M) i ↔
      (B.kind = BlockerKind.small ∧ B.machine = some i) ∨ InMS (⟨σ, L⟩ : AlgState J M) i := by
  constructor
  · rintro ⟨B', hB', h1, h2⟩
    rcases List.mem_cons.mp hB' with rfl | h
    · left; exact ⟨h1, h2⟩
    · right; exact ⟨B', h, h1, h2⟩
  · rintro (⟨h1, h2⟩ | ⟨B', hB', h1, h2⟩)
    · exact ⟨B, List.mem_cons_self, h1, h2⟩
    · exact ⟨B', List.mem_cons_of_mem _ hB', h1, h2⟩

theorem aux_ep_ms_insert (σ : J → Option M) (B : Blocker J M) (L : List (Blocker J M)) (i0 : M)
    (hBk : B.kind = BlockerKind.small) (hBm : B.machine = some i0) :
    Finset.univ.filter (fun i => InMS (⟨σ, B :: L⟩ : AlgState J M) i)
      = insert i0 (Finset.univ.filter (fun i => InMS (⟨σ, L⟩ : AlgState J M) i)) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, aux_ep_ms_cons,
    hBm, Option.some.injEq]
  constructor
  · rintro (⟨_, h⟩ | h)
    · left; exact h.symm
    · right; exact h
  · rintro (h | h)
    · left; exact ⟨hBk, h.symm⟩
    · right; exact h

theorem aux_ep_acc (σ : J → Option M) (T : List (Blocker J M)) (f : M → ℝ)
    (hnd : ∀ T1 B T2, T = T1 ++ B :: T2 → B.kind = BlockerKind.small → ∀ i, B.machine = some i →
      ¬ InMS (⟨σ, T1⟩ : AlgState J M) i)
    (hgood : ∀ T1 B T2, T = T1 ++ B :: T2 → B.kind = BlockerKind.small → ∀ i, B.machine = some i →
      0 < f i ∨ ∃ B' T3, T2 = B' :: T3 ∧ B'.kind = BlockerKind.small ∧
        ∃ i₂, B'.machine = some i₂ ∧ 0 < f i₂ ∧ 0 < f i + f i₂) :
    ∀ n : ℕ, ∀ L T0, T = T0 ++ L → L.length ≤ n →
      0 ≤ ∑ i ∈ Finset.univ.filter (fun i => InMS (⟨σ, L⟩ : AlgState J M) i), f i ∧
      ((Finset.univ.filter (fun i => InMS (⟨σ, L⟩ : AlgState J M) i)).Nonempty →
        0 < ∑ i ∈ Finset.univ.filter (fun i => InMS (⟨σ, L⟩ : AlgState J M) i), f i) := by
  have hnd' : ∀ T0 B L, T = T0 ++ B :: L → B.kind = BlockerKind.small → ∀ i, B.machine = some i →
      ¬ InMS (⟨σ, L⟩ : AlgState J M) i := by
    rintro T0 B L hT hBk i hBm ⟨B2, hB2, hB2k, hB2m⟩
    obtain ⟨L1, L2, hL⟩ := List.append_of_mem hB2
    apply hnd (T0 ++ B :: L1) B2 L2 (by rw [hT, show L = L1 ++ B2 :: L2 from hL]; simp) hB2k i hB2m
    exact ⟨B, by simp, hBk, hBm⟩
  have hempty : Finset.univ.filter (fun i => InMS (⟨σ, []⟩ : AlgState J M) i) = ∅ := by
    ext i
    simp [InMS]
  intro n
  induction n with
  | zero =>
    intro L T0 hT hL
    have : L = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rw [hempty]; simp
  | succ n ih =>
    intro L T0 hT hL
    rcases L with _ | ⟨B, L'⟩
    · rw [hempty]; simp
    · have ihL' := ih L' (T0 ++ [B]) (by rw [hT]; simp) (by simp at hL; omega)
      by_cases hBs : B.kind = BlockerKind.small ∧ ∃ i0, B.machine = some i0
      · obtain ⟨hBk, i0, hBm⟩ := hBs
        have hnot := hnd' T0 B L' hT hBk i0 hBm
        have hi0 : i0 ∉ Finset.univ.filter (fun i => InMS (⟨σ, L'⟩ : AlgState J M) i) := by
          simp [hnot]
        rw [aux_ep_ms_insert σ B L' i0 hBk hBm, Finset.sum_insert hi0]
        rcases hgood T0 B L' hT hBk i0 hBm with hpos | ⟨B', T3, hL', hB'k, i₂, hB'm, hpos2, hpair⟩
        · exact ⟨by linarith [ihL'.1], fun _ => by linarith [ihL'.1]⟩
        · subst hL'
          have ihT3 := ih T3 (T0 ++ [B, B']) (by rw [hT]; simp) (by simp at hL; omega)
          have hnot2 := hnd' (T0 ++ [B]) B' T3 (by rw [hT]; simp) hB'k i₂ hB'm
          have hi2 : i₂ ∉ Finset.univ.filter (fun i => InMS (⟨σ, T3⟩ : AlgState J M) i) := by
            simp [hnot2]
          rw [aux_ep_ms_insert σ B' T3 i₂ hB'k hB'm, Finset.sum_insert hi2]
          exact ⟨by linarith [ihT3.1], fun _ => by linarith [ihT3.1]⟩
      · have hset : Finset.univ.filter (fun i => InMS (⟨σ, B :: L'⟩ : AlgState J M) i)
            = Finset.univ.filter (fun i => InMS (⟨σ, L'⟩ : AlgState J M) i) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, aux_ep_ms_cons]
          constructor
          · rintro (⟨h1, h2⟩ | h)
            · exact absurd ⟨h1, i, h2⟩ hBs
            · exact h
          · intro h; right; exact h
        rw [hset]
        exact ihL'

theorem aux_ep_claim48 (Γ : J → Finset M) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hp1 : ∀ j, p j ≤ 1) (jnew : J) (σ : J → Option M) (T : List (Blocker J M))
    (hI : aux_ep_Inv Γ p jnew ⟨σ, T⟩) (hnone : σ jnew = none) (hΓ : (Γ jnew).Nonempty)
    (hno : ∀ j i, ¬ IsPotentialMove Γ p ⟨σ, T⟩ j i) :
    ∑ i, yStar Γ p ⟨σ, T⟩ i < ∑ j, zStar Γ p ⟨σ, T⟩ j := by
  have hznn := fun j => aux_ep_z_nonneg Γ p hp ⟨σ, T⟩ j
  set W : M → ℝ := fun i =>
    ∑ j ∈ Finset.univ.filter (fun j => σ j = some i), zStar Γ p ⟨σ, T⟩ j with hW
  set MS := Finset.univ.filter (fun i => InMS (⟨σ, T⟩ : AlgState J M) i) with hMS
  have hy : ∑ i, yStar Γ p ⟨σ, T⟩ i = ∑ i ∈ MS, (1:ℝ)
      + ∑ i ∈ Finset.univ.filter (fun i => ¬ InMS (⟨σ, T⟩ : AlgState J M) i), W i := by
    simp only [yStar]
    rw [Finset.sum_ite]
  have hz : ∑ j, zStar Γ p ⟨σ, T⟩ j
      = ∑ j ∈ Finset.univ.filter (fun j => σ j = none), zStar Γ p ⟨σ, T⟩ j + ∑ i, W i := by
    rw [← Finset.sum_fiberwise Finset.univ σ (zStar Γ p ⟨σ, T⟩), Fintype.sum_option]
  have hWsplit : ∑ i, W i = ∑ i ∈ MS, W i
      + ∑ i ∈ Finset.univ.filter (fun i => ¬ InMS (⟨σ, T⟩ : AlgState J M) i), W i :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hjnew : zStar Γ p ⟨σ, T⟩ jnew
      ≤ ∑ j ∈ Finset.univ.filter (fun j => σ j = none), zStar Γ p ⟨σ, T⟩ j := by
    apply Finset.single_le_sum (fun j _ => hznn j)
    simp [hnone]
  obtain ⟨T0, hT0, hT0m⟩ := hI.root
  dsimp only at hT0
  have hjJT : InJT (⟨σ, T⟩ : AlgState J M) jnew :=
    ⟨aux_ep_root jnew, by rw [hT0]; exact List.mem_cons_self, by simp [aux_ep_root]⟩
  -- W agrees with Z on small-blocker machines
  have hWZ : ∀ i ∈ MS, W i = aux_ep_Z p σ i := by
    intro i hi
    simp only [hMS, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨B, hB, hBk, hBm⟩ := hi
    obtain ⟨T1, T2, hdec⟩ := List.append_of_mem hB
    have ha := (hI.small T1 B T2 hdec hBk i hBm).1
    simp only [hW, aux_ep_Z]
    apply Finset.sum_congr rfl
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨B', hB', hxB'⟩ := ha x hx
    apply aux_ep_z_JT
    refine ⟨B', ?_, hxB'⟩
    dsimp only
    rw [show T = T1 ++ B :: T2 from hdec]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hB' ⊢
    rcases hB' with h | h
    · left; exact h
    · right; left; exact h
  have hkey : ∑ i ∈ MS, (1:ℝ) < ∑ j ∈ Finset.univ.filter (fun j => σ j = none),
      zStar Γ p ⟨σ, T⟩ j + ∑ i ∈ MS, W i := by
    rcases MS.eq_empty_or_nonempty with he | hne
    · rw [he, Finset.sum_empty, Finset.sum_empty, add_zero]
      refine lt_of_lt_of_le ?_ hjnew
      rw [aux_ep_z_JT Γ p _ jnew hjJT]
      obtain ⟨i0, hi0⟩ := hΓ
      have hi0MS : ¬ InMS (⟨σ, T⟩ : AlgState J M) i0 := by
        intro h
        have : i0 ∈ MS := by simp only [hMS, Finset.mem_filter, Finset.mem_univ, true_and]; exact h
        rw [he] at this
        simp at this
      have hns : ¬ IsSmall p jnew := by
        intro hs
        exact hno jnew i0 ⟨.small, hjJT, ⟨hi0, show σ jnew ≠ some i0 by rw [hnone]; simp⟩, Or.inl ⟨hs, hi0MS⟩⟩
      unfold aux_ep_zeta
      split_ifs with hb hm
      · norm_num
      · norm_num
      · exact absurd ((aux_ep_small_iff p jnew).mpr ⟨hb, hm⟩) hns
    · have hacc := aux_ep_acc σ T (fun i => aux_ep_Z p σ i - 1) ?_ ?_ T.length T [] (by simp) le_rfl
      · have h2 := hacc.2 hne
        have h3 : ∑ i ∈ MS, W i = ∑ i ∈ MS, aux_ep_Z p σ i := Finset.sum_congr rfl hWZ
        rw [Finset.sum_sub_distrib] at h2
        have h4 := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ.filter (fun j => σ j = none)) =>
          hznn j)
        linarith
      · intro T1 B T2 hdec hBk i hBm
        exact (hI.small T1 B T2 hdec hBk i hBm).2.1
      · intro T1 B T2 hdec hBk i hBm
        obtain ⟨ha, -, hc⟩ := hI.small T1 B T2 hdec hBk i hBm
        rcases hc with hc | ⟨j', i', h1, h2, h3, h4, h5, h6, h7, h8⟩
        · left; linarith
        · right
          rcases T2 with _ | ⟨B', T3⟩
          · exfalso
            apply hno j' i'
            refine ⟨.small, ?_, ⟨h3, h4⟩, Or.inl ⟨h2, ?_⟩⟩
            · obtain ⟨B₀, hB₀, hjB₀⟩ := ha j' h1
              exact ⟨B₀, by dsimp only; rw [show T = T1 ++ [B] from hdec]; exact hB₀, hjB₀⟩
            · rw [show T = T1 ++ [B] from hdec]; exact h5
          · obtain ⟨hB'k, i₂, hB'm, q, hq, hq9, hZ2, hq7⟩ := h8 B' T3 rfl
            refine ⟨B', T3, rfl, hB'k, i₂, hB'm, by linarith, ?_⟩
            show 0 < aux_ep_Z p σ i - 1 + (aux_ep_Z p σ i₂ - 1)
            rcases h7 with h | h
            · linarith
            · by_cases hpj : p j' < 7/17
              · have := hq7 (by linarith)
                linarith
              · push_neg at hpj
                linarith
  rw [hy, hz, hWsplit]
  linarith

theorem aux_ep_swap (S : M → Finset (Finset J)) (x : M → Finset J → ℝ) (z : J → ℝ) :
    ∑ j, z j * ∑ i, ∑ C ∈ (S i).filter (fun C => j ∈ C), x i C
      = ∑ i, ∑ C ∈ S i, x i C * ∑ j ∈ C, z j := by
  simp_rw [Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  simp [mul_comm]

theorem aux_ep_weak_duality (Γ : J → Finset M) (p : J → ℝ) (y : M → ℝ) (z : J → ℝ)
    (hy : ∀ i, 0 ≤ y i) (hz : ∀ j, 0 ≤ z j)
    (hC : ∀ i, ∀ C ∈ configs Γ p 1 i, ∑ j ∈ C, z j ≤ y i)
    (hLP : CLPFeasible Γ p 1) : ∑ j, z j ≤ ∑ i, y i := by
  obtain ⟨x, hx0, hx1, hx2⟩ := hLP
  have h1 : ∑ j, z j ≤ ∑ j, z j * ∑ i, ∑ C ∈ (configs Γ p 1 i).filter (fun C => j ∈ C), x i C := by
    refine Finset.sum_le_sum (fun j _ => ?_)
    have := mul_le_mul_of_nonneg_left (hx2 j) (hz j)
    linarith
  rw [aux_ep_swap] at h1
  have h2 : ∑ i, ∑ C ∈ configs Γ p 1 i, x i C * ∑ j ∈ C, z j ≤ ∑ i, y i := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    calc ∑ C ∈ configs Γ p 1 i, x i C * ∑ j ∈ C, z j
        ≤ ∑ C ∈ configs Γ p 1 i, x i C * y i :=
          Finset.sum_le_sum (fun C hCm => mul_le_mul_of_nonneg_left (hC i C hCm) (hx0 i C))
      _ = (∑ C ∈ configs Γ p 1 i, x i C) * y i := by rw [Finset.sum_mul]
      _ ≤ 1 * y i := mul_le_mul_of_nonneg_right (hx1 i) (hy i)
      _ = y i := one_mul _
  linarith

end RestrictedAssignment.Svensson

open RestrictedAssignment.Svensson

theorem solution {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]
    (Γ : J → Finset M) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hLP : CLPFeasible Γ p 1)
    (σ0 : J → Option M) (jnew : J) (hσ0 : Valid Γ p σ0) (hjnew : σ0 jnew = none)
    (s : AlgState J M) (hs : Reachable Γ p σ0 jnew s) (hloop : s.σ jnew = none) :
    ∃ j i, IsPotentialMove Γ p s j i := by
  by_contra hno
  push_neg at hno
  have hp1 := aux_ep_p_le_one Γ p hp hLP
  have hI := aux_ep_inv_reach Γ p hp hp1 σ0 jnew hσ0 s hs hloop
  obtain ⟨σ, T⟩ := s
  have h48 := aux_ep_claim48 Γ p hp hp1 jnew σ T hI hloop (aux_ep_Γ_nonempty Γ p hLP jnew) hno
  have hwd := aux_ep_weak_duality Γ p (yStar Γ p ⟨σ, T⟩) (zStar Γ p ⟨σ, T⟩)
    (fun i => by
      unfold yStar
      split_ifs
      · norm_num
      · exact Finset.sum_nonneg (fun j _ => aux_ep_z_nonneg Γ p hp _ j))
    (fun j => aux_ep_z_nonneg Γ p hp _ j)
    (fun i C hC => aux_ep_claim47 Γ p hp hp1 jnew σ T hI hno i C hC) hLP
  linarith
