-- Prove2me | solution 1 for PandoraOrder.Tree.claim_2
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T11:07:54.1015+00:00
-- url     : https://prove2.me/submissions/e98dd326-62e1-46ae-b453-0bbfdf85492c

import Definitions.Def_PandoraOrder_Tree_Contracts

open PandoraOrder.Tree

@[reducible] noncomputable def instClaim2 : Instance 1 where
  size _ := 1
  law _ := ⟨fun _ => 1, fun _ => by norm_num, by simp⟩
  reward _ _ := 0
  reward_nonneg _ _ := le_rfl
  cost _ := 1
  cost_nonneg _ := zero_le_one

noncomputable def openFirstPolicy : Policy 1
  | [] => pureAction (some 0)
  | _ :: _ => pureAction none

private lemma admissible_openFirstPolicy :
    Admissible (lineConstraint ([0] : List (Fin 1))) openFirstPolicy := by
  intro h _ b hb
  cases h with
  | nil =>
    fin_cases b
    exact ⟨by simp, List.prefix_refl [0]⟩
  | cons hd tl =>
    exfalso
    apply hb
    simp [openFirstPolicy, pureAction]

private lemma value_eq_sub_one (π : Policy 1) (x : ℝ) (hx : 0 ≤ x)
    (hopen : (π []).prob (some 0) = 1) :
    value instClaim2 π x = x - 1 := by
  have hsum := (π []).sum_eq_one
  rw [Fintype.sum_option, Fin.sum_univ_one, hopen] at hsum
  have hnone : (π []).prob none = 0 := by linarith
  unfold value expectedRun
  rw [Fin.sum_univ_one, Fin.sum_univ_one]
  simp only [hnone, zero_mul, zero_add, hopen, one_mul, List.nil_append]
  change payoff instClaim2 x [(0, 0)] = x - 1
  unfold payoff
  simp [instClaim2, max_eq_left hx]

private lemma openingValue_instClaim2 (x : ℝ) (hx : 0 ≤ x) :
    openingValue instClaim2 0 [] x = x - 1 := by
  unfold openingValue
  have hset : {v | ∃ π : Policy 1, Admissible (lineConstraint ([0] : List (Fin 1))) π ∧
      (π []).prob (some 0) = 1 ∧ value instClaim2 π x = v} = {x - 1} := by
    ext v
    constructor
    · rintro ⟨π, _, hopen, rfl⟩
      exact value_eq_sub_one π x hx hopen
    · rintro rfl
      have hopen : (openFirstPolicy []).prob (some 0) = 1 := by
        simp [openFirstPolicy, pureAction]
      exact ⟨openFirstPolicy, admissible_openFirstPolicy, hopen,
        value_eq_sub_one openFirstPolicy x hx hopen⟩
  rw [hset, csSup_singleton]

theorem solution : ¬ (∀ {n : ℕ} (I : Instance n) (b : Fin n) (L : List (Fin n))
    (_hL : (b :: L).Nodup),
    IsLeast {x : ℝ | 0 ≤ x ∧ lineValue I (b :: L) x = x} (threshold I (b :: L)) ∧
    (∀ x : ℝ, 0 ≤ x →
      BddAbove {v | ∃ π : Policy n, Admissible (lineConstraint (b :: L)) π ∧
        value I π x = v} ∧
      (∃ π : Policy n, Admissible (lineConstraint (b :: L)) π ∧ Deterministic π ∧
        value I π x = lineValue I (b :: L) x) ∧
      (∀ π : Policy n, Admissible (lineConstraint (b :: L)) π →
        value I π x = lineValue I (b :: L) x →
        (value I π x - x = 0 ↔ lineValue I (b :: L) x = x))) ∧
    (0 < threshold I (b :: L) →
      ∃ π : Policy n, Admissible (lineConstraint (b :: L)) π ∧ Deterministic π ∧
        (π []).prob (some b) = 1 ∧
        value I π (threshold I (b :: L)) = threshold I (b :: L)) ∧
    openingValue I b L (threshold I (b :: L)) = threshold I (b :: L)) := by
  intro h
  have hL : ([0] : List (Fin 1)).Nodup := by decide
  have hinst := h instClaim2 0 [] hL
  have hthresh_nonneg : 0 ≤ threshold instClaim2 [0] := hinst.1.1.1
  have hopen_eq : openingValue instClaim2 0 [] (threshold instClaim2 [0]) =
      threshold instClaim2 [0] := hinst.2.2.2
  rw [openingValue_instClaim2 (threshold instClaim2 [0]) hthresh_nonneg] at hopen_eq
  linarith
