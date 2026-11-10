-- Prove2me | solution 1 for ShiMatchmaking.Communication.lemma_D_3
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T11:48:56.883407+00:00
-- url     : https://prove2.me/submissions/2031e17f-ac78-42c3-bcef-2f5dda6db8c1

import Definitions.Def_ShiMatchmaking_Communication_Matchmaking

noncomputable section
open ShiMatchmaking.Communication

abbrev dJ0 : ℝ := 1 / 2
abbrev dI0 : ℝ := 1 / ((64 : ℝ) * dJ0)

def bb0 : Blackboard (Agents 64) (fun _ => Fin 64 → Bool) (Outcome 64) where
  first := Sum.inl 0
  control := fun h => if h.length = 1 then Sum.inl (Sum.inr 0) else Sum.inr default
  send := fun a loc h =>
    match a with
    | Sum.inl _ => if loc 0 then [true] else []
    | Sum.inr _ =>
      if h = [[true]] then
        if loc 0 then [] else [false]
      else
        [true, false]

private lemma bb0_terminates (y : (a : Agents 64) → Fin 64 → Bool) :
    bb0.Terminates y := by
  refine ⟨1, default, ?_⟩
  simp [bb0, Blackboard.historyAt]

private lemma bb0_find_eq_one (y : (a : Agents 64) → Fin 64 → Bool) :
    @Nat.find _ (Classical.decPred _) (bb0_terminates y) = 1 := by
  classical
  have hle : Nat.find (bb0_terminates y) ≤ 1 := by
    refine Nat.find_min' (bb0_terminates y) ⟨default, ?_⟩
    simp [bb0, Blackboard.historyAt]
  have hne0 : Nat.find (bb0_terminates y) ≠ 0 := by
    intro h0
    have hspec : ∃ o, bb0.control (bb0.historyAt y (Nat.find (bb0_terminates y))) = Sum.inr o :=
      Nat.find_spec (bb0_terminates y)
    rw [h0] at hspec
    rcases hspec with ⟨o, ho⟩
    revert ho
    simp [bb0, Blackboard.historyAt]
  omega

private lemma bb0_helper (b c : Bool) :
    ([if b then [true] else [],
      if [if b then [true] else []] = [[true]] then
        if c then [] else [false]
      else [true, false]] : List Message).flatten =
    if b && c then [true] else [true, false] := by
  cases b <;> cases c <;> rfl

private lemma bb0_transcript (ω : Profile 64) :
    bb0.transcript (privateInput ω) =
      if ω.1 0 0 && ω.2 0 0 then [true] else [true, false] := by
  classical
  unfold Blackboard.transcript Blackboard.history
  rw [dif_pos (bb0_terminates (privateInput ω)), bb0_find_eq_one]
  exact bb0_helper (ω.1 0 0) (ω.2 0 0)

def proto0 : MatchmakingProtocol 64 dI0 dJ0 where
  protocol := bb0
  terminates := fun ω _ => bb0_terminates (privateInput ω)

private lemma marketMass_pos (ω : Profile 64) : 0 < marketMass 64 dI0 dJ0 ω := by
  unfold marketMass bernoulliProduct
  refine mul_pos (Finset.prod_pos fun ij _ => ?_) (Finset.prod_pos fun ij _ => ?_)
  · split_ifs <;> norm_num [dI0, dJ0]
  · split_ifs <;> norm_num [dJ0]

private lemma probability_pos_of_mem {Ω : Type} [Fintype Ω] (w : Ω → ℝ) (E : Ω → Prop)
    (hw : ∀ ω, 0 < w ω) (ω0 : Ω) (hω0 : E ω0) : 0 < probability w E := by
  classical
  unfold probability
  have hle : (if E ω0 then w ω0 else 0) ≤ ∑ ω : Ω, if E ω then w ω else 0 := by
    refine Finset.single_le_sum (f := fun ω : Ω => if E ω then w ω else 0) (fun ω _ => ?_) (Finset.mem_univ ω0)
    split_ifs
    · exact le_of_lt (hw ω)
    · exact le_rfl
  rw [if_pos hω0] at hle
  exact lt_of_lt_of_le (hw ω0) hle

private lemma conditionalMass_of_const {Ω Z : Type} [Fintype Ω] [DecidableEq Z] (w : Ω → ℝ) (f : Ω → Z)
    (E : Ω → Prop) (z0 z : Z) (hprob : 0 < probability w E) (hf : ∀ ω, E ω → f ω = z0) :
    conditionalMass w f E z = if z = z0 then 1 else 0 := by
  classical
  unfold conditionalMass
  by_cases hz : z = z0
  · subst hz
    rw [if_pos rfl]
    have h1 : probability w (fun ω => E ω ∧ f ω = z) = probability w E := by
      unfold probability
      refine Finset.sum_congr rfl fun ω _ => ?_
      by_cases hE : E ω
      · rw [if_pos ⟨hE, hf ω hE⟩, if_pos hE]
      · have hnot : ¬ (E ω ∧ f ω = z) := fun h => hE h.1
        rw [if_neg hnot, if_neg hE]
    rw [h1]
    exact div_self (ne_of_gt hprob)
  · rw [if_neg hz]
    have h0 : probability w (fun ω => E ω ∧ f ω = z) = 0 := by
      unfold probability
      refine Finset.sum_eq_zero fun ω _ => ?_
      rw [if_neg]
      rintro ⟨hE, hEq⟩
      exact hz (hEq.symm.trans (hf ω hE))
    rw [h0, zero_div]

private lemma rangeL1_ge_of_mem {Ω Z : Type} [Fintype Ω] (f : Ω → Z) (p q : Z → ℝ) (ω0 : Ω) :
    |p (f ω0) - q (f ω0)| ≤ rangeL1 f p q := by
  classical
  unfold rangeL1
  exact Finset.single_le_sum (f := fun z : Z => |p z - q z|) (fun z _ => abs_nonneg (p z - q z))
    (Finset.mem_image.mpr ⟨ω0, Finset.mem_univ ω0, rfl⟩)

private lemma rangeL1_self {Ω Z : Type} [Fintype Ω] (f : Ω → Z) (p : Z → ℝ) :
    rangeL1 f p p = 0 := by
  classical
  simp [rangeL1]

private lemma pairLaw_eq (a b : Bool) (z : Message) :
    proto0.pairLaw 0 0 a b z =
      if z = (if a && b then [true] else [true, false]) then 1 else 0 := by
  unfold MatchmakingProtocol.pairLaw
  refine conditionalMass_of_const (marketMass 64 dI0 dJ0) proto0.transcript
    (fun ω => ω.1 0 0 = a ∧ ω.2 0 0 = b) (if a && b then [true] else [true, false]) z ?_ ?_
  · exact probability_pos_of_mem (marketMass 64 dI0 dJ0)
      (fun ω => ω.1 0 0 = a ∧ ω.2 0 0 = b) marketMass_pos (fun _ _ => a, fun _ _ => b) ⟨rfl, rfl⟩
  · rintro ω ⟨ha, hb⟩
    unfold MatchmakingProtocol.transcript proto0
    rw [bb0_transcript, ha, hb]

set_option linter.unusedVariables false in
theorem solution : ¬ (∀ (n : ℕ) (hn : 64 ≤ n) (dJ : ℝ) (hdlo : 1 / Real.sqrt (n : ℝ) ≤ dJ) (hdhi : dJ ≤ 1 / 2) (P : MatchmakingProtocol n (1 / ((n : ℝ) * dJ)) dJ) (i j : Fin n), (1 / 2 : ℝ) * rangeL1 P.transcript (P.pairLaw i j true true) (P.pairLaw i j false false) ≤ rangeL1 P.transcript (P.pairLaw i j true false) (P.pairLaw i j false false) + rangeL1 P.transcript (P.pairLaw i j false true) (P.pairLaw i j false false)) := by
  intro H
  have hdlo : 1 / Real.sqrt (64 : ℝ) ≤ dJ0 := by
    have hsqrt : Real.sqrt (64 : ℝ) = 8 := by
      rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [hsqrt]
    norm_num [dJ0]
  have h := H 64 le_rfl dJ0 hdlo le_rfl proto0 0 0
  have h10 : proto0.pairLaw 0 0 true false = proto0.pairLaw 0 0 false false := by
    ext z
    rw [pairLaw_eq, pairLaw_eq]
    rfl
  have h01 : proto0.pairLaw 0 0 false true = proto0.pairLaw 0 0 false false := by
    ext z
    rw [pairLaw_eq, pairLaw_eq]
    rfl
  rw [h10, h01, rangeL1_self, add_zero] at h
  let ω11 : Profile 64 := (fun _ _ => true, fun _ _ => true)
  have htr11 : proto0.transcript ω11 = [true] := by
    unfold MatchmakingProtocol.transcript proto0
    rw [bb0_transcript]
    rfl
  have hlhs := rangeL1_ge_of_mem proto0.transcript (proto0.pairLaw 0 0 true true)
    (proto0.pairLaw 0 0 false false) ω11
  rw [htr11, pairLaw_eq, pairLaw_eq] at hlhs
  have h1 : |(if ([true] : Message) = (if true && true then [true] else [true, false]) then (1 : ℝ) else 0) -
      (if ([true] : Message) = (if false && false then [true] else [true, false]) then (1 : ℝ) else 0)| = 1 := by
    simp
  rw [h1] at hlhs
  linarith
