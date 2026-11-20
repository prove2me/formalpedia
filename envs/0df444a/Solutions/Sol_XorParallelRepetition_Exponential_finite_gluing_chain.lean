-- Prove2me | solution 1 for XorParallelRepetition.Exponential.finite_gluing_chain
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:28:45.231184+00:00
-- url     : https://prove2.me/submissions/a509d464-18eb-411b-acbd-b0103be665c1

import Mathlib
import Definitions.Def_XorParallelRepetition_Exponential_XorGames
import Definitions.Def_XorParallelRepetition_Exponential_Contradiction
import Definitions.Def_XorParallelRepetition_Exponential_Gluing
import Theorems.Thm_XorParallelRepetition_Exponential_strict_lex_descent
universe u

section
set_option autoImplicit false

namespace XorParallelRepetition.Dev.Chain

open XorParallelRepetition.Exponential


/-- The finite set of sequences with entries at most `N`. -/
noncomputable def boxSet (N : ℕ) : Finset (Lex (Fin (N + 1) → ℕ)) :=
  (Finset.univ : Finset (Fin (N + 1) → Fin (N + 1))).image fun f => toLex fun j => (f j : ℕ)

theorem mem_boxSet {N : ℕ} (h : Lex (Fin (N + 1) → ℕ)) (hh : ∀ j, ofLex h j ≤ N) :
    h ∈ boxSet N := by
  refine Finset.mem_image.2 ⟨fun j => ⟨ofLex h j, Nat.lt_succ_of_le (hh j)⟩, Finset.mem_univ _, ?_⟩
  rfl

open Classical in
/-- The rank of a sequence: the number of elements of the box strictly below it. -/
noncomputable def rank (N : ℕ) (h : Lex (Fin (N + 1) → ℕ)) : ℕ :=
  ((boxSet N).filter fun g => g < h).card

open Classical in
theorem rank_lt {N : ℕ} {g h : Lex (Fin (N + 1) → ℕ)} (hg : g ∈ boxSet N) (hlt : g < h) :
    rank N g < rank N h := by
  unfold rank
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_of_subset ?_ |>.2 ⟨g, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hx.2.trans hlt⟩
  · simp [hg, hlt]
  · simp only [Finset.mem_filter, not_and]
    intro _ h2
    exact absurd h2 (lt_irrefl g)

open Classical in
theorem rank_le (N : ℕ) (h : Lex (Fin (N + 1) → ℕ)) : rank N h ≤ (boxSet N).card := by
  unfold rank
  exact Finset.card_filter_le _ _

variable {p : ℕ} {ι : Type}

theorem readingSeq_le [Fintype ι] {Ψ : GeneralizedXorGame.{u} p ι} {N : ℕ}
    (R : OrderedContradiction Ψ N) (i : ι) (j : Fin (N + 1)) :
    ofLex (R.readingSeq i) j ≤ N := by
  classical
  unfold OrderedContradiction.readingSeq
  refine le_trans (FreeGroup.reduce.red.sublist.length_le) ?_
  refine le_trans (List.length_take_le' _ _) ?_
  simp [signedWord]

theorem maxReadingSeq_le [Fintype ι] {Ψ : GeneralizedXorGame.{u} p ι} {N : ℕ}
    (R : OrderedContradiction Ψ N) (j : Fin (N + 1)) :
    ofLex R.maxReadingSeq j ≤ N := by
  unfold OrderedContradiction.maxReadingSeq
  split_ifs with h
  · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' h R.readingSeq
    rw [hi]
    exact readingSeq_le R i j
  · simp

theorem heightParam_mem [Fintype ι] (Ψ : GeneralizedXorGame.{u} p ι) (N : ℕ)
    (h : HasOrderedContradiction Ψ N) : heightParam Ψ N h ∈ boxSet N := by
  apply mem_boxSet
  have hm := (wellFounded_lt (α := Lex (Fin (N + 1) → ℕ))).min_mem
    (Set.range fun R : OrderedContradiction Ψ N => R.maxReadingSeq)
    (Set.range_nonempty_iff_nonempty.2 h)
  obtain ⟨R, hR⟩ := hm
  intro j
  unfold heightParam
  rw [← hR]
  exact maxReadingSeq_le R j

theorem phase_zero' : phase p 0 = 1 := by
  simp [phase]

/-- A glued game with an ordered contradiction has two targets. -/
theorem glue_hasTwoTargets [DecidableEq ι] (Φ : GeneralizedXorGame.{u} p ι) (I : Finset ι)
    (N : ℕ) (h : HasOrderedContradiction (Φ.glue I) N) : (Φ.glue I).HasTwoTargets := by
  obtain ⟨R⟩ := h
  -- some challenge has nonzero target
  have hex : ∃ j, (R.challenge j).2 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply R.rhs_ne_one
    apply Finset.prod_eq_one
    intro j _
    rw [hcon j, mul_zero, phase_zero']
  obtain ⟨j, hj⟩ := hex
  obtain ⟨ω, hω⟩ := Φ.μ.support_nonempty
  have hmem : Φ.glueChallenge I ω ω ∈ (Φ.glue I).μ.support := by
    show _ ∈ (Φ.μ.bindOnSupport _).support
    rw [PMF.mem_support_bindOnSupport_iff]
    refine ⟨ω, hω, ?_⟩
    rw [PMF.support_map]
    refine ⟨ω, ?_, rfl⟩
    unfold GeneralizedXorGame.conditional
    rw [PMF.support_filter]
    exact ⟨fun _ _ => rfl, hω⟩
  refine ⟨R.challenge j, R.mem_support j, Φ.glueChallenge I ω ω, hmem, ?_⟩
  simpa [GeneralizedXorGame.glueChallenge] using hj

theorem main [Fact p.Prime] (N : ℕ) : ∀ (m : ℕ) (G : PackedGame.{u} p)
    (hc : HasOrderedContradiction G.game N), rank N (heightParam G.game N hc) ≤ m →
    (Nonempty G.Player ∨ G.game.HasTwoTargets) →
    ∃ (T : ℕ) (chain : Fin (T + 1) → PackedGame.{u} p),
        T ≤ m ∧
        chain 0 = G ∧
        (∀ i : Fin T, ∃ I : Finset (chain i.castSucc).Player,
          I.Nonempty ∧ chain i.succ = (chain i.castSucc).glue I) ∧
        IsEmpty (chain (Fin.last T)).Player ∧
        (chain (Fin.last T)).game.HasTwoTargets := by
  intro m
  induction m with
  | zero =>
    intro G hc hr hne
    by_cases hP : Nonempty G.Player
    · exfalso
      obtain ⟨I, -, h', hlt⟩ := strict_lex_descent G.game N hc
      have := rank_lt (heightParam_mem _ N h') hlt
      omega
    · have h2 : G.game.HasTwoTargets := hne.resolve_left hP
      refine ⟨0, fun _ => G, le_refl _, rfl, fun i => i.elim0, not_nonempty_iff.1 hP, h2⟩
  | succ m ih =>
    intro G hc hr hne
    by_cases hP : Nonempty G.Player
    · obtain ⟨I, hI, h', hlt⟩ := strict_lex_descent G.game N hc
      have hrk : rank N (heightParam (G.glue I).game N h') < rank N (heightParam G.game N hc) :=
        rank_lt (heightParam_mem _ N h') hlt
      obtain ⟨T, chain, hT, h0, hstep, hemp, htt⟩ :=
        ih (G.glue I) h' (by omega) (Or.inr (glue_hasTwoTargets G.game I N h'))
      refine ⟨T + 1, Fin.cons (α := fun _ => PackedGame.{u} p) G chain, by omega, rfl, ?_, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun k => ?_) i
        · refine ⟨I, hI, ?_⟩
          show chain 0 = G.glue I
          exact h0
        · obtain ⟨J, hJ, hk⟩ := hstep k
          exact ⟨J, hJ, hk⟩
      · rw [← Fin.succ_last]
        exact hemp
      · rw [← Fin.succ_last]
        exact htt
    · have h2 : G.game.HasTwoTargets := hne.resolve_left hP
      refine ⟨0, fun _ => G, by omega, rfl, fun i => i.elim0, not_nonempty_iff.1 hP, h2⟩

end XorParallelRepetition.Dev.Chain

namespace XorParallelRepetition.Exponential


theorem chk_finite_gluing_chain :
    ∃ B : ℕ → ℕ, ∀ {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]
      (Ψ : GeneralizedXorGame.{u} p ι) (N : ℕ),
      HasOrderedContradiction Ψ N → (Nonempty ι ∨ Ψ.HasTwoTargets) →
      ∃ (T : ℕ) (chain : Fin (T + 1) → PackedGame.{u} p),
        T ≤ B N ∧
        chain 0 = { Player := ι, game := Ψ } ∧
        (∀ i : Fin T, ∃ I : Finset (chain i.castSucc).Player,
          I.Nonempty ∧ chain i.succ = (chain i.castSucc).glue I) ∧
        IsEmpty (chain (Fin.last T)).Player ∧
        (chain (Fin.last T)).game.HasTwoTargets := by
  refine ⟨fun N => (XorParallelRepetition.Dev.Chain.boxSet N).card, ?_⟩
  intro p _ ι _ _ Ψ N hc hne
  exact XorParallelRepetition.Dev.Chain.main N _ { Player := ι, game := Ψ } hc
    (XorParallelRepetition.Dev.Chain.rank_le N _) hne

end XorParallelRepetition.Exponential
end

theorem solution : type_of% @XorParallelRepetition.Exponential.chk_finite_gluing_chain := @XorParallelRepetition.Exponential.chk_finite_gluing_chain
