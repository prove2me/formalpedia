-- Prove2me | solution 1 for PersistClust.Count.proof_thm_4_8_partition_count_sep
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-09T10:28:25.462314+00:00
-- url     : https://prove2.me/submissions/06ddd47f-0ece-4c02-ada2-4f363231a1fa

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram

/-!
# Theorem 4.8, partition child 1 — `prominentCount` equals the separated region count

Under `IsDiagramLike D`, `0 ≤ d₁`, `IsSeparated D d₁ d₂` and `d₁ < d₂`, the multiplicity
`prominentCount D d₂` (defined as the number of copies of `D` lying in the closed half-plane
`Δ^S_{d₂}`) equals the number of copies lying in `Δ^S_{d₂} ∩ Λ^E_{d₂}`.

The two defining sets differ only by the extra open half-plane condition `Λ^E_{d₂}`
(birth `> d₂`). The proof is the set-equality

  `{q | q.2 < D q.1 ∧ q.1.2 ≤ q.1.1 − d₂}`
    = `{q | q.2 < D q.1 ∧ q.1 ∈ Δ^S_{d₂} ∩ Λ^E_{d₂}}`.

The forward inclusion is the whole content: for a copy `q` with `q.2 < D q.1` (so `D q.1 ≠ 0`)
and `q.1 ∈ Δ^S_{d₂}`, separation places `q.1` either in `Δ^N_{d₁}` or in `Δ^S_{d₂} ∩ Λ^E_{d₂}`.
In the second case `Λ^E_{d₂}` is immediate. In the first case `Δ^N_{d₁}` (birth `− d₁ < death`)
together with `Δ^S_{d₂}` (death `≤ birth − d₂`) forces `birth − d₁ < birth − d₂`, hence
`d₂ < d₁`, contradicting `d₁ < d₂`; the degenerate `±∞` births are ruled out by the same
inequality (a `⊥` birth makes `Δ^S_{d₂}` force `death = ⊥ < birth = ⊥`, impossible; a `⊤` birth
makes `Δ^N_{d₁}` read `⊤ < death`, impossible). So the first case cannot occur.
-/

open PersistClust.Count

/-- A point cannot lie simultaneously in `Δ^N_{d₁}` (birth − d₁ < death) and in
`Δ^S_{d₂}` (death ≤ birth − d₂) when `d₁ < d₂`: together they give `birth − d₁ < birth − d₂`,
i.e. `d₂ < d₁`, a contradiction. Degenerate births `±∞` are excluded by the same arithmetic. -/
theorem partition_sep_conflict {u b : EReal} {d₁ d₂ : ℝ} (hd12 : d₁ < d₂)
    (hN : u - ((d₁ : ℝ) : EReal) < b) (hS : b ≤ u - ((d₂ : ℝ) : EReal)) : False := by
  induction u with
  | bot =>
    -- birth = ⊥: Δ^S_{d₂} forces death ≤ ⊥ − d₂ = ⊥, so death = ⊥,
    -- but Δ^N_{d₁} reads ⊥ − d₁ = ⊥ < ⊥, impossible.
    rw [EReal.bot_sub] at hS
    have hb : b = ⊥ := le_bot_iff.mp hS
    rw [hb, EReal.bot_sub] at hN
    exact absurd hN (lt_irrefl ⊥)
  | coe x =>
    -- finite birth: the two inequalities give (x − d₁) < (x − d₂), hence d₂ < d₁.
    rw [← EReal.coe_sub] at hN
    rw [← EReal.coe_sub] at hS
    have h3 := lt_of_lt_of_le hN hS
    rw [EReal.coe_lt_coe_iff] at h3
    linarith
  | top =>
    -- birth = ⊤: Δ^N_{d₁} reads ⊤ − d₁ = ⊤ < death, impossible (death ≤ ⊤).
    rw [EReal.top_sub_coe] at hN
    exact absurd hN (not_lt_of_ge le_top)

theorem solution
    (D : EReal × EReal → ℕ∞) (hD : IsDiagramLike D)
    (d₁ d₂ : ℝ) (hd₁ : 0 ≤ d₁) (hsep : IsSeparated D d₁ d₂) (hd12 : d₁ < d₂) :
    prominentCount D d₂ =
      {q : (EReal × EReal) × ℕ | (q.2 : ℕ∞) < D q.1 ∧ q.1 ∈ DeltaS d₂ ∩ LamE d₂}.encard := by
  -- unfold the defining set of `prominentCount` and reduce to a set equality.
  show {q : (EReal × EReal) × ℕ | (q.2 : ℕ∞) < D q.1 ∧ q.1.2 ≤ q.1.1 - (d₂ : EReal)}.encard =
        {q : (EReal × EReal) × ℕ | (q.2 : ℕ∞) < D q.1 ∧ q.1 ∈ DeltaS d₂ ∩ LamE d₂}.encard
  refine congrArg (fun s : Set ((EReal × EReal) × ℕ) => s.encard) ?_
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, DeltaS, LamE]
  constructor
  · -- forward: prominentCount region ⊆ Δ^S_{d₂} ∩ Λ^E_{d₂}
    rintro ⟨hq, hS⟩
    refine ⟨hq, hS, ?_⟩
    -- D q.1 ≠ 0 because q.2 < D q.1 and 0 ≤ q.2.
    have hDq : D q.1 ≠ 0 := ne_of_gt (lt_of_le_of_lt (Nat.cast_le.mpr (Nat.zero_le _)) hq)
    -- separation: q.1 ∈ Δ^N_{d₁} ∨ (q.1 ∈ Δ^S_{d₂} ∧ q.1 ∈ Λ^E_{d₂})
    rcases hsep q.1 hDq with hN | ⟨-, hE⟩
    · -- Δ^N_{d₁} branch is incompatible with Δ^S_{d₂} when d₁ < d₂.
      have hN' : q.1.1 - ((d₁ : ℝ) : EReal) < q.1.2 := by simpa [DeltaN] using hN
      exact (partition_sep_conflict hd12 hN' hS).elim
    · -- second branch: Λ^E_{d₂} gives birth > d₂ directly.
      exact hE
  · -- backward: trivial, Δ^S_{d₂} ∩ Λ^E_{d₂} ⊆ Δ^S_{d₂}.
    rintro ⟨hq, hS, hE⟩
    exact ⟨hq, hS⟩
