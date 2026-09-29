-- Prove2me | solution 1 for RestrictedAssignment.Svensson.extendSchedule_terminates
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:40:35.332814+00:00
-- url     : https://prove2.me/submissions/31aba257-8140-4f29-a9af-aa8c03d7ac8e

import Mathlib
import Definitions.Def_RestrictedAssignment_Svensson_configLP
import Definitions.Def_RestrictedAssignment_Svensson_extendSchedule

namespace RestrictedAssignment.Svensson

open Classical

set_option linter.unusedSectionVars false

instance aux_ts_fintypeKind : Fintype BlockerKind :=
  ⟨{BlockerKind.small, BlockerKind.big, BlockerKind.medium}, by intro x; cases x <;> simp⟩

section

variable {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]
variable (Γ : J → Finset M) (p : J → ℝ)

/-- The successor state produced by one iteration, as in `Step`. -/
noncomputable def aux_ts_next (s : AlgState J M) (j : J) (i : M) (k : ℕ) : AlgState J M :=
  if IsValidMove Γ p s j i then
    ⟨Function.update s.σ j (some i), s.T.take k⟩
  else if IsPotentialMoveOf Γ p s j i .small ∨ IsPotentialMoveOf Γ p s j i .hugeToSmall then
    ⟨s.σ, s.T ++ [⟨Finset.univ.filter (fun j' => s.σ j' = some i) \ jobsT s,
      some i, BlockerKind.small⟩]⟩
  else if IsPotentialMoveOf Γ p s j i .medLargeToBig ∨
      IsPotentialMoveOf Γ p s j i .hugeToBig then
    ⟨s.σ, s.T ++ [⟨Finset.univ.filter (fun j' => s.σ j' = some i ∧ IsBig p j'),
      some i, BlockerKind.big⟩]⟩
  else
    ⟨s.σ, s.T ++ [⟨Finset.univ.filter (fun j' => s.σ j' = some i ∧ IsMedium p j'),
      some i, BlockerKind.medium⟩]⟩

omit [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M] in
lemma aux_ts_ms_mt {s : AlgState J M} {i : M} (h : InMS s i) : InMT s i := by
  obtain ⟨B, hB, -, h2⟩ := h; exact ⟨B, hB, h2⟩

omit [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M] in
lemma aux_ts_mb_mt {s : AlgState J M} {i : M} (h : InMB s i) : InMT s i := by
  obtain ⟨B, hB, -, h2⟩ := h; exact ⟨B, hB, h2⟩

lemma aux_ts_pm_notMS {s : AlgState J M} {j : J} {i : M} (h : IsPotentialMove Γ p s j i) :
    ¬ InMS s i := by
  intro hms
  have hmt := aux_ts_ms_mt hms
  obtain ⟨t, ht⟩ := h
  cases t <;> simp only [IsPotentialMoveOf] at ht <;> tauto

lemma aux_ts_pm_MB {s : AlgState J M} {j : J} {i : M} (h : IsPotentialMove Γ p s j i)
    (hmb : InMB s i) : IsSmall p j := by
  have hmt := aux_ts_mb_mt hmb
  obtain ⟨t, ht⟩ := h
  cases t <;> simp only [IsPotentialMoveOf] at ht <;> tauto

lemma aux_ts_pm_MT {s : AlgState J M} {j : J} {i : M} (h : IsPotentialMove Γ p s j i)
    (hmt : InMT s i) : ¬ IsMedium p j := by
  intro hmed
  have h1 : ¬ IsSmall p j := fun h => by
    unfold IsSmall at h; unfold IsMedium at hmed; linarith [hmed.1]
  have h2 : ¬ IsLarge p j := fun h => by
    unfold IsLarge at h; unfold IsMedium at hmed; linarith [hmed.2, h.1]
  obtain ⟨t, ht⟩ := h
  cases t <;> simp only [IsPotentialMoveOf] at ht <;> tauto

lemma aux_ts_big_notMB {s : AlgState J M} {j : J} {i : M}
    (h : IsPotentialMoveOf Γ p s j i .medLargeToBig ∨ IsPotentialMoveOf Γ p s j i .hugeToBig) :
    ¬ InMB s i := by
  intro hmb
  have := aux_ts_mb_mt hmb
  simp only [IsPotentialMoveOf] at h
  tauto

lemma aux_ts_pm_move {s : AlgState J M} {j : J} {i : M} (h : IsPotentialMove Γ p s j i) :
    IsMove Γ s j i := by
  obtain ⟨t, ht⟩ := h
  cases t <;> exact ht.2.1

lemma aux_ts_hm_of {s : AlgState J M} {j : J} {i : M} (hpm : IsPotentialMove Γ p s j i)
    (h2 : ¬ (IsPotentialMoveOf Γ p s j i .small ∨ IsPotentialMoveOf Γ p s j i .hugeToSmall))
    (h3 : ¬ (IsPotentialMoveOf Γ p s j i .medLargeToBig ∨ IsPotentialMoveOf Γ p s j i .hugeToBig)) :
    IsPotentialMoveOf Γ p s j i .hugeToMedium := by
  obtain ⟨t, ht⟩ := hpm
  cases t
  · exact absurd (Or.inl ht) h2
  · exact absurd (Or.inl ht) h3
  · exact absurd (Or.inr ht) h2
  · exact absurd (Or.inr ht) h3
  · exact ht

lemma aux_ts_st_lt {s : AlgState J M} {j : J} {i : M}
    (h : IsPotentialMoveOf Γ p s j i .small) : p j < 14 / 17 := by
  simp only [IsPotentialMoveOf] at h
  obtain ⟨-, -, h | h | h⟩ := h
  · have := h.1; unfold IsSmall at this; linarith
  · have := h.1; unfold IsMedium at this; linarith [this.2]
  · have := h.1; unfold IsLarge at this; linarith [this.2]

lemma aux_ts_mlb_lt {s : AlgState J M} {j : J} {i : M}
    (h : IsPotentialMoveOf Γ p s j i .medLargeToBig) : p j < 14 / 17 := by
  simp only [IsPotentialMoveOf] at h
  obtain ⟨-, -, h | h, -⟩ := h
  · have := h.1; unfold IsMedium at this; linarith [this.2]
  · have := h.1; unfold IsLarge at this; linarith [this.2]

omit [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M] in
lemma aux_ts_eqT {s s' : AlgState J M} (h : s'.T = s.T) (i : M) (j : J) :
    (InMS s' i ↔ InMS s i) ∧ (InMT s' i ↔ InMT s i) ∧ (InMB s' i ↔ InMB s i) ∧
      (InJT s' j ↔ InJT s j) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [InMS, InMT, InMB, InJT, h]

/-- Global invariants of the states of a run. -/
structure aux_ts_GInv (s : AlgState J M) : Prop where
  valid : Valid Γ p s.σ
  mach : ∀ B ∈ s.T, ∀ j ∈ B.jobs, s.σ j = B.machine
  disj : s.T.Pairwise (fun B B' => Disjoint B.jobs B'.jobs)
  med : ∀ B ∈ s.T, B.kind = BlockerKind.medium → ∀ j ∈ B.jobs, IsMedium p j
  rel : s.T.Pairwise (fun B B' => B'.machine ≠ none ∧
    ∀ i, B'.machine = some i → B.machine = some i →
      B.kind ≠ BlockerKind.small ∧ B.kind ≠ B'.kind)

lemma aux_ts_init (σ0 : J → Option M) (jnew : J) (hσ0 : Valid Γ p σ0) (hjnew : σ0 jnew = none) :
    aux_ts_GInv Γ p (initState σ0 jnew) := by
  refine ⟨hσ0, ?_, ?_, ?_, ?_⟩
  · intro B hB j hj
    simp only [initState, List.mem_singleton] at hB
    subst hB
    simp only [Finset.mem_singleton] at hj
    subst hj
    simpa [initState] using hjnew
  · simp [initState]
  · intro B hB
    simp only [initState, List.mem_singleton] at hB
    subst hB
    simp
  · simp [initState]

lemma aux_ts_inv_step {jnew : J} {s s' : AlgState J M} (hs : aux_ts_GInv Γ p s)
    (h : Step Γ p jnew s s') : aux_ts_GInv Γ p s' := by
  obtain ⟨-, j, i, hpm, -, k, hk, hjk, rfl⟩ := h
  rw [List.get_eq_getElem] at hjk
  have hnms := aux_ts_pm_notMS Γ p hpm
  split_ifs with hv h2 h3
  · refine ⟨hv.2, ?_, hs.disj.sublist (List.take_sublist _ _), ?_,
      hs.rel.sublist (List.take_sublist _ _)⟩
    · intro B hB j' hj'
      have hBT := List.mem_of_mem_take hB
      by_cases hjj : j' = j
      · subst hjj
        exfalso
        obtain ⟨m, hm, rfl⟩ := List.mem_take_iff_getElem.1 hB
        have := List.pairwise_iff_getElem.1 hs.disj m k (by omega) hk (by omega)
        exact Finset.disjoint_left.1 this hj' hjk
      · simp only [Function.update_of_ne hjj]
        exact hs.mach B hBT j' hj'
    · intro B hB
      exact hs.med B (List.mem_of_mem_take hB)
  · refine ⟨hs.valid, ?_, ?_, ?_, ?_⟩
    · intro B hB j' hj'
      rcases List.mem_append.1 hB with hB | hB
      · exact hs.mach B hB j' hj'
      · simp only [List.mem_singleton] at hB
        subst hB
        simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hj'
        exact hj'.1
    · rw [List.pairwise_append]
      refine ⟨hs.disj, by simp, ?_⟩
      intro B hB X hX
      simp only [List.mem_singleton] at hX
      subst hX
      rw [Finset.disjoint_left]
      intro j' hj'1 hj'2
      simp only [jobsT, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hj'2
      exact hj'2.2 ⟨B, hB, hj'1⟩
    · intro B hB hk'
      rcases List.mem_append.1 hB with hB | hB
      · exact hs.med B hB hk'
      · simp only [List.mem_singleton] at hB
        subst hB
        simp at hk'
    · rw [List.pairwise_append]
      refine ⟨hs.rel, by simp, ?_⟩
      intro B hB X hX
      simp only [List.mem_singleton] at hX
      subst hX
      refine ⟨by simp, ?_⟩
      intro i' hi' hBi
      simp only [Option.some.injEq] at hi'
      subst hi'
      have : B.kind ≠ BlockerKind.small := fun hks => hnms ⟨B, hB, hks, hBi⟩
      exact ⟨this, this⟩
  · have hnmb := aux_ts_big_notMB Γ p h3
    refine ⟨hs.valid, ?_, ?_, ?_, ?_⟩
    · intro B hB j' hj'
      rcases List.mem_append.1 hB with hB | hB
      · exact hs.mach B hB j' hj'
      · simp only [List.mem_singleton] at hB
        subst hB
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj'
        exact hj'.1
    · rw [List.pairwise_append]
      refine ⟨hs.disj, by simp, ?_⟩
      intro B hB X hX
      simp only [List.mem_singleton] at hX
      subst hX
      rw [Finset.disjoint_left]
      intro j' hj'1 hj'2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj'2
      have hBm : B.machine = some i := by rw [← hs.mach B hB j' hj'1, hj'2.1]
      cases hBk : B.kind
      · exact hnms ⟨B, hB, hBk, hBm⟩
      · exact hnmb ⟨B, hB, hBk, hBm⟩
      · have := hs.med B hB hBk j' hj'1
        have h4 := hj'2.2
        unfold IsMedium at this; unfold IsBig at h4; linarith [this.2]
    · intro B hB hk'
      rcases List.mem_append.1 hB with hB | hB
      · exact hs.med B hB hk'
      · simp only [List.mem_singleton] at hB
        subst hB
        simp at hk'
    · rw [List.pairwise_append]
      refine ⟨hs.rel, by simp, ?_⟩
      intro B hB X hX
      simp only [List.mem_singleton] at hX
      subst hX
      refine ⟨by simp, ?_⟩
      intro i' hi' hBi
      simp only [Option.some.injEq] at hi'
      subst hi'
      refine ⟨fun hks => hnms ⟨B, hB, hks, hBi⟩, fun hkb => hnmb ⟨B, hB, hkb, hBi⟩⟩
  · have hhm := aux_ts_hm_of Γ p hpm h2 h3
    have hnmt : ¬ InMT s i := hhm.2.2.2.1
    refine ⟨hs.valid, ?_, ?_, ?_, ?_⟩
    · intro B hB j' hj'
      rcases List.mem_append.1 hB with hB | hB
      · exact hs.mach B hB j' hj'
      · simp only [List.mem_singleton] at hB
        subst hB
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj'
        exact hj'.1
    · rw [List.pairwise_append]
      refine ⟨hs.disj, by simp, ?_⟩
      intro B hB X hX
      simp only [List.mem_singleton] at hX
      subst hX
      rw [Finset.disjoint_left]
      intro j' hj'1 hj'2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj'2
      have hBm : B.machine = some i := by rw [← hs.mach B hB j' hj'1, hj'2.1]
      exact hnmt ⟨B, hB, hBm⟩
    · intro B hB hk'
      rcases List.mem_append.1 hB with hB | hB
      · exact hs.med B hB hk'
      · simp only [List.mem_singleton] at hB
        subst hB
        intro j' hj'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj'
        exact hj'.2
    · rw [List.pairwise_append]
      refine ⟨hs.rel, by simp, ?_⟩
      intro B hB X hX
      simp only [List.mem_singleton] at hX
      subst hX
      refine ⟨by simp, ?_⟩
      intro i' hi' hBi
      simp only [Option.some.injEq] at hi'
      subst hi'
      exact absurd ⟨B, hB, hBi⟩ hnmt

lemma aux_ts_len_le {s : AlgState J M} (hs : aux_ts_GInv Γ p s) :
    s.T.length ≤ Fintype.card (Option M × BlockerKind) := by
  have hnd : (s.T.map (fun B => (B.machine, B.kind))).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    refine hs.rel.imp ?_
    rintro B B' ⟨hne, hrel⟩ heq
    obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.1 hne
    simp only [Prod.mk.injEq] at heq
    exact (hrel i hi (heq.1.trans hi)).2 heq.2
  simpa using hnd.length_le_card

lemma aux_ts_shape {jnew : J} {s s' : AlgState J M} (h : Step Γ p jnew s s') :
    ∃ j i k, ∃ hk : k < s.T.length, j ∈ s.T[k].jobs ∧ IsPotentialMove Γ p s j i ∧
      ((IsValidMove Γ p s j i ∧ s' = ⟨Function.update s.σ j (some i), s.T.take k⟩) ∨
       (s'.σ = s.σ ∧ ∃ Y : Blocker J M, s'.T = s.T ++ [Y])) := by
  obtain ⟨-, j, i, hpm, -, k, hk, hjk, rfl⟩ := h
  refine ⟨j, i, k, hk, by simpa using hjk, hpm, ?_⟩
  split_ifs with hv h2 h3
  · exact Or.inl ⟨hv, rfl⟩
  · exact Or.inr ⟨rfl, _, rfl⟩
  · exact Or.inr ⟨rfl, _, rfl⟩
  · exact Or.inr ⟨rfl, _, rfl⟩

lemma aux_ts_traj {jnew : J} (f : ℕ → AlgState J M) (hstep : ∀ n, Step Γ p jnew (f n) (f (n+1)))
    (hinv : ∀ n, aux_ts_GInv Γ p (f n)) (a b ℓ : ℕ) (X : Blocker J M) (i1 : M)
    (hX : X.machine = some i1) (hℓ : 1 ≤ ℓ) (hLa : (f a).T.length = ℓ)
    (h1σ : (f (a+1)).σ = (f a).σ) (h1T : (f (a+1)).T = (f a).T ++ [X]) (hab : a + 1 < b)
    (hLb : (f b).T.length = ℓ) (hmid : ∀ c, a < c → c < b → ℓ < (f c).T.length) :
    (f b).T = (f a).T ∧ (∃ j ∈ X.jobs, (f b).σ j ≠ some i1) ∧
    (∀ j', (f b).σ j' = some i1 → (f a).σ j' ≠ some i1 →
      X.kind ≠ BlockerKind.small ∧ ¬ IsMedium p j' ∧ (X.kind = BlockerKind.big → IsSmall p j')) ∧
    (∀ j', (f b).σ j' = (f a).σ j' ∨ ∃ i ∈ Γ j', (f b).σ j' ≠ some i ∧
      ¬ ∃ B ∈ (f a).T, B.kind = BlockerKind.small ∧ B.machine = some i) := by
  have hpre : ∀ n, a + 1 ≤ n → n < b → (f n).T.take (ℓ+1) = (f a).T ++ [X] := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      intro _
      rw [h1T]
      apply List.take_of_length_le
      simp [hLa]
    | succ n hn ih =>
      intro hnb
      have hLn := hmid n (by omega) (by omega)
      have hLn1 := hmid (n+1) (by omega) hnb
      obtain ⟨j, i, k, hk, -, -, hsh⟩ := aux_ts_shape Γ p (hstep n)
      rcases hsh with ⟨-, heq⟩ | ⟨-, Y, hY⟩
      · rw [heq] at hLn1 ⊢
        dsimp only at hLn1 ⊢
        simp only [List.length_take] at hLn1
        rw [List.take_take, ← ih (by omega)]
        congr 1
        omega
      · rw [hY, List.take_append_of_le_length (by omega), ih (by omega)]
  have htake : ∀ n, a + 1 ≤ n → n < b → (f n).T.take ℓ = (f a).T := by
    intro n hn hnb
    have := congrArg (List.take ℓ) (hpre n hn hnb)
    rw [List.take_take, List.take_left' hLa] at this
    rwa [show min ℓ (ℓ+1) = ℓ by omega] at this
  have hXmem : ∀ n, a + 1 ≤ n → n < b → X ∈ (f n).T := by
    intro n hn hnb
    have : X ∈ (f n).T.take (ℓ+1) := by rw [hpre n hn hnb]; simp
    exact List.mem_of_mem_take this
  have hkey : ∀ n, a + 1 ≤ n → n ≤ b →
      (∀ j', (f n).σ j' = some i1 → (f a).σ j' ≠ some i1 →
        X.kind ≠ BlockerKind.small ∧ ¬ IsMedium p j' ∧ (X.kind = BlockerKind.big → IsSmall p j')) ∧
      (∀ j', (f n).σ j' = (f a).σ j' ∨ ∃ i ∈ Γ j', (f n).σ j' ≠ some i ∧
        ¬ ∃ B ∈ (f a).T, B.kind = BlockerKind.small ∧ B.machine = some i) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      intro _
      refine ⟨fun j' h1 h2 => ?_, fun j' => Or.inl (by rw [h1σ])⟩
      rw [h1σ] at h1
      exact absurd h1 h2
    | succ n hn ih =>
      intro hnb
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      have hLn1 : ℓ ≤ (f (n+1)).T.length := by
        rcases Nat.lt_or_ge (n+1) b with h | h
        · exact (hmid (n+1) (by omega) h).le
        · rw [show n + 1 = b by omega, hLb]
      obtain ⟨j, i, k, hk, hjk, hpm, hsh⟩ := aux_ts_shape Γ p (hstep n)
      rcases hsh with ⟨hv, heq⟩ | ⟨hσ, Y, hY⟩
      · have hkℓ : ℓ ≤ k := by
          rw [heq] at hLn1
          dsimp only at hLn1
          simp only [List.length_take] at hLn1
          omega
        have hinvn := hinv n
        have hrel0 := List.pairwise_iff_getElem.1 hinvn.rel 0 k (by omega) hk (by omega)
        obtain ⟨im, him⟩ := Option.ne_none_iff_exists'.1 hrel0.1
        have hσj : (f n).σ j = some im := by
          rw [hinvn.mach _ (List.getElem_mem hk) j hjk, him]
        have hσ1 : (f (n+1)).σ = Function.update (f n).σ j (some i) := by rw [heq]
        have hmv := aux_ts_pm_move Γ p hpm
        have hii : i ≠ im := fun h => hmv.2 (by rw [hσj, h])
        have hΓ : im ∈ Γ j := hinvn.valid.1 j im hσj
        have hnoMS : ¬ ∃ B ∈ (f a).T, B.kind = BlockerKind.small ∧ B.machine = some im := by
          rintro ⟨B, hB, hBk, hBm⟩
          rw [← htake n hn (by omega)] at hB
          obtain ⟨m, hm, rfl⟩ := List.mem_take_iff_getElem.1 hB
          have := (List.pairwise_iff_getElem.1 hinvn.rel m k (by omega) hk (by omega)).2 im him hBm
          exact this.1 hBk
        have hXn := hXmem n hn (by omega)
        refine ⟨?_, ?_⟩
        · intro j' h1 h2
          by_cases hjj : j' = j
          · subst hjj
            rw [hσ1, Function.update_self] at h1
            obtain rfl := Option.some_injective _ h1
            refine ⟨?_, ?_, ?_⟩
            · intro hks
              exact aux_ts_pm_notMS Γ p hpm ⟨X, hXn, hks, hX⟩
            · exact aux_ts_pm_MT Γ p hpm ⟨X, hXn, hX⟩
            · intro hkb
              exact aux_ts_pm_MB Γ p hpm ⟨X, hXn, hkb, hX⟩
          · rw [hσ1, Function.update_of_ne hjj] at h1
            exact ih1 j' h1 h2
        · intro j'
          by_cases hjj : j' = j
          · subst hjj
            right
            refine ⟨im, hΓ, ?_, hnoMS⟩
            rw [hσ1, Function.update_self]
            intro h
            exact hii (Option.some_injective _ h)
          · rw [hσ1, Function.update_of_ne hjj]
            exact ih2 j'
      · refine ⟨fun j' h1 h2 => ih1 j' (by rw [← hσ]; exact h1) h2, fun j' => ?_⟩
        rw [hσ]
        exact ih2 j'
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
  have hLn : ℓ < (f n).T.length := hmid n (by omega) (by omega)
  obtain ⟨k1, k2⟩ := hkey (n+1) (by omega) le_rfl
  obtain ⟨j, i, k, hk, hjk, hpm, hsh⟩ := aux_ts_shape Γ p (hstep n)
  rcases hsh with ⟨hv, heq⟩ | ⟨hσ, Y, hY⟩
  · have hkℓ : k = ℓ := by
      rw [heq] at hLb
      dsimp only at hLb
      simp only [List.length_take] at hLb
      omega
    have hXk : (f n).T[k] = X := by
      have h2 := congrArg (fun l => l[k]?) (hpre n (by omega) (by omega))
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hk,
        List.getElem?_append_right (by omega), hLa, show k - ℓ = 0 by omega] at h2
      simpa using h2
    have hjX : j ∈ X.jobs := hXk ▸ hjk
    have hσj : (f n).σ j = some i1 := by
      rw [(hinv n).mach _ (List.getElem_mem hk) j hjk, hXk, hX]
    have hmv := aux_ts_pm_move Γ p hpm
    refine ⟨?_, ⟨j, hjX, ?_⟩, k1, k2⟩
    · rw [heq]
      dsimp only
      rw [hkℓ, htake n (by omega) (by omega)]
    · rw [heq]
      dsimp only
      rw [Function.update_self]
      intro h
      apply hmv.2
      rw [hσj, ← h]
  · exfalso
    rw [hY] at hLb
    simp at hLb
    omega

lemma aux_ts_pload_lt (hp : ∀ j, 0 < p j) {σ σ' : J → Option M} {i : M} {j : J}
    (hmono : ∀ j', σ' j' = some i → σ j' = some i) (hj : σ j = some i) (hj' : σ' j ≠ some i) :
    pload p σ' i < pload p σ i := by
  unfold pload
  apply Finset.sum_lt_sum_of_subset (i := j)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hmono x hx
  · simp [hj]
  · simp [hj']
  · exact hp j
  · intro x _ _
    exact (hp x).le

lemma aux_ts_nobig {σa σb : J → Option M} {i1 : M} {j : J} (hv : Valid Γ p σa)
    (hja : σa j = some i1) (hjbig : IsBig p j) (hjb : σb j ≠ some i1)
    (F : ∀ j', σb j' = some i1 → σa j' ≠ some i1 → IsSmall p j') :
    ∀ j', σb j' = some i1 → ¬ IsBig p j' := by
  intro j' h1 hbig
  have hj'a : σa j' = some i1 := by
    by_contra hne
    have := F j' h1 hne
    unfold IsSmall at this; unfold IsBig at hbig; linarith
  have := Finset.card_le_one.1 (hv.2 i1).1 j'
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj'a, hbig⟩) j
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, hja, hjbig⟩)
  subst this
  exact hjb h1

lemma aux_ts_cycle {jnew : J} (f : ℕ → AlgState J M) (hstep : ∀ n, Step Γ p jnew (f n) (f (n+1)))
    (hinv : ∀ n, aux_ts_GInv Γ p (f n)) (hp : ∀ j, 0 < p j) (a b ℓ : ℕ) (j1 : J) (i1 : M)
    (k1 : ℕ) (hk1 : k1 < (f a).T.length) (hjk1 : j1 ∈ ((f a).T.get ⟨k1, hk1⟩).jobs)
    (hpm1 : IsPotentialMove Γ p (f a) j1 i1) (heq1 : f (a+1) = aux_ts_next Γ p (f a) j1 i1 k1)
    (hab : a < b) (hLa : (f a).T.length = ℓ) (hLb : (f b).T.length = ℓ)
    (hmid : ∀ c, a < c → c < b → ℓ < (f c).T.length) :
    IsPotentialMove Γ p (f b) j1 i1 ∧ moveVal Γ p (f b) j1 i1 < moveVal Γ p (f a) j1 i1 := by
  have hjk1' : j1 ∈ (f a).T[k1].jobs := by simpa using hjk1
  have hℓ : 1 ≤ ℓ := by omega
  have hLa1 : ℓ ≤ (f (a+1)).T.length := by
    rcases Nat.lt_or_ge (a+1) b with h | h
    · exact (hmid (a+1) (by omega) h).le
    · rw [show a + 1 = b by omega, hLb]
  have hv : ¬ IsValidMove Γ p (f a) j1 i1 := by
    intro hv
    rw [heq1, aux_ts_next, if_pos hv] at hLa1
    dsimp only at hLa1
    simp only [List.length_take] at hLa1
    omega
  have common : ∀ X : Blocker J M, f (a+1) = ⟨(f a).σ, (f a).T ++ [X]⟩ → X.machine = some i1 →
      (f b).T = (f a).T ∧ (f b).σ j1 = (f a).σ j1 ∧
      (∃ j ∈ X.jobs, (f a).σ j = some i1 ∧ (f b).σ j ≠ some i1) ∧
      (∀ j', (f b).σ j' = some i1 → (f a).σ j' ≠ some i1 →
        X.kind ≠ BlockerKind.small ∧ ¬ IsMedium p j' ∧ (X.kind = BlockerKind.big → IsSmall p j')) ∧
      Si Γ p (f b) i1 ⊆ Si Γ p (f a) i1 ∧ Mi p (f b) i1 ⊆ Mi p (f a) i1 := by
    intro X hXe hX
    have h1σ : (f (a+1)).σ = (f a).σ := by rw [hXe]
    have h1T : (f (a+1)).T = (f a).T ++ [X] := by rw [hXe]
    have hab' : a + 1 < b := by
      rcases Nat.lt_or_ge (a+1) b with h | h
      · exact h
      · exfalso
        have : b = a + 1 := by omega
        subst this
        rw [h1T] at hLb
        simp [hLa] at hLb
    obtain ⟨hTb, ⟨j, hjX, hjb⟩, F1, F2⟩ :=
      aux_ts_traj Γ p f hstep hinv a b ℓ X i1 hX hℓ hLa h1σ h1T hab' hLb hmid
    have hσj1 : (f b).σ j1 = (f a).σ j1 := by
      rw [(hinv a).mach _ (List.getElem_mem hk1) j1 hjk1',
        (hinv b).mach _ (by rw [hTb]; exact List.getElem_mem hk1) j1 hjk1']
    have hja : (f a).σ j = some i1 := by
      rw [← h1σ, (hinv (a+1)).mach X (by rw [h1T]; simp) j hjX, hX]
    refine ⟨hTb, hσj1, ⟨j, hjX, hja, hjb⟩, F1, ?_, ?_⟩
    · intro j' hj'
      simp only [Si, Finset.mem_filter, Finset.mem_univ, true_and] at hj' ⊢
      simp only [InS, IsMove, InMS] at hj' ⊢
      obtain ⟨hj'σ, hsm, hall⟩ := hj'
      rcases F2 j' with h | ⟨i, hiΓ, hine, hnms⟩
      · have hσa : (f a).σ j' = some i1 := by rw [← h]; exact hj'σ
        refine ⟨hσa, hsm, fun i hi => ?_⟩
        obtain ⟨B, hB, hB2⟩ := hall i ⟨hi.1, by rw [h]; exact hi.2⟩
        exact ⟨B, by rw [hTb] at hB; exact hB, hB2⟩
      · exfalso
        obtain ⟨B, hB, hB2⟩ := hall i ⟨hiΓ, hine⟩
        exact hnms ⟨B, by rw [hTb] at hB; exact hB, hB2⟩
    · intro j' hj'
      simp only [Mi, Finset.mem_filter, Finset.mem_univ, true_and] at hj' ⊢
      refine ⟨?_, hj'.2⟩
      by_contra hne
      exact (F1 j' hj'.1 hne).2.1 hj'.2
  have hX := heq1
  by_cases hS : IsPotentialMoveOf Γ p (f a) j1 i1 .small
  · rw [aux_ts_next, if_neg hv, if_pos (Or.inl hS)] at hX
    obtain ⟨hTb, hσj1, ⟨j, -, hja, hjb⟩, F1, -, -⟩ := common _ hX rfl
    have hmono : ∀ j', (f b).σ j' = some i1 → (f a).σ j' = some i1 := fun j' h => by
      by_contra hne
      exact (F1 j' h hne).1 rfl
    have hHB : HasBig p (f b) i1 → HasBig p (f a) i1 := fun ⟨j', h1, h2⟩ => ⟨j', hmono j' h1, h2⟩
    obtain ⟨eMS, eMT, eMB, eJT⟩ := aux_ts_eqT hTb i1 j1
    have hSb : IsPotentialMoveOf Γ p (f b) j1 i1 .small := by
      obtain ⟨hjt, hmv, hc⟩ := hS
      refine ⟨eJT.2 hjt, ⟨hmv.1, by rw [hσj1]; exact hmv.2⟩, ?_⟩
      rw [eMS, eMT, eMB]
      rcases hc with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr (Or.inl ⟨h1, h2, fun h => h3 (hHB h)⟩)
      · exact Or.inr (Or.inr ⟨h1, h2, h3, fun h => h4 (hHB h)⟩)
    refine ⟨⟨_, hSb⟩, ?_⟩
    have hva : moveVal Γ p (f a) j1 i1 = toLex (p j1, pload p (f a).σ i1) := by
      rw [moveVal, if_neg hv, if_pos hS]
    rw [hva]
    by_cases hvb : IsValidMove Γ p (f b) j1 i1
    · rw [moveVal, if_pos hvb, Prod.Lex.toLex_lt_toLex]
      left
      exact hp j1
    · rw [moveVal, if_neg hvb, if_pos hSb, Prod.Lex.toLex_lt_toLex]
      right
      exact ⟨rfl, aux_ts_pload_lt p hp hmono hja hjb⟩
  by_cases hML : IsPotentialMoveOf Γ p (f a) j1 i1 .medLargeToBig
  · have hnHS : ¬ IsPotentialMoveOf Γ p (f a) j1 i1 .hugeToSmall := by
      intro h
      have h1 := aux_ts_mlb_lt Γ p hML
      have h2 := h.2.2.1
      unfold IsHuge at h2
      linarith
    rw [aux_ts_next, if_neg hv, if_neg (not_or.2 ⟨hS, hnHS⟩), if_pos (Or.inl hML)] at hX
    obtain ⟨hTb, hσj1, ⟨j, hjX, hja, hjb⟩, F1, -, -⟩ := common _ hX rfl
    have hjbig : IsBig p j := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hjX
      exact hjX.2
    have hnb : ¬ HasBig p (f b) i1 := fun ⟨j', h1, h2⟩ =>
      aux_ts_nobig Γ p (hinv a).valid hja hjbig hjb (fun j' h h' => (F1 j' h h').2.2 rfl) j' h1 h2
    obtain ⟨eMS, eMT, eMB, eJT⟩ := aux_ts_eqT hTb i1 j1
    have hSb : IsPotentialMoveOf Γ p (f b) j1 i1 .small := by
      obtain ⟨hjt, hmv, hc, -⟩ := hML
      refine ⟨eJT.2 hjt, ⟨hmv.1, by rw [hσj1]; exact hmv.2⟩, ?_⟩
      rw [eMS, eMT, eMB]
      rcases hc with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
      · exact Or.inr (Or.inl ⟨h1, h2, hnb⟩)
      · exact Or.inr (Or.inr ⟨h1, h2, h3, hnb⟩)
    refine ⟨⟨_, hSb⟩, ?_⟩
    have hva : moveVal Γ p (f a) j1 i1 = toLex ((2:ℝ), (0:ℝ)) := by
      rw [moveVal, if_neg hv, if_neg hS, if_pos hML]
    rw [hva]
    by_cases hvb : IsValidMove Γ p (f b) j1 i1
    · rw [moveVal, if_pos hvb, Prod.Lex.toLex_lt_toLex]
      left
      norm_num
    · rw [moveVal, if_neg hvb, if_pos hSb, Prod.Lex.toLex_lt_toLex]
      left
      have := aux_ts_st_lt Γ p hSb
      show p j1 < 2
      linarith
  by_cases hHS : IsPotentialMoveOf Γ p (f a) j1 i1 .hugeToSmall
  · rw [aux_ts_next, if_neg hv, if_pos (Or.inr hHS)] at hX
    obtain ⟨hTb, hσj1, ⟨j, -, hja, hjb⟩, F1, hSi, hMi⟩ := common _ hX rfl
    have hmono : ∀ j', (f b).σ j' = some i1 → (f a).σ j' = some i1 := fun j' h => by
      by_contra hne
      exact (F1 j' h hne).1 rfl
    obtain ⟨eMS, eMT, eMB, eJT⟩ := aux_ts_eqT hTb i1 j1
    have hva : moveVal Γ p (f a) j1 i1 = toLex ((3:ℝ), pload p (f a).σ i1) := by
      rw [moveVal, if_neg hv, if_neg hS, if_neg hML, if_pos hHS]
    obtain ⟨hjt, hmv, hhuge, hnmt, hnhb, hsum⟩ := hHS
    have hsub := Finset.sum_le_sum_of_subset_of_nonneg (f := p)
      (Finset.union_subset_union hSi hMi) (fun x _ _ => (hp x).le)
    have hHSb : IsPotentialMoveOf Γ p (f b) j1 i1 .hugeToSmall :=
      ⟨eJT.2 hjt, ⟨hmv.1, by rw [hσj1]; exact hmv.2⟩, hhuge, fun h => hnmt (eMT.1 h),
        fun ⟨j', h1, h2⟩ => hnhb ⟨j', hmono j' h1, h2⟩, by linarith⟩
    refine ⟨⟨_, hHSb⟩, ?_⟩
    rw [hva]
    by_cases hvb : IsValidMove Γ p (f b) j1 i1
    · rw [moveVal, if_pos hvb, Prod.Lex.toLex_lt_toLex]
      left
      norm_num
    · have hnS : ¬ IsPotentialMoveOf Γ p (f b) j1 i1 .small := fun h => by
        have := aux_ts_st_lt Γ p h; unfold IsHuge at hhuge; linarith
      have hnML : ¬ IsPotentialMoveOf Γ p (f b) j1 i1 .medLargeToBig := fun h => by
        have := aux_ts_mlb_lt Γ p h; unfold IsHuge at hhuge; linarith
      rw [moveVal, if_neg hvb, if_neg hnS, if_neg hnML, if_pos hHSb, Prod.Lex.toLex_lt_toLex]
      right
      exact ⟨rfl, aux_ts_pload_lt p hp hmono hja hjb⟩
  by_cases hHB : IsPotentialMoveOf Γ p (f a) j1 i1 .hugeToBig
  · rw [aux_ts_next, if_neg hv, if_neg (not_or.2 ⟨hS, hHS⟩), if_pos (Or.inr hHB)] at hX
    obtain ⟨hTb, hσj1, ⟨j, hjX, hja, hjb⟩, F1, hSi, hMi⟩ := common _ hX rfl
    have hjbig : IsBig p j := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hjX
      exact hjX.2
    have hnb : ¬ HasBig p (f b) i1 := fun ⟨j', h1, h2⟩ =>
      aux_ts_nobig Γ p (hinv a).valid hja hjbig hjb (fun j' h h' => (F1 j' h h').2.2 rfl) j' h1 h2
    obtain ⟨eMS, eMT, eMB, eJT⟩ := aux_ts_eqT hTb i1 j1
    have hva : moveVal Γ p (f a) j1 i1 = toLex ((4:ℝ), (0:ℝ)) := by
      rw [moveVal, if_neg hv, if_neg hS, if_neg hML, if_neg hHS, if_pos hHB]
    obtain ⟨hjt, hmv, hhuge, hnmt, -, hsum⟩ := hHB
    have hsub := Finset.sum_le_sum_of_subset_of_nonneg (f := p)
      (Finset.union_subset_union hSi hMi) (fun x _ _ => (hp x).le)
    have hHSb : IsPotentialMoveOf Γ p (f b) j1 i1 .hugeToSmall :=
      ⟨eJT.2 hjt, ⟨hmv.1, by rw [hσj1]; exact hmv.2⟩, hhuge, fun h => hnmt (eMT.1 h), hnb,
        by linarith⟩
    refine ⟨⟨_, hHSb⟩, ?_⟩
    rw [hva]
    by_cases hvb : IsValidMove Γ p (f b) j1 i1
    · rw [moveVal, if_pos hvb, Prod.Lex.toLex_lt_toLex]
      left
      norm_num
    · have hnS : ¬ IsPotentialMoveOf Γ p (f b) j1 i1 .small := fun h => by
        have := aux_ts_st_lt Γ p h; unfold IsHuge at hhuge; linarith
      have hnML : ¬ IsPotentialMoveOf Γ p (f b) j1 i1 .medLargeToBig := fun h => by
        have := aux_ts_mlb_lt Γ p h; unfold IsHuge at hhuge; linarith
      rw [moveVal, if_neg hvb, if_neg hnS, if_neg hnML, if_pos hHSb, Prod.Lex.toLex_lt_toLex]
      left
      norm_num
  have hHM := aux_ts_hm_of Γ p hpm1 (not_or.2 ⟨hS, hHS⟩) (not_or.2 ⟨hML, hHB⟩)
  rw [aux_ts_next, if_neg hv, if_neg (not_or.2 ⟨hS, hHS⟩), if_neg (not_or.2 ⟨hML, hHB⟩)] at hX
  obtain ⟨hTb, hσj1, ⟨j, hjX, hja, hjb⟩, F1, hSi, hMi⟩ := common _ hX rfl
  have hjmed : IsMedium p j := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hjX
    exact hjX.2
  have hcard : (Mi p (f b) i1).card < (Mi p (f a) i1).card := by
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset hMi]
    refine ⟨j, ?_, ?_⟩
    · simp only [Mi, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hja, hjmed⟩
    · simp only [Mi, Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun h => hjb h.1
  obtain ⟨eMS, eMT, eMB, eJT⟩ := aux_ts_eqT hTb i1 j1
  have hva : moveVal Γ p (f a) j1 i1 = toLex ((5:ℝ), ((Mi p (f a) i1).card : ℝ)) := by
    rw [moveVal, if_neg hv, if_neg hS, if_neg hML, if_neg hHS, if_neg hHB, if_pos hHM]
  obtain ⟨hjt, hmv, hhuge, hnmt, hsumS, -⟩ := hHM
  have hsubS := Finset.sum_le_sum_of_subset_of_nonneg (f := p) hSi (fun x _ _ => (hp x).le)
  have hjtb := eJT.2 hjt
  have hmvb : IsMove Γ (f b) j1 i1 := ⟨hmv.1, by rw [hσj1]; exact hmv.2⟩
  have hnmtb : ¬ InMT (f b) i1 := fun h => hnmt (eMT.1 h)
  have hnS : ¬ IsPotentialMoveOf Γ p (f b) j1 i1 .small := fun h => by
    have := aux_ts_st_lt Γ p h; unfold IsHuge at hhuge; linarith
  refine ⟨?_, ?_⟩
  · by_cases hle : p j1 + ∑ k ∈ Si Γ p (f b) i1 ∪ Mi p (f b) i1, p k ≤ 1 + R
    · by_cases hb : HasBig p (f b) i1
      · exact ⟨.hugeToBig, hjtb, hmvb, hhuge, hnmtb, hb, hle⟩
      · exact ⟨.hugeToSmall, hjtb, hmvb, hhuge, hnmtb, hb, hle⟩
    · exact ⟨.hugeToMedium, hjtb, hmvb, hhuge, hnmtb, by linarith, not_le.1 hle⟩
  · rw [hva, moveVal]
    split_ifs
    all_goals rw [Prod.Lex.toLex_lt_toLex]
    all_goals first
      | (left; norm_num; done)
      | (right
         refine ⟨rfl, ?_⟩
         show ((Mi p (f b) i1).card : ℝ) < ((Mi p (f a) i1).card : ℝ)
         exact_mod_cast hcard)
      | (exfalso; contradiction)

lemma aux_ts_val_mem (s : AlgState J M) (j : J) (i : M) :
    moveVal Γ p s j i ∈ toLex '' ((insert (0:ℝ) (insert 2 (insert 3 (insert 4 (insert 5
      (Set.range p)))))) ×ˢ (insert (0:ℝ) (Set.range (fun x : (J → Option M) × M => pload p x.1 x.2)
        ∪ Set.range (fun c : Finset J => (c.card : ℝ))))) := by
  unfold moveVal
  split_ifs
  all_goals refine Set.mem_image_of_mem _ (Set.mk_mem_prod ?_ ?_)
  all_goals simp

lemma aux_ts_W_fin :
    (toLex '' ((insert (0:ℝ) (insert 2 (insert 3 (insert 4 (insert 5
      (Set.range p)))))) ×ˢ (insert (0:ℝ) (Set.range (fun x : (J → Option M) × M => pload p x.1 x.2)
        ∪ Set.range (fun c : Finset J => (c.card : ℝ)))))).Finite := by
  apply Set.Finite.image
  apply Set.Finite.prod
  · simp only [Set.finite_insert]
    exact Set.finite_range p
  · rw [Set.finite_insert]
    exact (Set.finite_range _).union (Set.finite_range _)

end

end RestrictedAssignment.Svensson

open RestrictedAssignment.Svensson

theorem solution {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]
    (Γ : J → Finset M) (p : J → ℝ) (hp : ∀ j, 0 < p j)
    (σ0 : J → Option M) (jnew : J) (hσ0 : Valid Γ p σ0) (hjnew : σ0 jnew = none) :
    ¬ ∃ f : ℕ → AlgState J M,
        f 0 = initState σ0 jnew ∧ ∀ n, Step Γ p jnew (f n) (f (n + 1)) := by
  classical
  rintro ⟨f, hf0, hstep⟩
  have hinv : ∀ n, aux_ts_GInv Γ p (f n) := by
    intro n
    induction n with
    | zero => rw [hf0]; exact aux_ts_init Γ p σ0 jnew hσ0 hjnew
    | succ n ih => exact aux_ts_inv_step Γ p ih (hstep n)
  have hch := fun n => (hstep n).2
  choose jj ii hpm hmin kk hkk hjk heq using hch
  have hLK : ∀ n, (f n).T.length ≤ Fintype.card (Option M × BlockerKind) :=
    fun n => aux_ts_len_le Γ p (hinv n)
  have hex : ∃ v, ∀ N, ∃ n, N ≤ n ∧ (f n).T.length ≤ v := ⟨_, fun N => ⟨N, le_rfl, hLK N⟩⟩
  obtain ⟨ℓ, n0, hn0, hR⟩ : ∃ ℓ n0, (∀ n, n0 ≤ n → ℓ ≤ (f n).T.length) ∧
      (∀ N, ∃ n, N ≤ n ∧ n0 ≤ n ∧ (f n).T.length = ℓ) := by
    refine ⟨Nat.find hex, ?_⟩
    have hℓ := Nat.find_spec hex
    obtain ⟨n0, hn0⟩ : ∃ n0, ∀ n, n0 ≤ n → Nat.find hex ≤ (f n).T.length := by
      by_cases h0 : Nat.find hex = 0
      · exact ⟨0, fun n _ => by omega⟩
      · have hm := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
        push_neg at hm
        obtain ⟨n0, hn0⟩ := hm
        exact ⟨n0, fun n hn => by have := hn0 n hn; omega⟩
    refine ⟨n0, hn0, fun N => ?_⟩
    obtain ⟨n, hn, hle⟩ := hℓ (max N n0)
    exact ⟨n, by omega, by omega, le_antisymm hle (hn0 n (by omega))⟩
  let nxt : ℕ → ℕ := fun a => Nat.find (hR (a+1))
  let r : ℕ → ℕ := fun m => Nat.rec (Nat.find (hR 0)) (fun _ a => nxt a) m
  have hr0 : ∀ m, n0 ≤ r m ∧ (f (r m)).T.length = ℓ := by
    intro m
    cases m with
    | zero => exact (Nat.find_spec (hR 0)).2
    | succ m => exact (Nat.find_spec (hR (r m + 1))).2
  let μ : ℕ → Lex (ℝ × ℝ) := fun n => moveVal Γ p (f n) (jj n) (ii n)
  have hdec : ∀ m, μ (r (m+1)) < μ (r m) := by
    intro m
    have hb := Nat.find_spec (hR (r m + 1))
    have hrb : r (m+1) = Nat.find (hR (r m + 1)) := rfl
    have hmid : ∀ c, r m < c → c < r (m+1) → ℓ < (f c).T.length := by
      intro c hac hcb
      rw [hrb] at hcb
      have hnot := Nat.find_min (hR (r m + 1)) hcb
      have hrm := (hr0 m).1
      have h1 := hn0 c (by omega)
      have h3 : (f c).T.length ≠ ℓ := fun h => hnot ⟨by omega, by omega, h⟩
      omega
    have hcyc := aux_ts_cycle Γ p f hstep hinv hp (r m) (r (m+1)) ℓ (jj (r m)) (ii (r m))
      (kk (r m)) (hkk (r m)) (hjk (r m)) (hpm (r m)) (heq (r m)) (by rw [hrb]; omega)
      (hr0 m).2 (hr0 (m+1)).2 hmid
    exact lt_of_le_of_lt (hmin (r (m+1)) _ _ hcyc.1) hcyc.2
  have hanti : StrictAnti (μ ∘ r) := strictAnti_nat_of_succ_lt hdec
  have hfin := aux_ts_W_fin (M := M) p
  apply Set.infinite_range_of_injective hanti.injective
  apply hfin.subset
  rintro _ ⟨m, rfl⟩
  exact aux_ts_val_mem Γ p _ _ _
