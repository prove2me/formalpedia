-- Prove2me | solution 1 for StableMatching.galeShapley_woman_pessimal
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-12T14:59:37.388978+00:00
-- url     : https://prove2.me/submissions/1caa6a81-7651-4ac8-a1dc-dcb06a4aa405

import Mathlib
import Definitions.Def_StableMatching_GaleShapley

set_option autoImplicit false

open StableMatching

/-!
# Shared core library for the Gale–Shapley mission (`StableMatching.GSCore`)

For an arbitrary instance `I : Instance n`:

* round lemmas: `gsRun_zero`, `gsRun_succ`, `gsRound_next`, `gsRound_fiance`, `candidates`,
  `mem_candidates`, `proposal_eq_some`, `proposal_isSome`, `proposal_eq_none_of_engaged`,
  `gsRound_next_of_isSome`, `gsRound_next_of_not_isSome`, `le_gsRound_next`, `gsRound_next_le`,
  `favourite_spec`, `favourite_eq_none`, `favourite_mem`, `exists_favourite_le`,
  `gsRound_fiance_eq_some`, `gsRound_fiance_mem`, `gsRound_fiance_of_mem`,
  `gsRound_fiance_of_proposal`, `gsRound_fiance_of_fiance`;
* the invariant `Inv I s` (fields `fiance_inj` (a), `next_of_fiance` (b), `next_le` (c),
  `proposed` (d)), with `inv_init`, `Inv.gsRound`, `inv_gsRun`, and the derived
  `Inv.next_lt_of_not_engaged` (e);
* monotonicity: `gsRun_next_mono`, `gsRun_fiance_mono`;
* fixpoint: `gsRound_eq_self`, `gsRun_eq_of_all_engaged`;
* termination: `potential`, `gsRun_all_engaged`, `galeShapley_isEngaged`, `gsRun_eq_galeShapley`,
  `inv_galeShapley`;
* the outcome: `exists_isGSOutcome`, `fiance_of_isGSOutcome`, `next_of_isGSOutcome`,
  `isGSOutcome_unique`, `existsUnique_isGSOutcome`;
* stability: `isStable_of_isGSOutcome`, `exists_isGSOutcome_isStable`, `exists_isStable`;
* history facts: `gsRound_galeShapley`, `gsRound_next_eq_succ_iff`, `gsRound_next_eq_self_iff`,
  `proposal_isSome_iff_exists`, `Inv.exists_proposal_of_not_engaged`,
  `exists_proposal_of_lt_next`.

All lemmas take the instance `I` as an explicit argument.
-/

namespace StableMatching.GSCore

variable {n : ℕ} (I : Instance n)

theorem gsRun_zero : I.gsRun 0 = GSState.init n := rfl

theorem gsRun_succ (k : ℕ) : I.gsRun (k + 1) = I.gsRound (I.gsRun k) :=
  Function.iterate_succ_apply' _ _ _

theorem gsRound_next (s : GSState n) (m : Fin n) :
    (I.gsRound s).next m = if (I.proposal s m).isSome then s.next m + 1 else s.next m := rfl

/-- The candidates of woman `w` in a round starting from `s`: this round's suitors and her
current fiancé. -/
def candidates (s : GSState n) (w : Fin n) : Finset (Fin n) :=
  (Finset.univ.filter fun m => I.proposal s m = some w) ∪ (s.fiance w).toFinset

theorem gsRound_fiance (s : GSState n) (w : Fin n) :
    (I.gsRound s).fiance w = I.favourite w (candidates I s w) := rfl

theorem mem_candidates {s : GSState n} {w m : Fin n} :
    m ∈ candidates I s w ↔ I.proposal s m = some w ∨ s.fiance w = some m := by
  simp [candidates, Option.mem_toFinset, eq_comm]

theorem proposal_eq_some {s : GSState n} {m w : Fin n} :
    I.proposal s m = some w ↔ ¬ s.IsEngaged m ∧ s.next m = I.manRank m w := by
  unfold Instance.proposal
  split_ifs with h
  · rw [Option.some_inj, Equiv.symm_apply_eq, Fin.ext_iff]
    simp only [h.1, not_false_eq_true, true_and]
  · simp only [false_iff]
    rintro ⟨h1, h2⟩
    exact h ⟨h1, h2 ▸ (I.manRank m w).isLt⟩

theorem proposal_isSome {s : GSState n} {m : Fin n} :
    (I.proposal s m).isSome ↔ ¬ s.IsEngaged m ∧ s.next m < n := by
  unfold Instance.proposal
  split_ifs with h <;> simp [h]

theorem proposal_eq_none_of_engaged {s : GSState n} {m : Fin n} (h : s.IsEngaged m) :
    I.proposal s m = none := by
  unfold Instance.proposal
  rw [dif_neg (fun h' => h'.1 h)]

theorem gsRound_next_of_isSome {s : GSState n} {m : Fin n} (h : (I.proposal s m).isSome) :
    (I.gsRound s).next m = s.next m + 1 := by
  rw [gsRound_next, if_pos h]

theorem gsRound_next_of_not_isSome {s : GSState n} {m : Fin n}
    (h : ¬ (I.proposal s m).isSome) : (I.gsRound s).next m = s.next m := by
  rw [gsRound_next, if_neg h]

theorem le_gsRound_next (s : GSState n) (m : Fin n) : s.next m ≤ (I.gsRound s).next m := by
  rw [gsRound_next]; split_ifs <;> omega

theorem gsRound_next_le (s : GSState n) (m : Fin n) : (I.gsRound s).next m ≤ s.next m + 1 := by
  rw [gsRound_next]; split_ifs <;> omega

theorem favourite_spec {w m : Fin n} {c : Finset (Fin n)} :
    I.favourite w c = some m ↔ m ∈ c ∧ ∀ m' ∈ c, I.womanRank w m ≤ I.womanRank w m' := by
  unfold Instance.favourite
  split_ifs with h
  · rw [Option.some_inj, Equiv.symm_apply_eq]
    constructor
    · intro hm
      obtain ⟨m0, hm0, hm0e⟩ := Finset.mem_image.1 (Finset.min'_mem _ (h.image (I.womanRank w)))
      have : m0 = m := (I.womanRank w).injective (hm0e.trans hm)
      subst this
      refine ⟨hm0, fun m' hm' => ?_⟩
      rw [← hm]
      exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ hm')
    · rintro ⟨hm, hle⟩
      apply le_antisymm
      · exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ hm)
      · apply Finset.le_min'
        intro y hy
        obtain ⟨m', hm', rfl⟩ := Finset.mem_image.1 hy
        exact hle m' hm'
  · simp only [false_iff, not_and, not_forall]
    intro hm
    exact absurd ⟨m, hm⟩ h

theorem favourite_eq_none {w : Fin n} {c : Finset (Fin n)} :
    I.favourite w c = none ↔ c = ∅ := by
  unfold Instance.favourite
  split_ifs with h
  · simp only [false_iff]
    exact h.ne_empty
  · simp only [true_iff]
    exact Finset.not_nonempty_iff_eq_empty.1 h

theorem favourite_mem {w m : Fin n} {c : Finset (Fin n)} (h : I.favourite w c = some m) :
    m ∈ c := ((favourite_spec I).1 h).1

theorem exists_favourite_le {w m : Fin n} {c : Finset (Fin n)} (hm : m ∈ c) :
    ∃ m', I.favourite w c = some m' ∧ I.womanRank w m' ≤ I.womanRank w m := by
  cases hf : I.favourite w c with
  | none => exact absurd ((favourite_eq_none I).1 hf ▸ hm) (Finset.notMem_empty m)
  | some m' => exact ⟨m', rfl, ((favourite_spec I).1 hf).2 m hm⟩

theorem gsRound_fiance_eq_some {s : GSState n} {w m : Fin n} :
    (I.gsRound s).fiance w = some m ↔
      m ∈ candidates I s w ∧ ∀ m' ∈ candidates I s w, I.womanRank w m ≤ I.womanRank w m' :=
  favourite_spec I

theorem gsRound_fiance_mem {s : GSState n} {w m : Fin n} (h : (I.gsRound s).fiance w = some m) :
    I.proposal s m = some w ∨ s.fiance w = some m :=
  (mem_candidates I).1 (favourite_mem I h)

theorem gsRound_fiance_of_mem {s : GSState n} {w m : Fin n} (hm : m ∈ candidates I s w) :
    ∃ m', (I.gsRound s).fiance w = some m' ∧ I.womanRank w m' ≤ I.womanRank w m :=
  exists_favourite_le I hm

theorem gsRound_fiance_of_proposal {s : GSState n} {w m : Fin n} (h : I.proposal s m = some w) :
    ∃ m', (I.gsRound s).fiance w = some m' ∧ I.womanRank w m' ≤ I.womanRank w m :=
  gsRound_fiance_of_mem I ((mem_candidates I).2 (Or.inl h))

/-- A woman engaged before a round stays engaged, to a man she likes at least as much. -/
theorem gsRound_fiance_of_fiance {s : GSState n} {w m : Fin n} (h : s.fiance w = some m) :
    ∃ m', (I.gsRound s).fiance w = some m' ∧ I.womanRank w m' ≤ I.womanRank w m :=
  gsRound_fiance_of_mem I ((mem_candidates I).2 (Or.inr h))

/-! ## The invariant -/

/-- The invariant of the Gale–Shapley algorithm. -/
structure Inv (I : Instance n) (s : GSState n) : Prop where
  /-- (a) No man is engaged to two women. -/
  fiance_inj : ∀ {w w' m : Fin n}, s.fiance w = some m → s.fiance w' = some m → w = w'
  /-- (b) An engaged man's last proposal went to his fiancée. -/
  next_of_fiance : ∀ {w m : Fin n}, s.fiance w = some m → s.next m = (I.manRank m w : ℕ) + 1
  /-- (c) A man proposes at most `n` times. -/
  next_le : ∀ m : Fin n, s.next m ≤ n
  /-- (d) Every woman a man has proposed to holds someone she likes at least as much. -/
  proposed : ∀ {m w : Fin n}, (I.manRank m w : ℕ) < s.next m →
    ∃ m', s.fiance w = some m' ∧ I.womanRank w m' ≤ I.womanRank w m

theorem inv_init : Inv I (GSState.init n) where
  fiance_inj h := by simp [GSState.init] at h
  next_of_fiance h := by simp [GSState.init] at h
  next_le _ := Nat.zero_le _
  proposed h := by simp [GSState.init] at h

theorem Inv.gsRound {s : GSState n} (hs : Inv I s) : Inv I (I.gsRound s) where
  fiance_inj := by
    intro w w' m h h'
    rcases gsRound_fiance_mem I h with hp | hf <;>
      rcases gsRound_fiance_mem I h' with hp' | hf'
    · exact Option.some_inj.1 (hp.symm.trans hp')
    · exact absurd ⟨w', hf'⟩ ((proposal_eq_some I).1 hp).1
    · exact absurd ⟨w, hf⟩ ((proposal_eq_some I).1 hp').1
    · exact hs.fiance_inj hf hf'
  next_of_fiance := by
    intro w m h
    rcases gsRound_fiance_mem I h with hp | hf
    · have hsome : (I.proposal s m).isSome := by rw [hp]; rfl
      rw [gsRound_next_of_isSome I hsome, ((proposal_eq_some I).1 hp).2]
    · rw [gsRound_next_of_not_isSome I (by rw [proposal_eq_none_of_engaged I ⟨w, hf⟩]; simp)]
      exact hs.next_of_fiance hf
  next_le := by
    intro m
    by_cases h : (I.proposal s m).isSome
    · rw [gsRound_next_of_isSome I h]
      exact ((proposal_isSome I).1 h).2
    · rw [gsRound_next_of_not_isSome I h]
      exact hs.next_le m
  proposed := by
    intro m w hlt
    have key : ∀ m₁, s.fiance w = some m₁ → I.womanRank w m₁ ≤ I.womanRank w m →
        ∃ m', (I.gsRound s).fiance w = some m' ∧ I.womanRank w m' ≤ I.womanRank w m := by
      intro m₁ h₁ hle
      obtain ⟨m', hm', hle'⟩ := gsRound_fiance_of_fiance I h₁
      exact ⟨m', hm', hle'.trans hle⟩
    by_cases h : (I.proposal s m).isSome
    · rw [gsRound_next_of_isSome I h] at hlt
      rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt' | heq
      · obtain ⟨m₁, h₁, hle⟩ := hs.proposed hlt'
        exact key m₁ h₁ hle
      · have hp : I.proposal s m = some w :=
          (proposal_eq_some I).2 ⟨((proposal_isSome I).1 h).1, heq.symm⟩
        exact gsRound_fiance_of_proposal I hp
    · rw [gsRound_next_of_not_isSome I h] at hlt
      obtain ⟨m₁, h₁, hle⟩ := hs.proposed hlt
      exact key m₁ h₁ hle

theorem inv_gsRun (k : ℕ) : Inv I (I.gsRun k) := by
  induction k with
  | zero => exact inv_init I
  | succ k ih => rw [gsRun_succ]; exact ih.gsRound I

/-- (e) An unengaged man has not yet exhausted his list. -/
theorem Inv.next_lt_of_not_engaged {s : GSState n} (hs : Inv I s) {m : Fin n}
    (hm : ¬ s.IsEngaged m) : s.next m < n := by
  by_contra hge
  have hnext : s.next m = n := le_antisymm (hs.next_le m) (not_lt.1 hge)
  have hall : ∀ w, ∃ m', s.fiance w = some m' := by
    intro w
    obtain ⟨m', hm', -⟩ := hs.proposed (m := m) (w := w) (by rw [hnext]; exact (I.manRank m w).isLt)
    exact ⟨m', hm'⟩
  let f : Fin n → Fin n := fun w => (s.fiance w).getD m
  have hf : ∀ w, s.fiance w = some (f w) := by
    intro w
    obtain ⟨m', hm'⟩ := hall w
    simp [f, hm']
  have hinj : Function.Injective f := fun w w' h => hs.fiance_inj (hf w) (h ▸ hf w')
  obtain ⟨w, hw⟩ := (Finite.injective_iff_surjective.1 hinj) m
  exact hm ⟨w, hw ▸ hf w⟩

/-- An engaged man is engaged to exactly one woman. -/
theorem Inv.fiance_eq_of_engaged {s : GSState n} (hs : Inv I s) {w w' m : Fin n}
    (h : s.fiance w = some m) (h' : s.fiance w' = some m) : w = w' := hs.fiance_inj h h'

/-! ## Monotonicity -/

theorem gsRun_next_mono (m : Fin n) {j k : ℕ} (hjk : j ≤ k) :
    (I.gsRun j).next m ≤ (I.gsRun k).next m := by
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => rw [gsRun_succ]; exact ih.trans (le_gsRound_next I _ m)

theorem gsRun_fiance_mono {w m : Fin n} {j k : ℕ} (hjk : j ≤ k)
    (h : (I.gsRun j).fiance w = some m) :
    ∃ m', (I.gsRun k).fiance w = some m' ∧ I.womanRank w m' ≤ I.womanRank w m := by
  induction k, hjk using Nat.le_induction with
  | base => exact ⟨m, h, le_rfl⟩
  | succ k _ ih =>
    obtain ⟨m₁, h₁, hle₁⟩ := ih
    obtain ⟨m₂, h₂, hle₂⟩ := gsRound_fiance_of_fiance I h₁
    exact ⟨m₂, by rw [gsRun_succ]; exact h₂, hle₂.trans hle₁⟩

/-! ## Fixpoint -/

/-- Once every man is engaged, a round changes nothing. -/
theorem gsRound_eq_self {s : GSState n} (h : ∀ m, s.IsEngaged m) : I.gsRound s = s := by
  have hp : ∀ m, I.proposal s m = none := fun m => proposal_eq_none_of_engaged I (h m)
  obtain ⟨nx, fi⟩ := s
  show (⟨_, _⟩ : GSState n) = ⟨nx, fi⟩
  congr 1
  · funext m
    simp [hp m]
  · funext w
    have hc : candidates I ⟨nx, fi⟩ w = (fi w).toFinset := by
      simp [candidates, hp]
    show I.favourite w (candidates I ⟨nx, fi⟩ w) = fi w
    rw [hc]
    cases hfw : fi w with
    | none => exact (favourite_eq_none I).2 rfl
    | some m => exact (favourite_spec I).2 ⟨by simp, fun m' hm' => by simp at hm'; rw [hm']⟩

theorem gsRun_eq_of_all_engaged {j : ℕ} (h : ∀ m, (I.gsRun j).IsEngaged m) {k : ℕ}
    (hjk : j ≤ k) : I.gsRun k = I.gsRun j := by
  induction k, hjk using Nat.le_induction with
  | base => rfl
  | succ k _ ih => rw [gsRun_succ, ih, gsRound_eq_self I h]

/-! ## Termination -/

/-- The potential: the total number of proposals made so far. -/
def potential (s : GSState n) : ℕ := ∑ m, s.next m

/-- If some man is unengaged, the next round strictly increases the potential. -/
theorem potential_gsRound_ge {s : GSState n} (hs : Inv I s) {m : Fin n}
    (hm : ¬ s.IsEngaged m) : potential s + 1 ≤ potential (I.gsRound s) := by
  have hsome : (I.proposal s m).isSome :=
    (proposal_isSome I).2 ⟨hm, hs.next_lt_of_not_engaged I hm⟩
  have : ∑ x, s.next x < ∑ x, (I.gsRound s).next x :=
    Finset.sum_lt_sum (fun x _ => le_gsRound_next I s x)
      ⟨m, Finset.mem_univ _, by rw [gsRound_next_of_isSome I hsome]; omega⟩
  unfold potential
  omega

/-- If some man is unengaged, the potential is less than `n * n`. -/
theorem potential_lt {s : GSState n} (hs : Inv I s) {m : Fin n} (hm : ¬ s.IsEngaged m) :
    potential s < n * n := by
  unfold potential
  calc ∑ x, s.next x < ∑ _x : Fin n, n :=
        Finset.sum_lt_sum (fun x _ => hs.next_le x)
          ⟨m, Finset.mem_univ _, hs.next_lt_of_not_engaged I hm⟩
    _ = n * n := by simp

/-- If some man is unengaged after `k` rounds, at least `k` proposals have been made. -/
theorem le_potential_of_not_engaged {k : ℕ} {m : Fin n} (hm : ¬ (I.gsRun k).IsEngaged m) :
    k ≤ potential (I.gsRun k) := by
  induction k generalizing m with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    by_cases hall : ∀ m', (I.gsRun k).IsEngaged m'
    · exact absurd (by rw [gsRun_eq_of_all_engaged I hall (Nat.le_succ k)]; exact hall m) hm
    · obtain ⟨m', hm'⟩ := not_forall.1 hall
      have h1 := ih hm'
      have h2 := potential_gsRound_ge I (inv_gsRun I k) hm'
      rw [gsRun_succ]
      omega

/-- After `n ^ 2` rounds every man is engaged. -/
theorem gsRun_all_engaged : ∀ m, (I.gsRun (n ^ 2)).IsEngaged m := by
  intro m
  by_contra hm
  have h1 := le_potential_of_not_engaged I hm
  have h2 := potential_lt I (inv_gsRun I _) hm
  have h3 := h1.trans_lt h2
  rw [sq] at h3
  exact lt_irrefl _ h3

theorem galeShapley_isEngaged : ∀ m, I.galeShapley.IsEngaged m := gsRun_all_engaged I

theorem gsRun_eq_galeShapley {k : ℕ} (hk : n ^ 2 ≤ k) : I.gsRun k = I.galeShapley :=
  gsRun_eq_of_all_engaged I (gsRun_all_engaged I) hk

theorem inv_galeShapley : Inv I I.galeShapley := inv_gsRun I _

/-! ## The Gale–Shapley outcome -/

theorem exists_isGSOutcome : ∃ μ : Matching n, I.IsGSOutcome μ := by
  choose f hf using galeShapley_isEngaged I
  have hinj : Function.Injective f := fun m m' hmm' => by
    have h := hf m
    rw [hmm', hf m'] at h
    exact (Option.some_inj.1 h).symm
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), fun m => hf m⟩

theorem fiance_of_isGSOutcome {μ : Matching n} (h : I.IsGSOutcome μ) (w : Fin n) :
    I.galeShapley.fiance w = some (μ.symm w) := by
  simpa using h (μ.symm w)

theorem next_of_isGSOutcome {μ : Matching n} (h : I.IsGSOutcome μ) (m : Fin n) :
    I.galeShapley.next m = (I.manRank m (μ m) : ℕ) + 1 :=
  (inv_galeShapley I).next_of_fiance (h m)

theorem isGSOutcome_unique {μ ν : Matching n} (hμ : I.IsGSOutcome μ) (hν : I.IsGSOutcome ν) :
    μ = ν :=
  Equiv.ext fun m => (inv_galeShapley I).fiance_inj (hμ m) (hν m)

theorem existsUnique_isGSOutcome : ∃! μ : Matching n, I.IsGSOutcome μ := by
  obtain ⟨μ, hμ⟩ := exists_isGSOutcome I
  exact ⟨μ, hμ, fun ν hν => isGSOutcome_unique I hν hμ⟩

/-! ## Stability -/

theorem isStable_of_isGSOutcome {μ : Matching n} (h : I.IsGSOutcome μ) : I.IsStable μ := by
  rintro m w ⟨hm, hw⟩
  unfold Instance.manPrefers at hm
  unfold Instance.womanPrefers at hw
  have hs := inv_galeShapley I
  have hlt : (I.manRank m w : ℕ) < I.galeShapley.next m := by
    rw [hs.next_of_fiance (h m)]
    exact Nat.lt_succ_of_lt (Fin.lt_def.1 hm)
  obtain ⟨m', hm', hle⟩ := hs.proposed hlt
  rw [fiance_of_isGSOutcome I h w] at hm'
  cases Option.some_inj.1 hm'
  exact absurd hw (not_lt.2 hle)

theorem exists_isGSOutcome_isStable : ∃ μ : Matching n, I.IsGSOutcome μ ∧ I.IsStable μ := by
  obtain ⟨μ, hμ⟩ := exists_isGSOutcome I
  exact ⟨μ, hμ, isStable_of_isGSOutcome I hμ⟩

theorem exists_isStable : ∃ μ : Matching n, I.IsStable μ := by
  obtain ⟨μ, -, hμ⟩ := exists_isGSOutcome_isStable I
  exact ⟨μ, hμ⟩

/-! ## Extra history facts -/

theorem gsRound_galeShapley : I.gsRound I.galeShapley = I.galeShapley :=
  gsRound_eq_self I (galeShapley_isEngaged I)

theorem gsRound_next_eq_succ_iff {s : GSState n} {m : Fin n} :
    (I.gsRound s).next m = s.next m + 1 ↔ (I.proposal s m).isSome := by
  by_cases h : (I.proposal s m).isSome
  · simp [gsRound_next_of_isSome I h, h]
  · simp [gsRound_next_of_not_isSome I h, h]

theorem gsRound_next_eq_self_iff {s : GSState n} {m : Fin n} :
    (I.gsRound s).next m = s.next m ↔ ¬ (I.proposal s m).isSome := by
  by_cases h : (I.proposal s m).isSome
  · simp [gsRound_next_of_isSome I h, h]
  · simp [gsRound_next_of_not_isSome I h, h]

theorem proposal_isSome_iff_exists {s : GSState n} {m : Fin n} :
    (I.proposal s m).isSome ↔ ∃ w, I.proposal s m = some w :=
  Option.isSome_iff_exists

/-- An unengaged man proposes to someone (the woman of rank `s.next m` on his list). -/
theorem Inv.exists_proposal_of_not_engaged {s : GSState n} (hs : Inv I s) {m : Fin n}
    (hm : ¬ s.IsEngaged m) : ∃ w, I.proposal s m = some w :=
  (proposal_isSome_iff_exists I).1
    ((proposal_isSome I).2 ⟨hm, hs.next_lt_of_not_engaged I hm⟩)

/-- Men propose in order of preference: if `rank_m w < next_k m` then `m` proposed to `w` in some
round `t < k`. -/
theorem exists_proposal_of_lt_next {m w : Fin n} {k : ℕ}
    (h : (I.manRank m w : ℕ) < (I.gsRun k).next m) :
    ∃ t < k, I.proposal (I.gsRun t) m = some w := by
  induction k with
  | zero => simp [gsRun_zero, GSState.init] at h
  | succ k ih =>
    by_cases hlt : (I.manRank m w : ℕ) < (I.gsRun k).next m
    · obtain ⟨t, ht, hp⟩ := ih hlt
      exact ⟨t, Nat.lt_succ_of_lt ht, hp⟩
    · rw [gsRun_succ] at h
      have hle := gsRound_next_le I (I.gsRun k) m
      have heq : (I.gsRun k).next m = I.manRank m w := by omega
      have hsome : (I.proposal (I.gsRun k) m).isSome := by
        by_contra hns
        rw [gsRound_next_of_not_isSome I hns] at h
        exact hlt h
      exact ⟨k, Nat.lt_succ_self k,
        (proposal_eq_some I).2 ⟨((proposal_isSome I).1 hsome).1, heq⟩⟩

end StableMatching.GSCore

/-! # Man-optimality (`StableMatching.GSOpt`) -/

namespace StableMatching.GSOpt

open StableMatching.GSCore

variable {n : ℕ} (I : Instance n)

/-- The man-optimality invariant relative to a matching `μ`: no man has proposed beyond his
`μ`-partner, and if he has just proposed to her, she holds him. -/
def J (μ : Matching n) (s : GSState n) : Prop :=
  ∀ m : Fin n, s.next m ≤ (I.manRank m (μ m) : ℕ) + 1 ∧
    (s.next m = (I.manRank m (μ m) : ℕ) + 1 → s.fiance (μ m) = some m)

theorem J_init (μ : Matching n) : J I μ (GSState.init n) := by
  unfold J
  intro m
  simp [GSState.init]

/-- Key step: if `μ` is stable and `J` holds, no man is rejected by his `μ`-partner. -/
theorem key {μ : Matching n} (hμ : I.IsStable μ) {s : GSState n} (hs : Inv I s)
    (hJ : J I μ s) {m m' : Fin n} (hm : m ∈ candidates I s (μ m))
    (h' : (I.gsRound s).fiance (μ m) = some m') : m' = m := by
  by_contra hne
  obtain ⟨hm'c, hle⟩ := (gsRound_fiance_eq_some I).1 h'
  have hlt : I.womanRank (μ m) m' < I.womanRank (μ m) m := by
    rcases (hle m hm).lt_or_eq with h | h
    · exact h
    · exact absurd ((I.womanRank (μ m)).injective h) hne
  have hrank : (I.manRank m' (μ m) : ℕ) ≤ I.manRank m' (μ m') := by
    rcases (mem_candidates I).1 hm'c with hp | hf
    · obtain ⟨hne', hnext⟩ := (proposal_eq_some I).1 hp
      obtain ⟨h1, h2⟩ := hJ m'
      have : s.next m' ≠ (I.manRank m' (μ m') : ℕ) + 1 := fun h => hne' ⟨_, h2 h⟩
      omega
    · have := hs.next_of_fiance hf
      obtain ⟨h1, _⟩ := hJ m'
      omega
  have hw : μ m ≠ μ m' := fun h => hne (μ.injective h).symm
  have hlt' : I.manRank m' (μ m) < I.manRank m' (μ m') := by
    rcases Nat.lt_or_eq_of_le hrank with h | h
    · exact Fin.lt_def.2 h
    · exact absurd ((I.manRank m').injective (Fin.ext h)) hw
  apply hμ m' (μ m)
  refine ⟨hlt', ?_⟩
  show I.womanRank (μ m) m' < I.womanRank (μ m) (μ.symm (μ m))
  rw [Equiv.symm_apply_apply]
  exact hlt

theorem J_gsRound {μ : Matching n} (hμ : I.IsStable μ) {s : GSState n} (hs : Inv I s)
    (hJ : J I μ s) : J I μ (I.gsRound s) := by
  intro m
  obtain ⟨h1, h2⟩ := hJ m
  by_cases hp : (I.proposal s m).isSome
  · obtain ⟨w', hw'⟩ := (proposal_isSome_iff_exists I).1 hp
    obtain ⟨hne, hnext⟩ := (proposal_eq_some I).1 hw'
    have hlt : s.next m ≠ (I.manRank m (μ m) : ℕ) + 1 := fun h => hne ⟨_, h2 h⟩
    rw [gsRound_next_of_isSome I hp]
    refine ⟨by omega, fun heq => ?_⟩
    have hw : w' = μ m := by
      apply (I.manRank m).injective
      apply Fin.ext
      omega
    subst hw
    have hc : m ∈ candidates I s (μ m) := (mem_candidates I).2 (Or.inl hw')
    obtain ⟨m', hm', -⟩ := gsRound_fiance_of_mem I hc
    rw [hm', key I hμ hs hJ hc hm']
  · rw [gsRound_next_of_not_isSome I hp]
    refine ⟨h1, fun heq => ?_⟩
    have hc : m ∈ candidates I s (μ m) := (mem_candidates I).2 (Or.inr (h2 heq))
    obtain ⟨m', hm', -⟩ := gsRound_fiance_of_mem I hc
    rw [hm', key I hμ hs hJ hc hm']

theorem J_gsRun {μ : Matching n} (hμ : I.IsStable μ) (k : ℕ) : J I μ (I.gsRun k) := by
  induction k with
  | zero => exact J_init I μ
  | succ k ih => rw [gsRun_succ]; exact J_gsRound I hμ (inv_gsRun I k) ih

/-- Man-optimality of the Gale–Shapley outcome. -/
theorem man_optimal {μ₀ μ : Matching n} (h₀ : I.IsGSOutcome μ₀) (hμ : I.IsStable μ)
    (m : Fin n) : I.manRank m (μ₀ m) ≤ I.manRank m (μ m) := by
  have h1 := (J_gsRun I hμ (n ^ 2) m).1
  have h2 := next_of_isGSOutcome I h₀ m
  unfold Instance.galeShapley at h2
  rw [Fin.le_iff_val_le_val]
  omega

/-- Woman-pessimality of the Gale–Shapley outcome. -/
theorem woman_pessimal {μ₀ μ : Matching n} (h₀ : I.IsGSOutcome μ₀) (hμ : I.IsStable μ)
    (w : Fin n) : I.womanRank w (μ.symm w) ≤ I.womanRank w (μ₀.symm w) := by
  obtain ⟨m₀, rfl⟩ := μ₀.surjective w
  rw [Equiv.symm_apply_apply]
  by_contra hcon
  rw [not_le] at hcon
  have hne : μ m₀ ≠ μ₀ m₀ := by
    intro h
    have : μ.symm (μ₀ m₀) = m₀ := by rw [← h, Equiv.symm_apply_apply]
    rw [this] at hcon
    exact lt_irrefl _ hcon
  have hle := man_optimal I h₀ hμ m₀
  have hlt : I.manRank m₀ (μ₀ m₀) < I.manRank m₀ (μ m₀) := by
    rcases hle.lt_or_eq with h | h
    · exact h
    · exact absurd ((I.manRank m₀).injective h).symm hne
  exact hμ m₀ (μ₀ m₀) ⟨hlt, hcon⟩

end StableMatching.GSOpt

open StableMatching.GSOpt in
theorem solution {n : ℕ} (I : Instance n) (μ₀ μ : Matching n)
    (h₀ : I.IsGSOutcome μ₀) (hμ : I.IsStable μ) (w : Fin n) :
    I.womanRank w (μ.symm w) ≤ I.womanRank w (μ₀.symm w) :=
  woman_pessimal I h₀ hμ w
