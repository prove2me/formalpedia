-- Prove2me | solution 1 for ResourceScheduling.Chain.threePartition_iff_p3Schedule
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T17:21:03.238143+00:00
-- url     : https://prove2.me/submissions/889e94ae-7db2-47d0-8970-54ee64d84a76

import Mathlib
import Definitions.Def_ResourceScheduling_Chain_Constructions

namespace P3Sched5d59

open ResourceScheduling.Chain

/-- Two distinct naturals cast to reals are at distance at least one. -/
theorem nat_sep {a b : ℕ} (h : a ≠ b) : (a : ℝ) + 1 ≤ b ∨ (b : ℝ) + 1 ≤ a := by
  rcases lt_or_gt_of_ne h with h | h
  · left; exact_mod_cast h
  · right; exact_mod_cast h

theorem nat_eq_of_window {a b : ℕ} {x : ℝ} (ha1 : (a : ℝ) ≤ x) (ha2 : x < a + 1)
    (hb1 : (b : ℝ) ≤ x) (hb2 : x < b + 1) : a = b := by
  by_contra h
  rcases nat_sep h with h' | h' <;> linarith

theorem prec_nil (P : ThreePartition) (j k : Fin P.p3Instance.n) :
    ¬ P.p3Instance.Prec j k := by
  intro h
  induction h with
  | single h => cases h
  | tail _ h _ => cases h

/-- rank of `j` inside a finset: the number of smaller elements. -/
theorem rank_lt {n : ℕ} (T : Finset (Fin n)) (j : Fin n) (hj : j ∈ T) :
    (T.filter (· < j)).card < T.card := by
  apply Finset.card_lt_card
  refine ⟨Finset.filter_subset _ _, fun h => ?_⟩
  have := h hj
  simp at this

theorem rank_inj {n : ℕ} (T : Finset (Fin n)) (j k : Fin n) (hj : j ∈ T) (hk : k ∈ T)
    (h : (T.filter (· < j)).card = (T.filter (· < k)).card) : j = k := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have : (T.filter (· < j)).card < (T.filter (· < k)).card := by
      apply Finset.card_lt_card
      refine ⟨fun x hx => ?_, fun hs => ?_⟩
      · simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, lt_trans hx.2 hlt⟩
      · have : j ∈ T.filter (· < k) := by simp [hj, hlt]
        have := hs this
        simp at this
    omega
  · have : (T.filter (· < k)).card < (T.filter (· < j)).card := by
      apply Finset.card_lt_card
      refine ⟨fun x hx => ?_, fun hs => ?_⟩
      · simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, lt_trans hx.2 hlt⟩
      · have : k ∈ T.filter (· < j) := by simp [hk, hlt]
        have := hs this
        simp at this
    omega

theorem forward (P : ThreePartition) :
    P.HasSolution → P.p3Instance.HasScheduleWithin P.t := by
  rintro ⟨σ, hσ⟩
  classical
  let F : Fin P.t → Finset (Fin (3 * P.t)) := fun i => Finset.univ.filter fun j => σ j = i
  have hmem : ∀ j, j ∈ F (σ j) := fun j => by simp [F]
  have hFc : ∀ i, (F i).card = 3 := fun i => (hσ i).1
  let mach : Fin (3 * P.t) → Fin 3 := fun j =>
    ⟨((F (σ j)).filter (· < j)).card, lt_of_lt_of_eq (rank_lt (F (σ j)) j (hmem j)) (hFc (σ j))⟩
  let S : Schedule P.p3Instance := ⟨mach, fun j => ((σ j : ℕ) : ℝ)⟩
  refine ⟨S, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro j; exact Nat.cast_nonneg _
  · rintro (j : Fin (3 * P.t)) (k : Fin (3 * P.t)) hjk hm
    simp only [Schedule.completion, S]
    by_cases he : σ j = σ k
    · exfalso
      apply hjk
      have hm' : (mach j : ℕ) = mach k := congrArg Fin.val hm
      simp only [mach] at hm'
      rw [he] at hm'
      exact rank_inj (F (σ k)) j k (he ▸ hmem j) (hmem k) hm'
    · exact nat_sep (fun h => he (Fin.ext h))
  · intro j k h; exact absurd h (prec_nil P j k)
  · intro x h
    change ∑ j ∈ _, P.a j ≤ P.b
    by_cases hx : ∃ j0 : Fin (3 * P.t), S.IsExecutedAt j0 x
    · obtain ⟨j0, hj0⟩ := hx
      calc _ ≤ ∑ j ∈ F (σ j0), P.a j := by
            apply Finset.sum_le_sum_of_subset
            intro k hk
            have hk2 := (Finset.mem_filter.1 hk).2
            obtain ⟨k1, k2⟩ := hk2
            obtain ⟨a1, a2⟩ := hj0
            simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
            exact Fin.ext (nat_eq_of_window k1 k2 a1 a2)
        _ = P.b := (hσ (σ j0)).2
    · calc _ = 0 := Finset.sum_eq_zero (fun k hk => absurd ⟨k, (Finset.mem_filter.1 hk).2⟩ hx)
        _ ≤ P.b := Nat.zero_le _
  · unfold Schedule.cmax
    split_ifs with hn
    · apply Finset.sup'_le
      intro j _
      simp only [Schedule.completion, S]
      have := (σ j).isLt
      have : ((σ j : ℕ) : ℝ) + 1 ≤ (P.t : ℝ) := by exact_mod_cast this
      exact this
    · exact Nat.cast_nonneg _

theorem backward (P : ThreePartition) (hsum : ∑ j, P.a j = P.t * P.b) :
    P.p3Instance.HasScheduleWithin P.t → P.HasSolution := by
  rintro ⟨S, ⟨hnn, hov, _, hres⟩, hc⟩
  classical
  have hcomp : ∀ j, S.start j + 1 ≤ P.t := by
    intro j
    have hn : 0 < P.p3Instance.n := Fin.pos j
    have : S.completion j ≤ S.cmax := by
      unfold Schedule.cmax
      rw [dif_pos hn]
      exact Finset.le_sup' S.completion (Finset.mem_univ j)
    exact le_trans this hc
  -- the slot of a job: ⌈S_j⌉
  have hceil_lt : ∀ j, ⌈S.start j⌉.toNat < P.t := by
    intro j
    have h1 := hcomp j
    have h0 := hnn j
    have : ⌈S.start j⌉ ≤ (P.t : ℤ) - 1 := by
      rw [Int.ceil_le]; push_cast; linarith
    have := Int.ceil_nonneg h0
    omega
  let σ : Fin (3 * P.t) → Fin P.t := fun j => ⟨⌈S.start j⌉.toNat, hceil_lt j⟩
  have hceilnn : ∀ j, 0 ≤ ⌈S.start j⌉ := fun j => Int.ceil_nonneg (hnn j)
  -- executing at time i iff slot = i
  have hexec : ∀ (i : Fin P.t) (j : Fin (3 * P.t)), S.IsExecutedAt j (i : ℕ) ↔ σ j = i := by
    intro i j
    simp only [Schedule.IsExecutedAt, σ, Fin.ext_iff]
    constructor
    · rintro ⟨h1, h2⟩
      have : ⌈S.start j⌉ = ((i : ℕ) : ℤ) := by
        rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
      omega
    · intro h
      have h' : ⌈S.start j⌉ = ((i : ℕ) : ℤ) := by have := hceilnn j; omega
      rw [Int.ceil_eq_iff] at h'
      push_cast at h'
      constructor <;> linarith [h'.1, h'.2]
  -- injectivity of (machine, slot)
  have hinj : Function.Injective (fun j : Fin (3 * P.t) => (S.machine j, σ j)) := by
    intro j k h
    simp only [Prod.mk.injEq] at h
    by_contra hjk
    have hsl : ⌈S.start j⌉ = ⌈S.start k⌉ := by
      have := congrArg Fin.val h.2
      simp only [σ] at this
      have := hceilnn j; have := hceilnn k; omega
    rcases hov j k hjk h.1 with h' | h' <;>
    · simp only [Schedule.completion] at h'
      have a1 := Int.ceil_lt_add_one (S.start j)
      have a2 := Int.ceil_lt_add_one (S.start k)
      have b1 := Int.le_ceil (S.start j)
      have b2 := Int.le_ceil (S.start k)
      have : (⌈S.start j⌉ : ℝ) = ⌈S.start k⌉ := by exact_mod_cast hsl
      linarith
  have hbij : Function.Bijective (fun j : Fin (3 * P.t) => (S.machine j, σ j)) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    simp only [Fintype.card_prod, Fintype.card_fin]; rfl
  -- fiber cardinality
  have hcard : ∀ i : Fin P.t, (Finset.univ.filter fun j => σ j = i).card = 3 := by
    intro i
    have : (Finset.univ.filter fun j => σ j = i).card =
        (Finset.univ : Finset (Fin P.p3Instance.m)).card := by
      apply Finset.card_bij (fun j _ => S.machine j)
      · intro j _; exact Finset.mem_univ _
      · intro a ha b hb h
        have ha' := (Finset.mem_filter.1 ha).2
        have hb' := (Finset.mem_filter.1 hb).2
        exact hinj (Prod.ext h (ha'.trans hb'.symm))
      · intro m _
        obtain ⟨j, hj⟩ := hbij.2 (m, i)
        refine ⟨j, ?_, congrArg Prod.fst hj⟩
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, congrArg Prod.snd hj⟩
    rw [this, Finset.card_univ, Fintype.card_fin]; rfl
  -- fiber sums at most b
  have hle : ∀ i : Fin P.t, ∑ j ∈ Finset.univ.filter (fun j => σ j = i), P.a j ≤ P.b := by
    intro i
    have h := hres ((i : ℕ) : ℝ) ⟨0, Nat.one_pos⟩
    refine le_trans (le_of_eq ?_) h
    apply Finset.sum_congr ?_ (fun _ _ => rfl)
    ext j
    constructor
    · intro hj
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (hexec i j).2 (Finset.mem_filter.1 hj).2⟩
    · intro hj
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (hexec i j).1 (Finset.mem_filter.1 hj).2⟩
  -- total
  have htot : ∑ i : Fin P.t, ∑ j ∈ Finset.univ.filter (fun j => σ j = i), P.a j =
      ∑ i : Fin P.t, P.b := by
    rw [Finset.sum_fiberwise]
    simp [hsum]
  have heq := (Finset.sum_eq_sum_iff_of_le (fun i _ => hle i)).1 htot
  exact ⟨σ, fun i => ⟨hcard i, heq i (Finset.mem_univ i)⟩⟩

end P3Sched5d59

open ResourceScheduling.Chain in
theorem solution (P : ThreePartition) (hb : 0 < P.b)
    (ha : ∀ j, 0 < P.a j) (hsum : ∑ j, P.a j = P.t * P.b) :
    P.HasSolution ↔ P.p3Instance.HasScheduleWithin P.t := by
  exact ⟨P3Sched5d59.forward P, P3Sched5d59.backward P hsum⟩
