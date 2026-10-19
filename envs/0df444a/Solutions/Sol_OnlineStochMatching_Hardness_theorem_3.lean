-- Prove2me | solution 1 for OnlineStochMatching.Hardness.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-17T06:03:34.871496+00:00
-- url     : https://prove2.me/submissions/08867831-833e-48b3-bfa4-21562f43b6a5

-- Licensed under Apache 2.0. Full exact theorem: Online stochastic matching full hardness theorem, both parts.
import Mathlib
import Definitions.Def_OnlineStochMatching_Hardness_Model
import Definitions.Def_OnlineStochMatching_Hardness_SixCycle


open OnlineStochMatching.Hardness

namespace MatchingHardnessProof

noncomputable def copyALG (k : ℕ)
    (alg : OnlineAlg (Fin k × Adv) (Fin k × Imp) (3 * k))
    (ω : Fin (3 * k) → Fin k × Imp) (j : Fin k) : ℕ :=
  ((matchedAfter (kCycleEdge k) alg ω (3 * k)).filter fun a => a.1 = j).card

def BadCopy (k : ℕ)
    (alg : OnlineAlg (Fin k × Adv) (Fin k × Imp) (3 * k))
    (ω : Fin (3 * k) → Fin k × Imp) (j : Fin k) : Prop :=
  copyALG k alg ω j ≤ 2 ∧
    ∃ M : Fin (3 * k) → Option (Fin k × Adv),
      IsRealizationMatching (kCycleEdge k) ω M ∧ matchingSize M = 3 ∧
      ∀ t a, M t = some a → a.1 = j

end MatchingHardnessProof


open OnlineStochMatching.Hardness

namespace MatchingHardnessProof

variable {A I : Type} [Fintype A] [DecidableEq A] {n : ℕ}

noncomputable def assigned (M : Fin n → Option A) : Finset A :=
  Finset.univ.filter fun a => ∃ t, M t = some a

lemma mem_assigned (M : Fin n → Option A) (a : A) :
    a ∈ assigned M ↔ ∃ t, M t = some a := by
  classical
  simp [assigned]

lemma matchingSize_eq_card_assigned {G : A → I → Prop} {ω : Fin n → I}
    {M : Fin n → Option A} (hM : IsRealizationMatching G ω M) :
    matchingSize M = (assigned M).card := by
  classical
  unfold matchingSize
  let f : ∀ t ∈ Finset.univ.filter (fun t => (M t).isSome), A :=
    fun t ht => (M t).get (Finset.mem_filter.mp ht).2
  have hf : ∀ t ht, M t = some (f t ht) := by
    intro t ht
    exact (Option.some_get _).symm
  apply Finset.card_bij f
  · intro t ht
    exact (mem_assigned M _).mpr ⟨t, hf t ht⟩
  · intro t ht s hs heq
    exact hM.2 t s (f t ht) (hf t ht) (heq ▸ hf s hs)
  · intro a ha
    obtain ⟨t, ht⟩ := (mem_assigned M a).mp ha
    have hm : t ∈ Finset.univ.filter (fun t => (M t).isSome) := by simp [ht]
    exact ⟨t, hm, Option.some.inj ((hf t hm).symm.trans ht)⟩

omit [Fintype A] [DecidableEq A] in
lemma matchingSize_le_n (M : Fin n → Option A) : matchingSize M ≤ n := by
  unfold matchingSize
  exact (Finset.card_filter_le _ _).trans (by simp)

omit [DecidableEq A] in
lemma matchingSize_le_OPT {G : A → I → Prop} {ω : Fin n → I}
    {M : Fin n → Option A} (hM : IsRealizationMatching G ω M) :
    matchingSize M ≤ OPT G ω := by
  classical
  exact Finset.le_sup (f := matchingSize) (by simp [hM])

omit [DecidableEq A] in
lemma OPT_le_n (G : A → I → Prop) (ω : Fin n → I) : OPT G ω ≤ n := by
  classical
  apply Finset.sup_le
  intro M _
  exact matchingSize_le_n M

omit [Fintype A] in
lemma run_matching_witness (G : A → I → Prop) [DecidableRel G]
    (alg : OnlineAlg A I n) (ω : Fin n → I) (k : ℕ) (hk : k ≤ n) :
    ∃ M : Fin n → Option A, IsRealizationMatching G ω M ∧
      (∀ a, (∃ t, M t = some a) ↔ a ∈ matchedAfter G alg ω k) ∧
      ∀ t, k ≤ t.val → M t = none := by
  classical
  induction k with
  | zero =>
    refine ⟨fun _ => none, ⟨?_, ?_⟩, ?_, ?_⟩ <;> simp [matchedAfter]
  | succ k ih =>
    obtain ⟨M, hM, hr, hs⟩ := ih (by omega)
    have hkn : k < n := by omega
    let t : Fin n := ⟨k, hkn⟩
    have hMt : M t = none := hs t (by rfl)
    cases hp : alg t (prefixOf ω t) (ω t) with
    | none =>
      refine ⟨M, hM, ?_, ?_⟩
      · simpa [matchedAfter, hkn, step, t, hp] using hr
      · intro s hks; exact hs s (by omega)
    | some a =>
      by_cases ha : G a (ω t) ∧ a ∉ matchedAfter G alg ω k
      · let N := Function.update M t (some a)
        have hold : ∀ s, M s ≠ some a := by
          intro s he; exact ha.2 ((hr a).mp ⟨s, he⟩)
        refine ⟨N, ⟨?_, ?_⟩, ?_, ?_⟩
        · intro s b hb
          by_cases he : s = t
          · subst s
            have hab : a = b := Option.some.inj (by simpa [N] using hb)
            simpa [← hab] using ha.1
          · exact hM.1 s b (by simpa [N, he] using hb)
        · intro s u b hb hu
          by_cases hst : s = t
          · subst s
            have hab : a = b := Option.some.inj (by simpa [N] using hb)
            by_cases hut : u = t
            · exact hut.symm
            · exact False.elim (hold u (by simpa [N, hut, ← hab] using hu))
          · by_cases hut : u = t
            · subst u
              have hab : a = b := Option.some.inj (by simpa [N] using hu)
              exact False.elim (hold s (by simpa [N, hst, ← hab] using hb))
            · exact hM.2 s u b (by simpa [N, hst] using hb)
                (by simpa [N, hut] using hu)
        · intro b
          have hset : matchedAfter G alg ω (k + 1) =
              insert a (matchedAfter G alg ω k) := by
            simp [matchedAfter, hkn, step, t, hp, ha]
          rw [hset, Finset.mem_insert]
          constructor
          · rintro ⟨s, he⟩
            by_cases hst : s = t
            · subst s; exact Or.inl (Option.some.inj (by simpa [N] using he)).symm
            · exact Or.inr ((hr b).mp ⟨s, by simpa [N, hst] using he⟩)
          · rintro (rfl | hb)
            · exact ⟨t, by simp [N]⟩
            · obtain ⟨s, hs'⟩ := (hr b).mpr hb
              have hst : s ≠ t := by intro he; subst s; simp [hMt] at hs'
              exact ⟨s, by simpa [N, hst] using hs'⟩
        · intro s hks
          have hst : s ≠ t := by intro he; subst s; simp [t] at hks
          simpa [N, hst] using hs s (by omega)
      · refine ⟨M, hM, ?_, ?_⟩
        · simpa [matchedAfter, hkn, step, t, hp, ha] using hr
        · intro s hks; exact hs s (by omega)

lemma exists_run_matching (G : A → I → Prop) [DecidableRel G]
    (alg : OnlineAlg A I n) (ω : Fin n → I) :
    ∃ M : Fin n → Option A, IsRealizationMatching G ω M ∧
      assigned M = matchedAfter G alg ω n ∧ matchingSize M = ALG G alg ω := by
  obtain ⟨M, hM, hr, _⟩ := run_matching_witness G alg ω n le_rfl
  have he : assigned M = matchedAfter G alg ω n := by
    ext a; exact (mem_assigned M a).trans (hr a)
  exact ⟨M, hM, he, by rw [matchingSize_eq_card_assigned hM, he]; rfl⟩

lemma ALG_le_OPT (G : A → I → Prop) [DecidableRel G]
    (alg : OnlineAlg A I n) (ω : Fin n → I) : ALG G alg ω ≤ OPT G ω := by
  obtain ⟨M, hM, _, hm⟩ := exists_run_matching G alg ω
  rw [← hm]
  exact matchingSize_le_OPT hM

end MatchingHardnessProof


namespace MatchingHardnessProof
open OnlineStochMatching.Hardness

 def neighbors (v : Imp) : Finset Adv := Finset.univ.filter (fun advert => cycleEdge advert v)

 theorem mem_neighbors (advert : Adv) (v : Imp) : advert ∈ neighbors v ↔ cycleEdge advert v := by
  simp [neighbors]

 theorem card_neighbors (v : Imp) : (neighbors v).card = 2 := by
  cases v <;> decide

 theorem exists_repeat (u : Imp) (s : Option Adv) :
    ∃ v : Imp, v ≠ u ∧
      (∀ advert : Adv, s = some advert → cycleEdge advert u → cycleEdge advert v) ∧
      ∃ M : Fin 3 → Adv, Function.Injective M ∧
        ∀ t, cycleEdge (M t) (![u, v, v] t) := by
  cases u <;> cases s <;> first
    | decide
    | (rename_i advert; cases advert <;> decide)

 theorem exists_adjacent (u : Imp) : ∃ advert : Adv, cycleEdge advert u := by
  cases u <;> decide

end MatchingHardnessProof


namespace MatchingHardnessProof

noncomputable def fillPositions {n : ℕ} {I : Type} (s : Fin 3 ↪ Fin n)
    (v : Fin 3 → I) (w : {t : Fin n // t ∉ Set.range s} → I) (t : Fin n) : I := by
  classical
  exact if h : ∃ i, s i = t then v (Classical.choose h) else w ⟨t, h⟩

 theorem fillPositions_at {n : ℕ} {I : Type} (s : Fin 3 ↪ Fin n)
    (v : Fin 3 → I) (w : {t : Fin n // t ∉ Set.range s} → I) (i : Fin 3) :
    fillPositions s v w (s i) = v i := by
  classical
  unfold fillPositions
  rw [dif_pos ⟨i, rfl⟩]
  congr 1
  exact s.injective (Classical.choose_spec (show ∃ a, s a = s i from ⟨i, rfl⟩))

 theorem fillPositions_outside {n : ℕ} {I : Type} (s : Fin 3 ↪ Fin n)
    (v : Fin 3 → I) (w : {t : Fin n // t ∉ Set.range s} → I)
    (t : {t : Fin n // t ∉ Set.range s}) : fillPositions s v w t = w t := by
  classical
  unfold fillPositions
  rw [dif_neg (show ¬ ∃ i, s i = t from t.property)]

 theorem card_outside_positions {n : ℕ} (s : Fin 3 ↪ Fin n) :
    Fintype.card {t : Fin n // t ∉ Set.range s} = n - 3 := by
  classical
  change Fintype.card (↥(Set.range s)ᶜ) = n - 3
  rw [Fintype.card_compl_set, Fintype.card_range s]
  simp

 def blockPositions {k : ℕ} (i : Fin 3 → Fin k) : Fin 3 ↪ Fin (3 * k) where
  toFun r := ⟨r.val * k + (i r).val, by
    have hr : r.val + 1 ≤ 3 := by omega
    have hi := (i r).isLt
    nlinarith⟩
  inj' := by
    intro a b h
    have he := congrArg Fin.val h
    apply Fin.ext
    dsimp at he
    have ha := (i a).isLt
    have hb := (i b).isLt
    by_contra hne
    rcases lt_or_gt_of_ne hne with hab | hba
    · have hg : a.val + 1 ≤ b.val := by omega
      nlinarith
    · have hg : b.val + 1 ≤ a.val := by omega
      nlinarith

 theorem blockPositions_strictMono {k : ℕ} (i : Fin 3 → Fin k) :
    StrictMono (blockPositions i) := by
  intro a b hab
  change a.val * k + (i a).val < b.val * k + (i b).val
  have ha := (i a).isLt
  have hb := (i b).isLt
  have hab' : a.val < b.val := hab
  have hg : a.val + 1 ≤ b.val := by omega
  nlinarith

end MatchingHardnessProof


namespace MatchingHardnessProof
open OnlineStochMatching.Hardness

 theorem assigned_property {A I : Type} [DecidableEq A] {n : ℕ}
    (G : A → I → Prop) [DecidableRel G] (alg : OnlineAlg A I n) (ω : Fin n → I)
    (R : A → Prop)
    (h : ∀ t advert, alg t (prefixOf ω t) (ω t) = some advert → G advert (ω t) → R advert)
    (r : ℕ) : ∀ advert ∈ matchedAfter G alg ω r, R advert := by
  induction r with
  | zero => simp [matchedAfter]
  | succ r ih =>
    rw [matchedAfter]
    split_ifs with hr
    · unfold step
      split
      next advert ha =>
        split_ifs with hadj
        · intro other hb
          rcases Finset.mem_insert.mp hb with rfl | hb
          · exact h ⟨r, hr⟩ _ ha hadj.1
          · exact ih other hb
        · exact ih
      next => exact ih
    · exact ih

 theorem copyALG_le_two {k : ℕ}
    (alg : OnlineAlg (Fin k × Adv) (Fin k × Imp) (3*k))
    (ω : Fin (3*k) → Fin k × Imp) (j : Fin k) (v : Imp)
    (h : ∀ t advert, alg t (prefixOf ω t) (ω t) = some advert →
      kCycleEdge k advert (ω t) → advert.1 = j → cycleEdge advert.2 v) :
    copyALG k alg ω j ≤ 2 := by
  classical
  have hi := assigned_property (kCycleEdge k) alg ω
    (fun advert => advert.1 = j → cycleEdge advert.2 v) h (3*k)
  have hs : ((matchedAfter (kCycleEdge k) alg ω (3*k)).filter (fun advert => advert.1 = j)) ⊆
      (neighbors v).image (fun advert => (j, advert)) := by
    intro advert ha
    obtain ⟨ha, haj⟩ := Finset.mem_filter.mp ha
    apply Finset.mem_image.mpr
    exact ⟨advert.2, (mem_neighbors _ _).mpr (hi advert ha haj), by cases advert; simp_all⟩
  exact (Finset.card_le_card hs).trans ((Finset.card_image_le).trans_eq (card_neighbors v))

end MatchingHardnessProof


namespace MatchingHardnessProof
open OnlineStochMatching.Hardness

noncomputable def positionMatching {n : ℕ} {A : Type} (s : Fin 3 ↪ Fin n)
    (v : Fin 3 → A) : Fin n → Option A :=
  fillPositions s (fun r => some (v r)) (fun _ => none)

 theorem positionMatching_at {n : ℕ} {A : Type} (s : Fin 3 ↪ Fin n)
    (v : Fin 3 → A) (r : Fin 3) : positionMatching s v (s r) = some (v r) :=
  fillPositions_at s _ _ r

 theorem positionMatching_some {n : ℕ} {A : Type} (s : Fin 3 ↪ Fin n)
    (v : Fin 3 → A) (t : Fin n) (advert : A) :
    positionMatching s v t = some advert ↔ ∃ r, s r = t ∧ v r = advert := by
  classical
  by_cases ht : t ∈ Set.range s
  · obtain ⟨r, rfl⟩ := ht
    rw [positionMatching_at]
    constructor
    · intro he
      exact ⟨r, rfl, Option.some.inj he⟩
    · rintro ⟨q, hq, hv⟩
      have : q = r := s.injective hq
      simpa [this] using congrArg some hv
  · have he : positionMatching s v t = none := fillPositions_outside s _ _ ⟨t, ht⟩
    rw [he]
    simp only [reduceCtorEq, false_iff]
    rintro ⟨r, hr, _⟩
    exact ht ⟨r, hr⟩

 theorem positionMatching_valid {n : ℕ} {A I : Type}
    (s : Fin 3 ↪ Fin n) (v : Fin 3 → A) (hv : Function.Injective v)
    (G : A → I → Prop) (ω : Fin n → I) (he : ∀ r, G (v r) (ω (s r))) :
    IsRealizationMatching G ω (positionMatching s v) := by
  constructor
  · intro t advert ht
    obtain ⟨r, rfl, rfl⟩ := (positionMatching_some s v t advert).mp ht
    exact he r
  · intro t u advert ht hu
    obtain ⟨r, rfl, hr⟩ := (positionMatching_some s v t advert).mp ht
    obtain ⟨q, rfl, hq⟩ := (positionMatching_some s v u advert).mp hu
    exact congrArg s (hv (hr.trans hq.symm))

 theorem positionMatching_size {n : ℕ} {A : Type}
    (s : Fin 3 ↪ Fin n) (v : Fin 3 → A) : matchingSize (positionMatching s v) = 3 := by
  classical
  have he : (Finset.univ.filter fun t => (positionMatching s v t).isSome) =
      Finset.univ.image s := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro ht
      obtain ⟨advert, ha⟩ := Option.isSome_iff_exists.mp ht
      obtain ⟨r, hr, _⟩ := (positionMatching_some s v t advert).mp ha
      exact ⟨r, hr⟩
    · rintro ⟨r, rfl⟩
      simp [positionMatching_at]
  unfold matchingSize
  rw [he, Finset.card_image_of_injective _ s.injective]
  simp

end MatchingHardnessProof


namespace MatchingHardnessProof
open OnlineStochMatching.Hardness

abbrev OutsideCopy {k : ℕ} (j : Fin k) := {l : Fin k // l ≠ j} × Imp

noncomputable def copyFill {k n : ℕ} (j : Fin k) (s : Fin 3 ↪ Fin n)
    (v : Fin 3 → Imp) (w : {t : Fin n // t ∉ Set.range s} → OutsideCopy j) :
    Fin n → Fin k × Imp :=
  fillPositions s (fun r => (j, v r)) (fun t => ((w t).1.val, (w t).2))

 theorem copyFill_at {k n : ℕ} (j : Fin k) (s : Fin 3 ↪ Fin n)
    (v : Fin 3 → Imp) (w : {t : Fin n // t ∉ Set.range s} → OutsideCopy j) (r : Fin 3) :
    copyFill j s v w (s r) = (j, v r) := fillPositions_at s _ _ r

 theorem copyFill_outside {k n : ℕ} (j : Fin k) (s : Fin 3 ↪ Fin n)
    (v : Fin 3 → Imp) (w : {t : Fin n // t ∉ Set.range s} → OutsideCopy j)
    (t : {t : Fin n // t ∉ Set.range s}) :
    copyFill j s v w t = ((w t).1.val, (w t).2) := fillPositions_outside s _ _ t

 theorem copyFill_copy_iff {k n : ℕ} (j : Fin k) (s : Fin 3 ↪ Fin n)
    (v : Fin 3 → Imp) (w : {t : Fin n // t ∉ Set.range s} → OutsideCopy j) (t : Fin n) :
    (copyFill j s v w t).1 = j ↔ t ∈ Set.range s := by
  classical
  by_cases ht : t ∈ Set.range s
  · obtain ⟨r, rfl⟩ := ht
    simp [copyFill_at]
  · rw [copyFill_outside j s v w ⟨t, ht⟩]
    exact iff_of_false (w ⟨t, ht⟩).1.property ht

 theorem copyFill_prefix {k n : ℕ} (j : Fin k) (s : Fin 3 ↪ Fin n)
    (hs : StrictMono s) (v z : Fin 3 → Imp)
    (w : {t : Fin n // t ∉ Set.range s} → OutsideCopy j) :
    prefixOf (copyFill j s v w) (s 0) = prefixOf (copyFill j s z w) (s 0) := by
  funext t
  let q : Fin n := Fin.castLE (Nat.le_of_lt (s 0).isLt) t
  have hq : q ∉ Set.range s := by
    rintro ⟨r, hr⟩
    have hle : s 0 ≤ s r := hs.monotone (Fin.zero_le r)
    have hlt : q < s 0 := t.isLt
    rw [hr] at hle
    exact (not_le_of_gt hlt) hle
  change copyFill j s v w q = copyFill j s z w q
  rw [copyFill_outside j s v w ⟨q, hq⟩, copyFill_outside j s z w ⟨q, hq⟩]

 theorem card_outsideCopy {k : ℕ} (j : Fin k) : Fintype.card (OutsideCopy j) = (k-1)*3 := by
  classical
  rw [Fintype.card_prod]
  have he : Fintype.card {l : Fin k // l ≠ j} = k-1 := by
    simp
  rw [he]
  rfl

end MatchingHardnessProof


namespace MatchingHardnessProof
open OnlineStochMatching.Hardness

 theorem exists_bad_copy_fill {k : ℕ}
    (alg : OnlineAlg (Fin k × Adv) (Fin k × Imp) (3*k)) (j : Fin k)
    (s : Fin 3 ↪ Fin (3*k)) (hs : StrictMono s)
    (w : {t : Fin (3*k) // t ∉ Set.range s} → OutsideCopy j) (u : Imp) :
    ∃ v : Imp, BadCopy k alg (copyFill j s ![u,v,v] w) j := by
  classical
  let ω₀ := copyFill j s ![u,u,u] w
  let proposal := alg (s 0) (prefixOf ω₀ (s 0)) (j,u)
  let localProposal : Option Adv := proposal.bind (fun advert =>
    if advert.1 = j then some advert.2 else none)
  obtain ⟨v, _, hcover, M, hM, hedges⟩ := exists_repeat u localProposal
  refine ⟨v, ?_, ?_⟩
  · apply copyALG_le_two alg _ j v
    intro t advert hp he hj
    have ht : (copyFill j s ![u,v,v] w t).1 = j := he.1.symm.trans hj
    obtain ⟨r, rfl⟩ := (copyFill_copy_iff j s ![u,v,v] w t).mp ht
    have hedge := he.2
    fin_cases r
    · have hprefix := copyFill_prefix j s hs ![u,v,v] ![u,u,u] w
      have hp' : proposal = some advert := by
        change alg (s 0) (prefixOf (copyFill j s ![u,v,v] w) (s 0))
          (copyFill j s ![u,v,v] w (s 0)) = some advert at hp
        rw [copyFill_at] at hp
        change alg (s 0) (prefixOf (copyFill j s ![u,v,v] w) (s 0)) (j,u) = some advert at hp
        rw [hprefix] at hp
        exact hp
      have hl : localProposal = some advert.2 := by
        simp [localProposal, hp', hj]
      apply hcover advert.2 hl
      change cycleEdge advert.2 (copyFill j s ![u,v,v] w (s 0)).2 at hedge
      rw [copyFill_at] at hedge
      exact hedge
    · change cycleEdge advert.2 (copyFill j s ![u,v,v] w (s 1)).2 at hedge
      rw [copyFill_at] at hedge
      exact hedge
    · change cycleEdge advert.2 (copyFill j s ![u,v,v] w (s 2)).2 at hedge
      rw [copyFill_at] at hedge
      exact hedge
  · refine ⟨positionMatching s (fun r => (j, M r)), ?_, positionMatching_size _ _, ?_⟩
    · apply positionMatching_valid
      · intro r q he
        exact hM (congrArg Prod.snd he)
      · intro r
        rw [copyFill_at]
        exact ⟨rfl, hedges r⟩
    · intro t advert ht
      obtain ⟨r, _, he⟩ := (positionMatching_some s (fun r => (j, M r)) t advert).mp ht
      exact (congrArg Prod.fst he).symm

end MatchingHardnessProof


noncomputable section
namespace MatchingHardnessProof
open OnlineStochMatching.Hardness Classical

 def BadEncoding {k : ℕ} (j : Fin k) :=
  Σ i : Fin 3 → Fin k,
    ({t : Fin (3*k) // t ∉ Set.range (blockPositions i)} → OutsideCopy j) × Imp

 instance {k : ℕ} (j : Fin k) : Fintype (BadEncoding j) := by
  classical
  unfold BadEncoding
  infer_instance

 def badSequence {k : ℕ}
    (alg : OnlineAlg (Fin k × Adv) (Fin k × Imp) (3*k)) (j : Fin k)
    (d : BadEncoding j) : Fin (3*k) → Fin k × Imp :=
  let v := Classical.choose (exists_bad_copy_fill alg j (blockPositions d.1)
    (blockPositions_strictMono d.1) d.2.1 d.2.2)
  copyFill j (blockPositions d.1) ![d.2.2, v, v] d.2.1

 theorem badSequence_bad {k : ℕ}
    (alg : OnlineAlg (Fin k × Adv) (Fin k × Imp) (3*k)) (j : Fin k)
    (d : BadEncoding j) : BadCopy k alg (badSequence alg j d) j :=
  Classical.choose_spec (exists_bad_copy_fill alg j (blockPositions d.1)
    (blockPositions_strictMono d.1) d.2.1 d.2.2)

 theorem badSequence_copy_iff {k : ℕ}
    (alg : OnlineAlg (Fin k × Adv) (Fin k × Imp) (3*k)) (j : Fin k)
    (d : BadEncoding j) (t : Fin (3*k)) :
    (badSequence alg j d t).1 = j ↔ t ∈ Set.range (blockPositions d.1) :=
  copyFill_copy_iff j _ _ _ t

 theorem badSequence_injective {k : ℕ}
    (alg : OnlineAlg (Fin k × Adv) (Fin k × Imp) (3*k)) (j : Fin k) :
    Function.Injective (badSequence alg j) := by
  classical
  rintro ⟨i, w, u⟩ ⟨i', w', u'⟩ he
  have hr : Set.range (blockPositions i) = Set.range (blockPositions i') := by
    ext t
    rw [← badSequence_copy_iff alg j ⟨i,w,u⟩ t,
      ← badSequence_copy_iff alg j ⟨i',w',u'⟩ t, he]
  have hs := (blockPositions_strictMono i).range_inj (blockPositions_strictMono i') |>.mp hr
  have hi : i = i' := by
    funext r
    apply Fin.ext
    have hh := congrArg Fin.val (congrFun hs r)
    change r.val*k + (i r).val = r.val*k + (i' r).val at hh
    omega
  subst i'
  have hu : u = u' := by
    have hh := congrArg (fun f => (f (blockPositions i 0)).2) he
    simpa only [badSequence, copyFill_at, Matrix.cons_val_zero] using hh
  have hw : w = w' := by
    funext t
    have hh := congrArg (fun f => f t.val) he
    simp only [badSequence, copyFill_outside j (blockPositions i) _ _ t] at hh
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hh
    · exact congrArg (fun p : Fin k × Imp => p.2) hh
  subst w'
  subst u'
  rfl

 theorem bad_copy_count {k : ℕ}
    (alg : OnlineAlg (Fin k × Adv) (Fin k × Imp) (3*k)) (j : Fin k) :
    k^3 * 3 * (3*(k-1))^(3*k-3) ≤
      (Finset.univ.filter (fun ω => BadCopy k alg ω j)).card := by
  classical
  let f : BadEncoding j → {ω // BadCopy k alg ω j} :=
    fun d => ⟨badSequence alg j d, badSequence_bad alg j d⟩
  have hf : Function.Injective f := by
    intro d e he
    exact badSequence_injective alg j (congrArg Subtype.val he)
  have hh := Fintype.card_le_of_injective f hf
  have hc : Fintype.card (BadEncoding j) = k^3 * 3 * (3*(k-1))^(3*k-3) := by
    unfold BadEncoding
    rw [Fintype.card_sigma]
    simp only [Fintype.card_prod, Fintype.card_fun, card_outside_positions]
    have hco : Fintype.card {l : Fin k // l ≠ j} = k-1 := by simp
    simp only [hco, show Fintype.card Imp = 3 from rfl]
    change (∑ _ : Fin 3 → Fin k, ((k-1)*3)^(3*k-3)*3) = _
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      smul_eq_mul]
    ring
  rw [hc] at hh
  simpa only [Fintype.card_subtype] using hh

end MatchingHardnessProof

end


namespace MatchingHardnessProof

 theorem occupancy_power_lower (k : ℕ) (hk : 2 ≤ k) :
    Real.exp (-3) ≤ (((k : ℝ) - 1) / k) ^ (3*k-3) := by
  have hkpos : (0 : ℝ) < k := by positivity
  have hmpos : (0 : ℝ) < k - 1 := by
    have hh : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hcast : ((k-1 : ℕ) : ℝ) = (k : ℝ)-1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hb : (k : ℝ) / (k-1) ≤ Real.exp (1 / (k-1)) := by
    convert Real.add_one_le_exp (1 / ((k : ℝ)-1)) using 1
    field_simp
    ring
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ k / (k-1)) hb (k-1)
  rw [← Real.exp_nat_mul] at hp
  have he : ((k-1 : ℕ) : ℝ) * (1 / ((k : ℝ)-1)) = 1 := by
    rw [hcast]
    field_simp
  rw [he] at hp
  have hi : Real.exp (-1) ≤ (((k : ℝ)-1) / k) ^ (k-1) := by
    have hz : (0 : ℝ) < ((k : ℝ) / (k-1)) ^ (k-1) := by positivity
    have hh := (inv_le_inv₀ (Real.exp_pos 1) hz).mpr hp
    rw [← inv_pow, inv_div] at hh
    simpa only [Real.exp_neg] using hh
  have ht := pow_le_pow_left₀ (Real.exp_nonneg (-1)) hi 3
  rw [← Real.exp_nat_mul, ← pow_mul] at ht
  have hn : (k-1)*3 = 3*k-3 := by omega
  simpa only [Nat.cast_ofNat, mul_neg, mul_one, hn] using ht

end MatchingHardnessProof


open OnlineStochMatching.Hardness

namespace MatchingHardnessProof

lemma card_partition_copies {k : ℕ} (S : Finset (Fin k × Adv)) :
    S.card = ∑ j : Fin k, (S.filter fun p => p.1 = j).card := by
  exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)

lemma card_copy {k : ℕ} (j : Fin k) :
    (Finset.univ.filter (fun p : Fin k × Adv => p.1 = j)).card = 3 := by
  have he : Finset.univ.filter (fun p : Fin k × Adv => p.1 = j) =
      Finset.univ.image (fun ad : Adv => (j, ad)) := by
    ext p; simp; aesop
  rw [he, Finset.card_image_of_injective]
  · rfl
  · intro ad bd h; exact Prod.mk.inj h |>.2

lemma assigned_full_copy {k n : ℕ} {ω : Fin n → Fin k × Imp}
    {M : Fin n → Option (Fin k × Adv)} {j : Fin k}
    (hM : IsRealizationMatching (kCycleEdge k) ω M) (hsize : matchingSize M = 3)
    (hcopy : ∀ t ad, M t = some ad → ad.1 = j) :
    assigned M = Finset.univ.filter (fun p => p.1 = j) := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    obtain ⟨t, ht⟩ := (mem_assigned M p).mp hp
    simpa using hcopy t p ht
  · rw [← matchingSize_eq_card_assigned hM, hsize, card_copy]

lemma repair_bad_copies (k : ℕ)
    (alg : OnlineAlg (Fin k × Adv) (Fin k × Imp) (3*k))
    (ω : Fin (3*k) → Fin k × Imp) (B : Finset (Fin k))
    (hB : ∀ j ∈ B, BadCopy k alg ω j) :
    ALG (kCycleEdge k) alg ω + B.card ≤ OPT (kCycleEdge k) ω := by
  classical
  obtain ⟨M, hM, himage, hcount⟩ := exists_run_matching (kCycleEdge k) alg ω
  let P (j : Fin k) : Fin (3*k) → Option (Fin k × Adv) :=
    if hj : j ∈ B then Classical.choose (hB j hj).2 else fun _ => none
  have hP (j : Fin k) (hj : j ∈ B) :
      IsRealizationMatching (kCycleEdge k) ω (P j) ∧ matchingSize (P j) = 3 ∧
      ∀ t ad, P j t = some ad → ad.1 = j := by
    dsimp only [P]
    rw [dif_pos hj]
    exact Classical.choose_spec (hB j hj).2
  have hfull (j : Fin k) (hj : j ∈ B) :
      assigned (P j) = Finset.univ.filter (fun p => p.1 = j) :=
    assigned_full_copy (hP j hj).1 (hP j hj).2.1 (hP j hj).2.2
  let N (t : Fin (3*k)) := if (ω t).1 ∈ B then P (ω t).1 t else M t
  have hN : IsRealizationMatching (kCycleEdge k) ω N := by
    constructor
    · intro t ad ht
      by_cases hb : (ω t).1 ∈ B
      · exact (hP _ hb).1.1 t ad (by simpa [N, hb] using ht)
      · exact hM.1 t ad (by simpa [N, hb] using ht)
    · intro s t ad hs ht
      by_cases hsb : (ω s).1 ∈ B <;> by_cases htb : (ω t).1 ∈ B
      · have hsc : ad.1 = (ω s).1 :=
          ((hP _ hsb).1.1 s ad (by simpa [N, hsb] using hs)).1
        have htc : ad.1 = (ω t).1 :=
          ((hP _ htb).1.1 t ad (by simpa [N, htb] using ht)).1
        have he : (ω t).1 = (ω s).1 := htc.symm.trans hsc
        exact (hP _ hsb).1.2 s t ad (by simpa [N, hsb] using hs)
          (by simpa [N, htb, he, hsb] using ht)
      · have hsc := ((hP _ hsb).1.1 s ad (by simpa [N, hsb] using hs)).1
        have htc := (hM.1 t ad (by simpa [N, htb] using ht)).1
        exact False.elim (htb (htc ▸ hsc ▸ hsb))
      · have hsc := (hM.1 s ad (by simpa [N, hsb] using hs)).1
        have htc := ((hP _ htb).1.1 t ad (by simpa [N, htb] using ht)).1
        exact False.elim (hsb (hsc ▸ htc ▸ htb))
      · exact hM.2 s t ad (by simpa [N, hsb] using hs) (by simpa [N, htb] using ht)
  have hfiber (j : Fin k) :
      ((assigned N).filter fun p => p.1 = j).card =
        if j ∈ B then 3 else copyALG k alg ω j := by
    by_cases hj : j ∈ B
    · rw [if_pos hj]
      have he : (assigned N).filter (fun p => p.1 = j) =
          Finset.univ.filter (fun p => p.1 = j) := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · exact And.right
        · intro hp
          have hpm : p ∈ assigned (P j) := by rw [hfull j hj]; simpa using hp
          obtain ⟨t, ht⟩ := (mem_assigned (P j) p).mp hpm
          have hc : (ω t).1 = j := (((hP j hj).1.1 t p ht).1).symm.trans hp
          exact ⟨(mem_assigned N p).mpr ⟨t, by simp [N, hc, hj, ht]⟩, hp⟩
      rw [he, card_copy]
    · rw [if_neg hj]
      unfold copyALG
      rw [← himage]
      congr 1
      ext p
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hp, hpj⟩
        obtain ⟨t, ht⟩ := (mem_assigned N p).mp hp
        have hc : (ω t).1 = j := (hN.1 t p ht).1.symm.trans hpj
        exact ⟨(mem_assigned M p).mpr ⟨t, by simpa [N, hc, hj] using ht⟩, hpj⟩
      · rintro ⟨hp, hpj⟩
        obtain ⟨t, ht⟩ := (mem_assigned M p).mp hp
        have hc : (ω t).1 = j := (hM.1 t p ht).1.symm.trans hpj
        exact ⟨(mem_assigned N p).mpr ⟨t, by simp [N, hc, hj, ht]⟩, hpj⟩
  have hsum : ALG (kCycleEdge k) alg ω = ∑ j : Fin k, copyALG k alg ω j :=
    card_partition_copies _
  have hcard : B.card = ∑ j : Fin k, if j ∈ B then 1 else 0 := by simp
  calc
    ALG (kCycleEdge k) alg ω + B.card =
        ∑ j : Fin k, (copyALG k alg ω j + if j ∈ B then 1 else 0) := by
      rw [hsum, hcard, Finset.sum_add_distrib]
    _ ≤ ∑ j : Fin k, ((assigned N).filter fun p => p.1 = j).card := by
      apply Finset.sum_le_sum
      intro j _
      rw [hfiber]
      split_ifs with hj
      · have := (hB j hj).1; omega
      · simp
    _ = matchingSize N := by
      rw [← card_partition_copies, matchingSize_eq_card_assigned hN]
    _ ≤ OPT (kCycleEdge k) ω := matchingSize_le_OPT hN

end MatchingHardnessProof


open OnlineStochMatching.Hardness Classical

namespace MatchingHardnessProof

lemma ratio_le_one {A I : Type} [Fintype A] [DecidableEq A] {n : ℕ}
    (G : A → I → Prop) [DecidableRel G] (alg : OnlineAlg A I n) (ω : Fin n → I) :
    (ALG G alg ω : ℝ) / OPT G ω ≤ 1 := by
  by_cases ho : OPT G ω = 0
  · simp [ho]
  · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero ho)).mpr
    exact_mod_cast ALG_le_OPT G alg ω

lemma ratio_deficit_bound {a o b n : ℕ} (hn : 0 < n)
    (hao : a + b ≤ o) (hon : o ≤ n) :
    (a : ℝ) / o ≤ 1 - (b : ℝ) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases ho : o = 0
  · have hb : b = 0 := by omega
    simp [ho, hb]
  have ho' : (0 : ℝ) < o := by exact_mod_cast Nat.pos_of_ne_zero ho
  have hab : (a : ℝ) + b ≤ o := by exact_mod_cast hao
  have hon' : (o : ℝ) ≤ n := by exact_mod_cast hon
  have hb := div_le_div_of_nonneg_left (Nat.cast_nonneg b) ho' hon'
  have ha : (a : ℝ) / o ≤ 1 - (b : ℝ) / o := by
    apply (div_le_iff₀ ho').mpr
    field_simp
    nlinarith
  linarith

lemma pmf_sum_real {T : Type} [Fintype T] (P : PMF T) :
    ∑ t, (P t).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun t _ => P.apply_ne_top t)]
  simpa only [tsum_fintype, ENNReal.toReal_one] using congrArg ENNReal.toReal P.tsum_coe

lemma randomized_bound {A I : Type} [Fintype A] [DecidableEq A]
    [Fintype I] [DecidableEq I] {n : ℕ}
    (G : A → I → Prop) [DecidableRel G] (c : ℝ)
    (hc : ∀ alg : OnlineAlg A I n, expectedRatio G alg ≤ c)
    (P : PMF (OnlineAlg A I n)) : randExpectedRatio G P ≤ c := by
  unfold randExpectedRatio
  calc
    _ ≤ ∑ alg : OnlineAlg A I n, (P alg).toReal * c := by
      apply Finset.sum_le_sum
      intro alg _
      exact mul_le_mul_of_nonneg_left (hc alg) ENNReal.toReal_nonneg
    _ = c := by rw [← Finset.sum_mul, pmf_sum_real, one_mul]

lemma sum_bad_counts (k : ℕ)
    (alg : OnlineAlg (Fin k × Adv) (Fin k × Imp) (3*k)) :
    (∑ ω : Fin (3*k) → Fin k × Imp,
      ((Finset.univ.filter fun j => BadCopy k alg ω j).card : ℝ)) =
      ∑ j : Fin k, ((Finset.univ.filter fun ω => BadCopy k alg ω j).card : ℝ) := by
  classical
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]

end MatchingHardnessProof


open OnlineStochMatching.Hardness Classical

namespace MatchingHardnessProof

lemma expected_family_of_counts (k : ℕ) (hk : 0 < k)
    (alg : OnlineAlg (Fin k × Adv) (Fin k × Imp) (3*k)) (b : ℝ)
    (hb : ∀ j : Fin k, b ≤
      ((Finset.univ.filter fun ω => BadCopy k alg ω j).card : ℝ)) :
    expectedRatio (kCycleEdge k) alg ≤ 1 - b / (3 * (3*(k:ℝ))^(3*k)) := by
  classical
  let D : ℝ := (3*(k:ℝ))^(3*k)
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hD : 0 < D := by dsimp [D]; positivity
  have hcard : (Fintype.card (Fin (3*k) → Fin k × Imp) : ℝ) = D := by
    simp [Fintype.card_prod, show Fintype.card Imp = 3 from rfl,
      D, mul_comm]
  have hden : (Fintype.card (Fin k × Imp) : ℝ)^(3*k) = D := by
    simp [Fintype.card_prod, show Fintype.card Imp = 3 from rfl, D, mul_comm]
  have hpoint (ω : Fin (3*k) → Fin k × Imp) :
      (ALG (kCycleEdge k) alg ω : ℝ) / OPT (kCycleEdge k) ω ≤
        1 - ((Finset.univ.filter fun j => BadCopy k alg ω j).card : ℝ) / (3*k) := by
    have hr := repair_bad_copies k alg ω
      (Finset.univ.filter fun j => BadCopy k alg ω j)
      (fun j hj => (Finset.mem_filter.mp hj).2)
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      ratio_deficit_bound (by omega : 0 < 3*k) hr (OPT_le_n (kCycleEdge k) ω)
  have hsum : (k : ℝ)*b ≤
      ∑ ω : Fin (3*k) → Fin k × Imp,
        ((Finset.univ.filter fun j => BadCopy k alg ω j).card : ℝ) := by
    rw [sum_bad_counts]
    simpa using (Finset.sum_le_sum (s := Finset.univ) (fun j _ => hb j))
  unfold expectedRatio
  rw [hden]
  calc
    _ ≤ (∑ ω : Fin (3*k) → Fin k × Imp,
        (1 - ((Finset.univ.filter fun j => BadCopy k alg ω j).card : ℝ) / (3*k))) / D :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum fun ω _ => hpoint ω) hD.le
    _ = (D - (∑ ω : Fin (3*k) → Fin k × Imp,
        ((Finset.univ.filter fun j => BadCopy k alg ω j).card : ℝ)) / (3*k)) / D := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_div]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcard]
    _ ≤ (D - ((k:ℝ)*b)/(3*k)) / D := by
      apply div_le_div_of_nonneg_right _ hD.le
      exact sub_le_sub_left (div_le_div_of_nonneg_right hsum (by positivity)) D
    _ = 1 - b / (3 * (3*(k:ℝ))^(3*k)) := by
      change (D - ((k:ℝ)*b)/(3*k))/D = 1-b/(3*D)
      field_simp

end MatchingHardnessProof


namespace MatchingHardnessProof

noncomputable def blockedCount (k : ℕ) : ℝ :=
  (k:ℝ)^3 * 3 * (3*((k:ℝ)-1))^(3*k-3)

lemma blockedCount_ratio (k : ℕ) (hk : 2 ≤ k) :
    blockedCount k / (3 * (3*(k:ℝ))^(3*k)) =
      (((k:ℝ)-1)/k)^(3*k-3) / 27 := by
  have hk' : (k:ℝ) ≠ 0 := by positivity
  have he : 3*k = (3*k-3)+3 := by omega
  unfold blockedCount
  conv_lhs => arg 2; arg 2; rw [he, pow_add]
  rw [div_pow]
  simp only [mul_pow]
  field_simp
  ring

end MatchingHardnessProof


namespace MatchingHardnessProof
open OnlineStochMatching.Hardness

 theorem single_bad_suffix (alg : OnlineAlg Adv Imp 3) (u : Imp) :
    ∃ v : Imp, ALG cycleEdge alg ![u,v,v] ≤ 2 ∧ OPT cycleEdge ![u,v,v] = 3 := by
  classical
  obtain ⟨v, _, hc, M, hM, he⟩ := exists_repeat u (alg 0 (fun t => Fin.elim0 t) u)
  refine ⟨v, ?_, ?_⟩
  · have hs : matchedAfter cycleEdge alg ![u,v,v] 3 ⊆ neighbors v := by
      apply assigned_property
      intro t advert hp hadj
      apply (mem_neighbors _ _).mpr
      fin_cases t
      · apply hc advert _ hadj
        change alg 0 (prefixOf ![u,v,v] 0) u = some advert at hp
        have hz : prefixOf ![u,v,v] (0 : Fin 3) = (fun t => Fin.elim0 t) := by
          funext t
          exact Fin.elim0 t
        rwa [hz] at hp
      · simpa using hadj
      · simpa using hadj
    exact (Finset.card_le_card hs).trans_eq (card_neighbors v)
  · apply Nat.le_antisymm (OPT_le_n cycleEdge _)
    let s : Fin 3 ↪ Fin 3 := Function.Embedding.refl _
    have hv : IsRealizationMatching cycleEdge ![u,v,v] (positionMatching s M) :=
      positionMatching_valid s M hM cycleEdge _ he
    have hb := matchingSize_le_OPT hv
    rw [positionMatching_size] at hb
    exact hb

 theorem single_cycle_bound (alg : OnlineAlg Adv Imp 3) :
    expectedRatio cycleEdge alg ≤ 26/27 := by
  classical
  let v : Imp → Imp := fun u => Classical.choose (single_bad_suffix alg u)
  let f : Imp → (Fin 3 → Imp) := fun u => ![u,v u,v u]
  have hf : Function.Injective f := by
    intro u other h
    exact congrArg (fun ω => ω 0) h
  let B : Finset (Fin 3 → Imp) := Finset.univ.image f
  have hB : B.card = 3 := by
    rw [Finset.card_image_of_injective _ hf]
    rfl
  have hbad : ∀ ω ∈ B, (ALG cycleEdge alg ω : ℝ) / OPT cycleEdge ω ≤ 2/3 := by
    intro ω hω
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hω
    have hv := Classical.choose_spec (single_bad_suffix alg u)
    change (ALG cycleEdge alg ![u,v u,v u] : ℝ) / OPT cycleEdge ![u,v u,v u] ≤ _
    rw [hv.2]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hv.1) (by norm_num)
  have hsum : (∑ ω : Fin 3 → Imp, (ALG cycleEdge alg ω : ℝ) / OPT cycleEdge ω) ≤ 26 := by
    calc
      _ ≤ ∑ ω : Fin 3 → Imp, (1 - if ω ∈ B then (1:ℝ)/3 else 0) := by
        apply Finset.sum_le_sum
        intro ω _
        by_cases hω : ω ∈ B
        · simp only [if_pos hω]
          linarith [hbad ω hω]
        · simp only [if_neg hω, sub_zero]
          exact ratio_le_one cycleEdge alg ω
      _ = 26 := by
        rw [Finset.sum_sub_distrib]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
          Fintype.card_fin]
        rw [← Finset.sum_filter]
        simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const,
          hB, nsmul_eq_mul]
        norm_num [show Fintype.card Imp = 3 from rfl]
  unfold expectedRatio
  change _ / (3:ℝ)^3 ≤ _
  norm_num only [Nat.reducePow] at *
  linarith

end MatchingHardnessProof


namespace MatchingHardnessProof
open OnlineStochMatching.Hardness Classical

lemma family_deterministic_bound (k : ℕ) (hk : 2 ≤ k)
    (alg : OnlineAlg (Fin k × Adv) (Fin k × Imp) (3*k)) :
    expectedRatio (kCycleEdge k) alg ≤ 1 - Real.exp (-3) / 27 := by
  have hc (j : Fin k) : blockedCount k ≤
      ((Finset.univ.filter fun ω => BadCopy k alg ω j).card : ℝ) := by
    have hh : ((k^3 * 3 * (3*(k-1))^(3*k-3) : ℕ) : ℝ) ≤
        ((Finset.univ.filter fun ω => BadCopy k alg ω j).card : ℝ) := by
      exact_mod_cast bad_copy_count alg j
    simpa only [blockedCount, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one] using hh
  have he := expected_family_of_counts k (by omega) alg (blockedCount k) hc
  rw [blockedCount_ratio k hk] at he
  exact he.trans (sub_le_sub_left
    (div_le_div_of_nonneg_right (occupancy_power_lower k hk) (by norm_num)) 1)

end MatchingHardnessProof

namespace OnlineStochMatching.Hardness

theorem native_matching_recovery :
    (∀ P : PMF (OnlineAlg Adv Imp 3), randExpectedRatio cycleEdge P ≤ 26 / 27) ∧
    ∃ c : ℝ, c < 1 ∧ ∃ K₀ : ℕ, ∀ k : ℕ, K₀ ≤ k →
      ∀ P : PMF (OnlineAlg (Fin k × Adv) (Fin k × Imp) (3 * k)),
        randExpectedRatio (kCycleEdge k) P ≤ c := by
  constructor
  · intro P
    exact MatchingHardnessProof.randomized_bound cycleEdge (26/27)
      MatchingHardnessProof.single_cycle_bound P
  · refine ⟨1-Real.exp (-3)/27, ?_, 2, ?_⟩
    · have := Real.exp_pos (-3)
      linarith
    · intro k hk P
      exact MatchingHardnessProof.randomized_bound (kCycleEdge k) _
        (MatchingHardnessProof.family_deterministic_bound k hk) P

end OnlineStochMatching.Hardness




namespace OnlineStochMatching.Hardness

/-- Theorem 3 (p. 4; details App. B, p. 13). (a) On the 6-cycle instance (`n = 3`), no randomized
online algorithm has expected approximation factor above `26/27`. (b) On the family of `k`
disjoint 6-cycles with uniform arrivals and `n = 3k`, there is a constant `c < 1` such that for
all large `k` no randomized online algorithm has expected approximation factor above `c`; so
the best achievable expected factor does not tend to `1` as `n → ∞`. -/
theorem theorem_3 :
    (∀ P : PMF (OnlineAlg Adv Imp 3), randExpectedRatio cycleEdge P ≤ 26 / 27) ∧
    ∃ c : ℝ, c < 1 ∧ ∃ K₀ : ℕ, ∀ k : ℕ, K₀ ≤ k →
      ∀ P : PMF (OnlineAlg (Fin k × Adv) (Fin k × Imp) (3 * k)),
        randExpectedRatio (kCycleEdge k) P ≤ c := by
  exact OnlineStochMatching.Hardness.native_matching_recovery 

end OnlineStochMatching.Hardness

open OnlineStochMatching.Hardness

theorem solution :
    (∀ P : PMF (OnlineAlg Adv Imp 3), randExpectedRatio cycleEdge P ≤ 26 / 27) ∧
    ∃ c : ℝ, c < 1 ∧ ∃ K₀ : ℕ, ∀ k : ℕ, K₀ ≤ k →
      ∀ P : PMF (OnlineAlg (Fin k × Adv) (Fin k × Imp) (3 * k)),
        randExpectedRatio (kCycleEdge k) P ≤ c := OnlineStochMatching.Hardness.theorem_3
