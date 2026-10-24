-- Prove2me | solution 1 for StrategicAlloc.RRFair.theorem_3_3
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T20:50:42.336874+00:00
-- url     : https://prove2.me/submissions/ebe8d0e0-492b-48d2-9fa2-88dd430733c3

import Mathlib
import Definitions.Def_StrategicAlloc_RRFair_Setting

set_option autoImplicit false

namespace RRF33

open StrategicAlloc.RRFair

variable {n m : ℕ}

/-! ## Infrastructure: rankings and `top` -/

lemma rank_pairwise (c : Fin m → ℝ) :
    (rank c).Pairwise (fun g h => c h ≤ c g) := by
  have h := List.pairwise_mergeSort (le := fun g h : Fin m => decide (c h ≤ c g))
    (by intro a b d hab hbd; simp only [decide_eq_true_eq] at *; linarith)
    (by intro a b; rcases le_total (c b) (c a) with hab | hab <;> simp [hab])
    (List.finRange m)
  unfold rank
  exact h.imp (fun hh => by simpa using hh)

lemma mem_rank (c : Fin m → ℝ) (g : Fin m) : g ∈ rank c := by
  unfold rank
  exact (List.mergeSort_perm _ _).symm.subset (List.mem_finRange g)

lemma top_mem {l : List (Fin m)} {T : Finset (Fin m)} {g : Fin m}
    (h : top l T = some g) : g ∈ T := by
  unfold top at h
  have := List.find?_some h
  simpa using this

lemma top_mem_list {l : List (Fin m)} {T : Finset (Fin m)} {g : Fin m}
    (h : top l T = some g) : g ∈ l := by
  unfold top at h
  exact List.mem_of_find?_eq_some h

lemma top_isSome_rank (c : Fin m → ℝ) {T : Finset (Fin m)} (hT : T.Nonempty) :
    ∃ g, top (rank c) T = some g := by
  obtain ⟨g, hg⟩ := hT
  unfold top
  cases h : (rank c).find? (· ∈ T) with
  | some x => exact ⟨x, rfl⟩
  | none =>
    exfalso
    have := List.find?_eq_none.mp h g (mem_rank c g)
    simp [hg] at this

lemma top_none_iff {l : List (Fin m)} {T : Finset (Fin m)} :
    top l T = none ↔ ∀ g ∈ l, g ∉ T := by
  unfold top
  rw [List.find?_eq_none]
  simp

/-- Independence of irrelevant alternatives for `top`. -/
lemma top_subset {l : List (Fin m)} {T T' : Finset (Fin m)} {g : Fin m}
    (h : top l T = some g) (hg : g ∈ T') (hsub : T' ⊆ T) : top l T' = some g := by
  unfold top at *
  rw [List.find?_eq_some_iff_append] at h ⊢
  obtain ⟨hgT, as, bs, hl, has⟩ := h
  refine ⟨by simpa using hg, as, bs, hl, ?_⟩
  intro a ha
  have := has a ha
  simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at this ⊢
  exact fun h' => this (hsub h')

/-- A good with strictly larger bid than every other good of `T` is the top of `T`. -/
lemma top_rank_of_strict (c : Fin m → ℝ) {T : Finset (Fin m)} {g : Fin m} (hg : g ∈ T)
    (hmax : ∀ h ∈ T, h ≠ g → c h < c g) : top (rank c) T = some g := by
  obtain ⟨x, hx⟩ := top_isSome_rank c ⟨g, hg⟩
  by_cases hxg : x = g
  · rw [hx, hxg]
  exfalso
  have hxT := top_mem hx
  have hlt := hmax x hxT hxg
  unfold top at hx
  rw [List.find?_eq_some_iff_append] at hx
  obtain ⟨_, as, bs, hl, has⟩ := hx
  have hgl : g ∈ rank c := mem_rank c g
  rw [hl] at hgl
  rcases List.mem_append.mp hgl with hga | hgb
  · have := has g hga
    simp [hg] at this
  · rcases List.mem_cons.mp hgb with hgx | hgb'
    · exact hxg hgx.symm
    · have hp := rank_pairwise c
      rw [hl, List.pairwise_append] at hp
      have := (List.pairwise_cons.mp hp.2.1).1 g hgb'
      linarith


/-! ## A list-driven model of Round-Robin -/

section Model
variable [NeZero n]

/-- Round-Robin driven by explicit preference lists `L k` (each agent takes the first
available good of her list). -/
def allocL (L : Fin n → List (Fin m)) : ℕ → Finset (Fin m)
  | 0 => ∅
  | t + 1 => match top (L (agentAt (0 : Fin n) t)) (Finset.univ \ allocL L t) with
    | some g => insert g (allocL L t)
    | none => allocL L t

def pickL (L : Fin n → List (Fin m)) (t : ℕ) : Option (Fin m) :=
  top (L (agentAt (0 : Fin n) t)) (Finset.univ \ allocL L t)

def bundleL (L : Fin n → List (Fin m)) (i : Fin n) (t : ℕ) : Finset (Fin m) :=
  ((Finset.range t).filter (fun s => agentAt (0 : Fin n) s = i)).biUnion
    (fun s => (pickL L s).toFinset)

lemma allocL_succ (L : Fin n → List (Fin m)) (t : ℕ) :
    allocL L (t + 1) = match pickL L t with
      | some g => insert g (allocL L t)
      | none => allocL L t := rfl

lemma alloc_eq (b : Fin n → Fin m → ℝ) (L : Fin n → List (Fin m))
    (h : ∀ k T, top (rank (b k)) T = top (L k) T) (t : ℕ) :
    allocBefore 0 Finset.univ b t = allocL L t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [allocBefore, allocL, ih, h]
    generalize top (L (agentAt 0 t)) (Finset.univ \ allocL L t) = o
    cases o <;> rfl

lemma rr_eq (b : Fin n → Fin m → ℝ) (L : Fin n → List (Fin m))
    (h : ∀ k T, top (rank (b k)) T = top (L k) T) (k : Fin n) :
    roundRobin b k = bundleL L k m := by
  unfold roundRobin rrFrom bundleL
  rw [Finset.card_univ, Fintype.card_fin]
  apply Finset.biUnion_congr rfl
  intro t _
  unfold pick pickL
  rw [alloc_eq b L h, h]

lemma allocL_mono (L : Fin n → List (Fin m)) {s t : ℕ} (hst : s ≤ t) :
    allocL L s ⊆ allocL L t := by
  induction hst with
  | refl => exact le_refl _
  | step _ ih =>
    refine ih.trans ?_
    rw [allocL_succ]
    split
    · exact Finset.subset_insert _ _
    · exact le_refl _

lemma pickL_not_mem {L : Fin n → List (Fin m)} {t : ℕ} {g : Fin m}
    (hp : pickL L t = some g) : g ∉ allocL L t := by
  have := top_mem hp
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at this
  exact this

lemma pickL_mem_succ {L : Fin n → List (Fin m)} {t : ℕ} {g : Fin m}
    (hp : pickL L t = some g) : g ∈ allocL L (t + 1) := by
  rw [allocL_succ, hp]
  exact Finset.mem_insert_self _ _

lemma bundleL_sub (L : Fin n → List (Fin m)) (i : Fin n) (t : ℕ) :
    bundleL L i t ⊆ allocL L t := by
  intro g hg
  unfold bundleL at hg
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range,
    Option.mem_toFinset, Option.mem_def] at hg
  obtain ⟨s, ⟨hs, _⟩, hp⟩ := hg
  exact allocL_mono L (by omega : s + 1 ≤ t) (pickL_mem_succ hp)

lemma bundleL_succ (L : Fin n → List (Fin m)) (i : Fin n) (t : ℕ) :
    bundleL L i (t + 1) =
      if agentAt (0 : Fin n) t = i then bundleL L i t ∪ (pickL L t).toFinset
      else bundleL L i t := by
  unfold bundleL
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.biUnion_insert, Finset.union_comm]
  · rfl

/-- Game-tree check: every play of agent `i` (any choice at each of her steps, or none),
against the fixed lists of the others, gives `i` a total `w`-value at most `B`. -/
def okL (L : Fin n → List (Fin m)) (i : Fin n) (w : Fin m → ℕ) (B : ℕ) :
    ℕ → ℕ → Finset (Fin m) → ℕ → Bool
  | 0, _, _, acc => decide (acc ≤ B)
  | k + 1, t, A, acc =>
    if agentAt (0 : Fin n) t = i then
      okL L i w B k (t + 1) A acc &&
        (List.finRange m).all
          (fun g => decide (g ∈ A) || okL L i w B k (t + 1) (insert g A) (acc + w g))
    else
      match top (L (agentAt (0 : Fin n) t)) (Finset.univ \ A) with
      | some g => okL L i w B k (t + 1) (insert g A) acc
      | none => okL L i w B k (t + 1) A acc

lemma okL_sound (L L' : Fin n → List (Fin m)) (i : Fin n) (w : Fin m → ℕ) (B : ℕ)
    (hL : ∀ k, k ≠ i → L' k = L k) :
    ∀ k t acc, okL L i w B k t (allocL L' t) acc = true →
      acc = ∑ g ∈ bundleL L' i t, w g → ∑ g ∈ bundleL L' i (t + k), w g ≤ B := by
  intro k
  induction k with
  | zero =>
    intro t acc hok hacc
    simp only [okL, decide_eq_true_eq] at hok
    simpa [← hacc] using hok
  | succ k ih =>
    intro t acc hok hacc
    rw [show t + (k + 1) = (t + 1) + k by omega]
    by_cases hi : agentAt (0 : Fin n) t = i
    · simp only [okL, hi, if_true, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
        true_implies, Bool.or_eq_true, decide_eq_true_eq] at hok
      cases hp : pickL L' t with
      | none =>
        apply ih (t + 1) acc
        · rw [allocL_succ, hp]; exact hok.1
        · rw [bundleL_succ, if_pos hi, hp]; simpa using hacc
      | some g =>
        have hg := pickL_not_mem hp
        have hok2 := (hok.2 g).resolve_left hg
        apply ih (t + 1) (acc + w g)
        · rw [allocL_succ, hp]; exact hok2
        · rw [bundleL_succ, if_pos hi, hp]
          have hgb : g ∉ bundleL L' i t := fun h => hg (bundleL_sub L' i t h)
          rw [Option.toFinset_some, Finset.union_comm, ← Finset.insert_eq,
            Finset.sum_insert hgb, hacc, add_comm]
    · have hLk : L' (agentAt (0 : Fin n) t) = L (agentAt (0 : Fin n) t) := hL _ hi
      have hpk : pickL L' t = top (L (agentAt (0 : Fin n) t)) (Finset.univ \ allocL L' t) := by
        unfold pickL; rw [hLk]
      simp only [okL, hi, if_false] at hok
      have hb : bundleL L' i (t + 1) = bundleL L' i t := by rw [bundleL_succ, if_neg hi]
      rw [← hpk] at hok
      cases hp : pickL L' t with
      | none =>
        rw [hp] at hok
        apply ih (t + 1) acc
        · rw [allocL_succ, hp]; exact hok
        · rw [hb]; exact hacc
      | some g =>
        rw [hp] at hok
        apply ih (t + 1) acc
        · rw [allocL_succ, hp]; exact hok
        · rw [hb]; exact hacc

/-- `top` of the bid ranking equals `top` of a list along which the bids strictly decrease. -/
lemma top_rank_eq (c : Fin m → ℝ) (L : List (Fin m))
    (hL : L.Pairwise (fun a b => c b < c a)) (hmem : ∀ g, g ∈ L) (T : Finset (Fin m)) :
    top (rank c) T = top L T := by
  cases hx : top L T with
  | none =>
    rw [top_none_iff] at hx ⊢
    intro g _ hg
    exact hx g (hmem g) hg
  | some g =>
    apply top_rank_of_strict c (top_mem hx)
    intro h hh hne
    unfold top at hx
    rw [List.find?_eq_some_iff_append] at hx
    obtain ⟨_, as, bs, hl, has⟩ := hx
    have hhL := hmem h
    rw [hl] at hhL
    rcases List.mem_append.mp hhL with ha | hb
    · have := has h ha
      simp [hh] at this
    · rcases List.mem_cons.mp hb with h1 | h2
      · exact absurd h1 hne
      · rw [hl, List.pairwise_append] at hL
        exact (List.pairwise_cons.mp hL.2.1).1 h h2

end Model

/-! ## The counterexample: 3 agents, 8 goods -/

/-- Integer bids (higher = preferred). Agent 0 ranks 7,6,3,4,0,1,2,5; agent 1 (the
deviating agent) ranks 1,2,0,3,4,5,6,7; agent 2 ranks 3,6,2,1,5,0,4,7. -/
def fC : Fin 3 → Fin 8 → ℕ := ![![4, 3, 2, 6, 5, 1, 7, 8], ![6, 8, 7, 5, 4, 3, 2, 1],
  ![3, 5, 6, 8, 2, 4, 7, 1]]

def LC : Fin 3 → List (Fin 8) := ![[7, 6, 3, 4, 0, 1, 2, 5], [1, 2, 0, 3, 4, 5, 6, 7],
  [3, 6, 2, 1, 5, 0, 4, 7]]

/-- Valuations: agent 1 values goods 3,4,6,7 at 2, goods 0,1,2 at 1 and good 5 at 0;
agents 0 and 2 value exactly the goods they receive. -/
def wC : Fin 3 → Fin 8 → ℕ := ![![0, 0, 0, 0, 1, 0, 1, 1], ![1, 1, 1, 2, 2, 0, 2, 2],
  ![0, 0, 0, 1, 0, 1, 0, 0]]

noncomputable def bC : Fin 3 → Fin 8 → ℝ := fun k g => (fC k g : ℝ)
noncomputable def vC : Fin 3 → Fin 8 → ℝ := fun k g => (wC k g : ℝ)

lemma LC_pairwise (k : Fin 3) : (LC k).Pairwise (fun a b => fC k b < fC k a) := by
  revert k; decide

lemma LC_mem (k : Fin 3) (g : Fin 8) : g ∈ LC k := by
  revert k g; decide

lemma top_bC (k : Fin 3) (T : Finset (Fin 8)) : top (rank (bC k)) T = top (LC k) T :=
  top_rank_eq (bC k) (LC k)
    ((LC_pairwise k).imp (fun h => by simp only [bC]; exact_mod_cast h)) (LC_mem k) T

lemma val_cast (k : Fin 3) (S : Finset (Fin 8)) : val vC k S = ((∑ g ∈ S, wC k g : ℕ) : ℝ) := by
  unfold val vC; push_cast; rfl

lemma bundle_eq : (bundleL LC 0 8 = {4, 6, 7}) ∧ (bundleL LC 1 8 = {0, 1, 2}) ∧
    (bundleL LC 2 8 = {3, 5}) := by
  decide

lemma okC : okL LC 1 (wC 1) 3 8 0 ∅ 0 = true := by decide

lemma rrC (k : Fin 3) : roundRobin bC k = bundleL LC k 8 := rr_eq bC LC top_bC k

lemma br_one (b' : Fin 8 → ℝ) :
    val vC 1 (roundRobin (Function.update bC 1 b') 1) ≤ 3 := by
  set L' : Fin 3 → List (Fin 8) := Function.update LC 1 (rank b') with hL'
  have htop : ∀ k T, top (rank (Function.update bC 1 b' k)) T = top (L' k) T := by
    intro k T
    by_cases hk : k = 1
    · subst hk; simp [hL']
    · rw [Function.update_of_ne hk, hL', Function.update_of_ne hk, top_bC]
  rw [rr_eq _ L' htop, val_cast]
  have := okL_sound LC L' 1 (wC 1) 3 (fun k hk => by rw [hL', Function.update_of_ne hk])
    8 0 0 okC (by simp [bundleL])
  simp only [zero_add] at this
  exact_mod_cast this

lemma val_le_univ (k : Fin 3) (S : Finset (Fin 8)) : val vC k S ≤ val vC k Finset.univ := by
  unfold val
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    (fun g _ _ => by simp [vC])

lemma pneC : IsPNE roundRobin vC bC := by
  refine ⟨fun k g => by simp [bC], ?_⟩
  intro k b' _
  obtain ⟨h0, h1, h2⟩ := bundle_eq
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by revert k; decide
  rcases hk with rfl | rfl | rfl
  · refine (val_le_univ 0 _).trans (le_of_eq ?_)
    rw [rrC, h0, val_cast, val_cast]; exact congrArg _ (by decide)
  · refine (br_one b').trans (le_of_eq ?_)
    rw [rrC, h1, val_cast, show (∑ x ∈ ({0, 1, 2} : Finset (Fin 8)), wC 1 x) = 3 by decide]
    norm_num
  · refine (val_le_univ 2 _).trans (le_of_eq ?_)
    rw [rrC, h2, val_cast, val_cast]; exact congrArg _ (by decide)

lemma not_ef1C : ¬ IsEF1 vC (roundRobin bC) := by
  intro h
  obtain ⟨h0, h1, -⟩ := bundle_eq
  have hne : (roundRobin bC 0).Nonempty := by rw [rrC, h0]; decide
  obtain ⟨g, hg, hle⟩ := h 1 0 hne
  rw [rrC, h0] at hg hle
  rw [rrC, h1, val_cast, val_cast] at hle
  have hle' : (∑ x ∈ ({4, 6, 7} : Finset (Fin 8)).erase g, wC 1 x) ≤ ∑ x ∈ ({0, 1, 2} : Finset (Fin 8)), wC 1 x := by
    exact_mod_cast hle
  clear hle
  revert g; decide

end RRF33

open StrategicAlloc.RRFair in
theorem solution : ¬ (∀ {n m : ℕ} [NeZero n] (v : Fin n → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (b : Fin n → Fin m → ℝ) (hpne : IsPNE roundRobin v b),
    IsEF1 v (roundRobin b)) := by
  intro h
  exact RRF33.not_ef1C (h (n := 3) (m := 8) RRF33.vC (fun k g => by simp [RRF33.vC]) RRF33.bC
    RRF33.pneC)
