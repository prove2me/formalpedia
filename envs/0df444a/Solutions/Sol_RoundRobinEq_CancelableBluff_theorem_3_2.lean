-- Prove2me | solution 1 for RoundRobinEq.CancelableBluff.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-24T05:02:08.285219+00:00
-- url     : https://prove2.me/submissions/7698f87e-dc4e-4ef8-8ca1-87bb368bbf03

import Mathlib
import Definitions.Def_RoundRobinEq_CancelableBluff_Setting


open RoundRobinEq.CancelableBluff
namespace RRProof
variable {n : ℕ} [NeZero n] {M : Type*} [Fintype M] [DecidableEq M]

omit [Fintype M] in
theorem top_mem {l : List M} {S : Finset M} {g : M} (h : top l S = some g) : g ∈ S := by
  simpa [top] using List.find?_some h

omit [Fintype M] in
theorem top_exists (l : List M) (hl : IsRanking l) (S : Finset M) (hS : S.Nonempty) :
    ∃ g, top l S = some g := by
  cases h : top l S with
  | some g => exact ⟨g, rfl⟩
  | none =>
    have hn := List.find?_eq_none.mp h
    obtain ⟨g, hg⟩ := hS
    exact False.elim (hn g (hl.2 g) (by simpa using hg))

theorem alloc_succ (σ : Fin n → List M) (t : ℕ) :
    allocBefore σ (t+1) = allocBefore σ t ∪ (pick σ t).toFinset := by
  simp only [allocBefore, pick]
  split <;> simp_all [Finset.union_comm]

theorem alloc_mono (σ : Fin n → List M) : Monotone (allocBefore σ) := by
  apply monotone_nat_of_le_succ
  intro t
  rw [alloc_succ]
  exact Finset.subset_union_left

theorem pick_fresh {σ : Fin n → List M} {t : ℕ} {g : M} (h : pick σ t = some g) :
    g ∉ allocBefore σ t := by
  exact (Finset.mem_sdiff.mp (top_mem h)).2

theorem pick_mem_next {σ : Fin n → List M} {t : ℕ} {g : M} (h : pick σ t = some g) :
    g ∈ allocBefore σ (t+1) := by
  rw [alloc_succ, h]
  simp

theorem alloc_card (σ : Fin n → List M) (hσ : ∀ i, IsRanking (σ i)) :
    ∀ t, t ≤ Fintype.card M → (allocBefore σ t).card = t := by
  intro t
  induction t with
  | zero => simp [allocBefore]
  | succ t ih =>
    intro ht
    have hc := ih (by omega)
    obtain ⟨g, -, hg⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := allocBefore σ t) (t := Finset.univ) (by simpa [hc] using (show t < Fintype.card M by omega))
    obtain ⟨a, ha⟩ := top_exists (σ (agentAt n t)) (hσ _) (Finset.univ \ allocBefore σ t)
      ⟨g, by simpa using hg⟩
    change pick σ t = some a at ha
    rw [alloc_succ, ha]
    simp [Finset.union_comm, pick_fresh ha, hc]

theorem pick_exists (σ : Fin n → List M) (hσ : ∀ i, IsRanking (σ i))
    (t : ℕ) (ht : t < Fintype.card M) : ∃ g, pick σ t = some g := by
  have hc := alloc_card σ hσ t (by omega)
  obtain ⟨g, -, hg⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := allocBefore σ t) (t := Finset.univ) (by simpa [hc] using ht)
  exact top_exists _ (hσ _) _ ⟨g, by simpa using hg⟩

noncomputable def runGood (σ : Fin n → List M) (hσ : ∀ i, IsRanking (σ i))
    (t : Fin (Fintype.card M)) : M := Classical.choose (pick_exists σ hσ t t.isLt)

theorem pick_runGood (σ : Fin n → List M) (hσ : ∀ i, IsRanking (σ i))
    (t : Fin (Fintype.card M)) : pick σ t = some (runGood σ hσ t) :=
  Classical.choose_spec (pick_exists σ hσ t t.isLt)

theorem runGood_ne_of_lt (σ : Fin n → List M) (hσ : ∀ i, IsRanking (σ i))
    {s t : Fin (Fintype.card M)} (hst : s < t) : runGood σ hσ s ≠ runGood σ hσ t := by
  intro he
  have hm := pick_mem_next (pick_runGood σ hσ s)
  have hm' := alloc_mono σ (show s.val+1 ≤ t.val by omega) hm
  exact pick_fresh (pick_runGood σ hσ t) (he ▸ hm')

theorem runGood_injective (σ : Fin n → List M) (hσ : ∀ i, IsRanking (σ i)) :
    Function.Injective (runGood σ hσ) := by
  intro s t h
  rcases lt_trichotomy s t with hlt | he | hgt
  · exact False.elim (runGood_ne_of_lt σ hσ hlt h)
  · exact he
  · exact False.elim (runGood_ne_of_lt σ hσ hgt h.symm)

noncomputable def runEquiv (σ : Fin n → List M) (hσ : ∀ i, IsRanking (σ i)) :
    Fin (Fintype.card M) ≃ M :=
  Equiv.ofBijective (runGood σ hσ)
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨runGood_injective σ hσ, by simp⟩)

theorem pick_runEquiv (σ : Fin n → List M) (hσ : ∀ i, IsRanking (σ i))
    (t : Fin (Fintype.card M)) : pick σ t = some (runEquiv σ hσ t) := pick_runGood σ hσ t

theorem alloc_mem_iff (σ : Fin n → List M) (t : ℕ) (g : M) :
    g ∈ allocBefore σ t ↔ ∃ s < t, pick σ s = some g := by
  induction t with
  | zero => simp [allocBefore]
  | succ t ih =>
    rw [alloc_succ, Finset.mem_union, ih]
    simp only [Option.mem_toFinset]
    constructor
    · rintro (⟨s, hs, hp⟩ | hp)
      · exact ⟨s, by omega, hp⟩
      · exact ⟨t, by omega, hp⟩
    · rintro ⟨s, hs, hp⟩
      by_cases he : s = t
      · exact Or.inr (he ▸ hp)
      · exact Or.inl ⟨s, by omega, hp⟩

theorem alloc_runEquiv_iff (σ : Fin n → List M) (hσ : ∀ i, IsRanking (σ i))
    (t : ℕ) (ht : t ≤ Fintype.card M) (j : Fin (Fintype.card M)) :
    runEquiv σ hσ j ∈ allocBefore σ t ↔ j.val < t := by
  rw [alloc_mem_iff]
  constructor
  · rintro ⟨s, hs, hp⟩
    have hs' : s < Fintype.card M := by omega
    have he : runEquiv σ hσ ⟨s, hs'⟩ = runEquiv σ hσ j := by
      have h := pick_runEquiv σ hσ ⟨s, hs'⟩
      rw [hp] at h
      exact (Option.some.inj h).symm
    have hv := congrArg Fin.val ((runEquiv σ hσ).injective he)
    simpa using hv ▸ hs
  · intro hj
    exact ⟨j.val, hj, pick_runEquiv σ hσ j⟩

theorem pickOrder_eq (σ : Fin n → List M) (hσ : ∀ i, IsRanking (σ i)) :
    pickOrder σ = List.ofFn (runEquiv σ hσ) := by
  have hr : (List.finRange (Fintype.card M)).map Fin.val = List.range (Fintype.card M) := by
    apply List.ext_getElem
    · simp
    · intro j h₁ h₂
      simp
  rw [pickOrder, ← hr, List.filterMap_map, List.ofFn_eq_map]
  apply List.filterMap_eq_map_iff_forall_eq_some.mpr
  intro j _
  exact pick_runEquiv σ hσ j

theorem pickOrder_ranking (σ : Fin n → List M) (hσ : ∀ i, IsRanking (σ i)) :
    IsRanking (pickOrder σ) := by
  rw [pickOrder_eq σ hσ]
  exact ⟨List.nodup_ofFn.mpr (runEquiv σ hσ).injective,
    fun g => List.mem_ofFn.mpr ((runEquiv σ hσ).surjective g)⟩

theorem roundRobin_mem_iff (σ : Fin n → List M) (i : Fin n) (g : M) :
    g ∈ roundRobin σ i ↔ ∃ t < Fintype.card M, agentAt n t = i ∧ pick σ t = some g := by
  simp [roundRobin, and_assoc]

def ownIndex (k : ℕ) (hm : Fintype.card M = k*n) (i : Fin n) (r : Fin k) :
    Fin (Fintype.card M) := ⟨r.val*n+i.val, by rw [hm]; nlinarith [i.isLt, r.isLt]⟩

noncomputable def ownPick (σ : Fin n → List M) (hσ : ∀ i, IsRanking (σ i))
    (k : ℕ) (hm : Fintype.card M = k*n) (i : Fin n) (r : Fin k) : M :=
  runEquiv σ hσ (ownIndex k hm i r)

theorem ownPick_injective (σ : Fin n → List M) (hσ : ∀ i, IsRanking (σ i))
    (k : ℕ) (hm : Fintype.card M = k*n) (i : Fin n) :
    Function.Injective (ownPick σ hσ k hm i) := by
  intro r s he
  have h := congrArg Fin.val ((runEquiv σ hσ).injective he)
  change r.val*n+i.val=s.val*n+i.val at h
  apply Fin.ext
  have hn := Nat.pos_of_ne_zero (NeZero.ne n)
  nlinarith

theorem ownPick_image (σ : Fin n → List M) (hσ : ∀ i, IsRanking (σ i))
    (k : ℕ) (hm : Fintype.card M = k*n) (i : Fin n) :
    Finset.univ.image (ownPick σ hσ k hm i) = roundRobin σ i := by
  ext g
  rw [roundRobin_mem_iff]
  constructor
  · rintro hg
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hg
    refine ⟨r.val*n+i.val, (ownIndex k hm i r).isLt, ?_, pick_runEquiv σ hσ (ownIndex k hm i r)⟩
    apply Fin.ext
    simp [agentAt, Nat.add_mod, Nat.mod_eq_of_lt i.isLt]
  · rintro ⟨t, ht, hi, hp⟩
    have hiv : t%n=i.val := congrArg Fin.val hi
    have hn := Nat.pos_of_ne_zero (NeZero.ne n)
    have hr : t/n<k := (Nat.div_lt_iff_lt_mul hn).2 (by simpa [hm] using ht)
    let r : Fin k := ⟨t/n, hr⟩
    have he : (ownIndex k hm i r).val=t := by
      dsimp [ownIndex, r]
      have hd := Nat.mod_add_div t n
      nlinarith
    refine Finset.mem_image.mpr ⟨r, Finset.mem_univ _, ?_⟩
    have hh := pick_runEquiv σ hσ (ownIndex k hm i r)
    rw [he, hp] at hh
    exact (Option.some.inj hh).symm

theorem roundRobin_card (σ : Fin n → List M) (hσ : ∀ i, IsRanking (σ i))
    (k : ℕ) (hm : Fintype.card M = k*n) (i : Fin n) : (roundRobin σ i).card=k := by
  rw [← ownPick_image σ hσ k hm i, Finset.card_image_of_injective _
    (ownPick_injective σ hσ k hm i)]
  simp

end RRProof

open RoundRobinEq.CancelableBluff
namespace RRProof
variable {n : ℕ} [NeZero n] {M : Type*} [Fintype M] [DecidableEq M]

omit [Fintype M] in
theorem top_idx_le (l : List M) (hl : IsRanking l) (S : Finset M) {g a : M}
    (hg : top l S = some g) (ha : a ∈ S) : l.idxOf g ≤ l.idxOf a := by
  obtain ⟨-, j, hj, he, hb⟩ := List.find?_eq_some_iff_getElem.mp hg
  have hjg : l.idxOf g = j := by
    rw [← he]
    exact hl.1.idxOf_getElem j hj
  by_contra hn
  have hlt : l.idxOf a < j := by omega
  have hh := hb (l.idxOf a) hlt
  have hm := hl.2 a
  simp [List.getElem_idxOf, ha] at hh

theorem bluff_ranking (σ : Fin n → List M) (hσ : ∀ i, IsRanking (σ i)) :
    ∀ i, IsRanking (bluff σ i) := fun _ => pickOrder_ranking σ hσ

theorem bluff_pick_of_alloc_eq (σ : Fin n → List M) (hσ : ∀ i, IsRanking (σ i))
    (t : Fin (Fintype.card M)) (he : allocBefore (bluff σ) t = allocBefore σ t) :
    pick (bluff σ) t = some (runEquiv σ hσ t) := by
  simp only [pick, bluff, pickOrder_eq σ hσ, he, top]
  apply List.find?_eq_some_iff_getElem.mpr
  refine ⟨?_, t.val, by simp, by simp, ?_⟩
  · simp [alloc_runEquiv_iff σ hσ t (Nat.le_of_lt t.isLt) t]
  · intro j hj
    have hjm : j < Fintype.card M := by omega
    simp only [List.getElem_ofFn]
    have ha : runEquiv σ hσ ⟨j, hjm⟩ ∈ allocBefore σ t :=
      (alloc_runEquiv_iff σ hσ t (Nat.le_of_lt t.isLt) _).2 hj
    simp [ha]

theorem alloc_bluff (σ : Fin n → List M) (hσ : ∀ i, IsRanking (σ i)) :
    ∀ t, t ≤ Fintype.card M → allocBefore (bluff σ) t = allocBefore σ t := by
  intro t
  induction t with
  | zero => simp [allocBefore]
  | succ t ih =>
    intro ht
    have hlt : t < Fintype.card M := by omega
    have he := ih (by omega)
    rw [alloc_succ, alloc_succ, he, bluff_pick_of_alloc_eq σ hσ ⟨t, hlt⟩ he,
      pick_runEquiv σ hσ ⟨t, hlt⟩]

theorem pick_bluff (σ : Fin n → List M) (hσ : ∀ i, IsRanking (σ i))
    (t : ℕ) (ht : t < Fintype.card M) : pick (bluff σ) t = pick σ t := by
  rw [bluff_pick_of_alloc_eq σ hσ ⟨t, ht⟩ (alloc_bluff σ hσ t (by omega)),
    pick_runEquiv σ hσ ⟨t, ht⟩]

theorem roundRobin_bluff (σ : Fin n → List M) (hσ : ∀ i, IsRanking (σ i)) :
    roundRobin (bluff σ) = roundRobin σ := by
  funext i
  ext g
  simp only [roundRobin_mem_iff]
  constructor <;> rintro ⟨t, ht, hi, hp⟩
  · exact ⟨t, ht, hi, by rwa [pick_bluff σ hσ t ht] at hp⟩
  · exact ⟨t, ht, hi, by rwa [pick_bluff σ hσ t ht]⟩

theorem truthful_pick_best (v : Fin n → Finset M → ℝ) (σ : Fin n → List M)
    (hσ : IsStrictTruthful v σ) (t : Fin (Fintype.card M)) (a : M)
    (ha : a ∉ allocBefore σ t) :
    v (agentAt n t) {a} ≤ v (agentAt n t) {runEquiv σ (fun i => (hσ i).1) t} := by
  by_contra hn
  have hv := (hσ (agentAt n t)).2 a (runEquiv σ (fun i => (hσ i).1) t)
    (lt_of_not_ge hn)
  have hi := top_idx_le (σ (agentAt n t)) (hσ _).1 _
    (pick_runEquiv σ (fun i => (hσ i).1) t) (a := a) (by simpa using ha)
  omega

theorem truthful_tail_domination (v : Fin n → Finset M → ℝ) (σ : Fin n → List M)
    (hσ : IsStrictTruthful v σ) (k : ℕ) (hm : Fintype.card M=k*n) (i : Fin n)
    (r : Fin k) (j : Fin (Fintype.card M)) (hj : r.val*n+i.val≤j.val) :
    v i {runEquiv σ (fun a => (hσ a).1) j} ≤
      v i {ownPick σ (fun a => (hσ a).1) k hm i r} := by
  have hi : agentAt n (ownIndex k hm i r).val=i := by
    apply Fin.ext
    simp [agentAt, ownIndex, Nat.add_mod, Nat.mod_eq_of_lt i.isLt]
  have hh := truthful_pick_best v σ hσ (ownIndex k hm i r)
    (runEquiv σ (fun a => (hσ a).1) j) ?_
  · simpa [hi, ownPick] using hh
  · rw [alloc_runEquiv_iff σ (fun a => (hσ a).1) _
      (Nat.le_of_lt (ownIndex k hm i r).isLt)]
    exact Nat.not_lt.mpr hj

theorem idxOf_runEquiv (σ : Fin n → List M) (hσ : ∀ i, IsRanking (σ i))
    (j : Fin (Fintype.card M)) : (pickOrder σ).idxOf (runEquiv σ hσ j)=j.val := by
  rw [pickOrder_eq σ hσ]
  have he : (List.ofFn (runEquiv σ hσ))[j.val]'(by simp) =
    runEquiv σ hσ j := by simp
  rw [← he]
  exact (List.nodup_ofFn.mpr (runEquiv σ hσ).injective).idxOf_getElem _ _

theorem top_common_rank (σ : Fin n → List M) (hσ : ∀ i, IsRanking (σ i))
    (S : Finset M) {s t : Fin (Fintype.card M)}
    (hp : top (pickOrder σ) S = some (runEquiv σ hσ s))
    (ht : runEquiv σ hσ t ∈ S) : s ≤ t := by
  have hh := top_idx_le (pickOrder σ) (pickOrder_ranking σ hσ) S hp ht
  simpa [idxOf_runEquiv σ hσ] using hh

end RRProof

set_option autoImplicit false
namespace RRProof

noncomputable def ownTimes (n k : ℕ) (i : Fin n) : Finset (Fin (k*n)) :=
  Finset.univ.filter (fun t => t.val % n = i.val)
noncomputable def ownRanks {n k : ℕ} (w : Fin (k*n) ≃ Fin (k*n)) (i : Fin n) :
    Finset (Fin (k*n)) := (ownTimes n k i).image w

lemma residue_prefix_card {n : ℕ} (hn : 0<n) (i : Fin n) (q : ℕ) :
    ((Finset.range (q*n+i.val)).filter (fun t => t%n=i.val)).card=q := by
  classical
  symm
  calc
    q = (Finset.range q).card := (Finset.card_range q).symm
    _ = ((Finset.range (q*n+i.val)).filter (fun t => t%n=i.val)).card := by
      apply Finset.card_bij (fun a _ => a*n+i.val)
      · intro a ha
        simp only [Finset.mem_range] at ha
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_range.mpr ?_, ?_⟩
        · nlinarith
        · simp [Nat.add_mod, Nat.mod_eq_of_lt i.isLt]
      · intro a ha b hb he
        nlinarith
      · intro b hb
        obtain ⟨hb, hr⟩ := Finset.mem_filter.mp hb
        have hbl := Finset.mem_range.mp hb
        have he : b = (b/n)*n+i.val := by
          have hh := Nat.mod_add_div b n
          rw [hr] at hh
          nlinarith
        refine ⟨b/n, Finset.mem_range.mpr ?_, he.symm⟩
        nlinarith

lemma ownTimes_card {n k : ℕ} [NeZero n] (i : Fin n) :
    (ownTimes n k i).card=k := by
  classical
  have hn : 0<n := Nat.pos_of_ne_zero (NeZero.ne n)
  apply (Finset.card_bij (fun a (_ : a ∈ ownTimes n k i) => a.val/n) ?_ ?_ ?_).trans
    (Finset.card_range k)
  · intro a ha
    apply Finset.mem_range.mpr
    exact (Nat.div_lt_iff_lt_mul hn).mpr a.isLt
  · intro a ha b hb he
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    apply Fin.ext
    have h1 := Nat.mod_add_div a.val n
    have h2 := Nat.mod_add_div b.val n
    rw [ha', he] at h1
    rw [hb'] at h2
    omega
  · intro b hb
    have hb' := Finset.mem_range.mp hb
    have hlt : b*n+i.val<k*n := by nlinarith [i.isLt]
    refine ⟨⟨b*n+i.val,hlt⟩, ?_, ?_⟩
    · simp [ownTimes, Nat.add_mod, Nat.mod_eq_of_lt i.isLt]
    · change (b*n+i.val)/n=b
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn]
      simp [Nat.div_eq_of_lt i.isLt]

lemma ownRanks_card {n k : ℕ} [NeZero n]
    (w : Fin (k*n) ≃ Fin (k*n)) (i : Fin n) : (ownRanks w i).card=k := by
  rw [ownRanks, Finset.card_image_of_injective _ w.injective, ownTimes_card]

lemma own_before_card {n k : ℕ} [NeZero n] (i : Fin n) (t : Fin (k*n))
    (ht : t.val%n=i.val) :
    ((Finset.Iio t).filter (fun s => s.val%n=i.val)).card=t.val/n := by
  classical
  have hn : 0<n := Nat.pos_of_ne_zero (NeZero.ne n)
  have he : t.val=t.val/n*n+i.val := by
    have hh:=Nat.mod_add_div t.val n
    rw [ht] at hh
    nlinarith
  calc
    _ = ((Finset.range t.val).filter (fun s => s%n=i.val)).card := by
      apply Finset.card_bij (fun s _ => s.val)
      · intro s hs
        simpa using hs
      · intro a ha b hb hab
        exact Fin.ext hab
      · intro b hb
        have hbt : b<t.val := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
        refine ⟨⟨b,lt_trans hbt t.isLt⟩, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_Iio.mpr hbt, (Finset.mem_filter.mp hb).2⟩
    _ = t.val/n := by
      calc
        _ = ((Finset.range (t.val/n*n+i.val)).filter (fun s=>s%n=i.val)).card := by rw [←he]
        _ = _ := residue_prefix_card hn i (t.val/n)

lemma own_through_card {n k : ℕ} [NeZero n] (i : Fin n) (t : Fin (k*n))
    (ht : t.val%n=i.val) :
    ((Finset.Iic t).filter (fun s => s.val%n=i.val)).card=t.val/n+1 := by
  classical
  have he : (Finset.Iic t).filter (fun s => s.val%n=i.val) =
      insert t ((Finset.Iio t).filter (fun s => s.val%n=i.val)) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_insert, Finset.mem_Iio]
    constructor
    · rintro ⟨hs, hr⟩
      rcases lt_or_eq_of_le hs with hlt | rfl
      · exact Or.inr ⟨hlt,hr⟩
      · exact Or.inl rfl
    · rintro (rfl | ⟨hs,hr⟩)
      · exact ⟨le_rfl,ht⟩
      · exact ⟨le_of_lt hs,hr⟩
  rw [he, Finset.card_insert_of_notMem (by simp), own_before_card i t ht]

lemma other_before_card {n k : ℕ} [NeZero n] (i : Fin n) (t : Fin (k*n))
    (ht : t.val%n=i.val) :
    ((Finset.Iio t).filter (fun s => s.val%n≠i.val)).card =
      (t.val/n)*(n-1)+i.val := by
  classical
  have hh := Finset.card_filter_add_card_filter_not (s := Finset.Iio t)
    (fun s : Fin (k*n) => s.val%n=i.val)
  rw [own_before_card i t ht] at hh
  have hc : (Finset.Iio t).card=t.val := by simp
  rw [hc] at hh
  have hd:=Nat.mod_add_div t.val n
  rw [ht] at hd
  have hn : 0<n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hn' : n=(n-1)+1 := by omega
  have hm := congrArg (fun a : ℕ => a*(t.val/n)) hn'
  nlinarith

lemma sorted_own_rank_lower {n k : ℕ} [NeZero n]
    (w : Fin (k*n) ≃ Fin (k*n)) (i : Fin n)
    (hgreedy : ∀ s t, s<t → s.val%n≠i.val → w s<w t) (r : Fin k) :
    r.val*n+i.val ≤ ((ownRanks w i).orderEmbOfFin (ownRanks_card w i) r).val := by
  classical
  let e := (ownRanks w i).orderEmbOfFin (ownRanks_card w i)
  let Q := (Finset.Iic r).image e
  let L := Q.image w.symm
  have hQcard : Q.card=r.val+1 := by
    dsimp only [Q]
    rw [Finset.card_image_of_injective _ e.injective]
    simp
  have hLcard : L.card=r.val+1 := by
    dsimp only [L]
    rw [Finset.card_image_of_injective _ w.symm.injective,hQcard]
  have hLnonempty : L.Nonempty := Finset.card_pos.mp (by omega)
  let t := L.max' hLnonempty
  have htL : t∈L := Finset.max'_mem L hLnonempty
  have hLt : ∀ s∈L,s≤t := fun s hs => Finset.le_max' L s hs
  have hLown : ∀ s∈L,s.val%n=i.val := by
    intro s hs
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
    have he : e b∈ownRanks w i := Finset.orderEmbOfFin_mem _ _ b
    obtain ⟨u,hu,heu⟩ := Finset.mem_image.mp he
    rw [← heu,w.symm_apply_apply]
    exact (Finset.mem_filter.mp hu).2
  have ht : t.val%n=i.val := hLown t htL
  have hQle : ∀ a∈Q,a≤e r := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
    exact e.monotone (Finset.mem_Iic.mp hb)
  have hwt : w t∈Q := by
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp htL
    rw [←he,w.apply_symm_apply]
    exact ha
  have hsubset : L⊆(Finset.Iic t).filter (fun s=>s.val%n=i.val) := by
    intro s hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr (hLt s hs),hLown s hs⟩
  have hcardle := Finset.card_le_card hsubset
  rw [hLcard,own_through_card i t ht] at hcardle
  have hqr : r.val≤t.val/n := by omega
  let O := (Finset.Iio t).filter (fun s=>s.val%n≠i.val)
  have hOcard : (O.image w).card=(t.val/n)*(n-1)+i.val := by
    rw [Finset.card_image_of_injective _ w.injective]
    exact other_before_card i t ht
  have hd : Disjoint (O.image w) Q := by
    rw [Finset.disjoint_left]
    intro a ha hq
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp ha
    have hsL : s∈L := by
      exact Finset.mem_image.mpr ⟨w s,hq,w.symm_apply_apply s⟩
    exact (Finset.mem_filter.mp hs).2 (hLown s hsL)
  have hU : O.image w ∪ Q ⊆ Finset.Iic (e r) := by
    intro a ha
    apply Finset.mem_Iic.mpr
    rcases Finset.mem_union.mp ha with ho | hq
    · obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp ho
      obtain ⟨hst,hsn⟩ := Finset.mem_filter.mp hs
      exact (le_of_lt (hgreedy s t (Finset.mem_Iio.mp hst) hsn)).trans (hQle _ hwt)
    · exact hQle a hq
  have hc := Finset.card_le_card hU
  rw [Finset.card_union_of_disjoint hd,hOcard,hQcard] at hc
  have hIc : (Finset.Iic (e r)).card=(e r).val+1 := by simp
  rw [hIc] at hc
  have hn : 0<n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hn' : n=(n-1)+1 := by omega
  change r.val*n+i.val≤(e r).val
  nlinarith [Nat.mul_le_mul_right (n-1) hqr]

end RRProof

open RoundRobinEq.CancelableBluff
namespace RRProof
variable {n : ℕ} [NeZero n] {M : Type*} [Fintype M] [DecidableEq M]

noncomputable def runKN (σ : Fin n → List M) (hσ : ∀ i, IsRanking (σ i))
    (k : ℕ) (hm : Fintype.card M=k*n) : Fin (k*n) ≃ M :=
  (finCongr hm.symm).trans (runEquiv σ hσ)

theorem pick_runKN (σ : Fin n → List M) (hσ : ∀ i, IsRanking (σ i))
    (k : ℕ) (hm : Fintype.card M=k*n) (t : Fin (k*n)) :
    pick σ t.val = some (runKN σ hσ k hm t) :=
  pick_runEquiv σ hσ ((finCongr hm.symm) t)

theorem bundle_runKN_image (σ : Fin n → List M) (hσ : ∀ i, IsRanking (σ i))
    (k : ℕ) (hm : Fintype.card M=k*n) (i : Fin n) :
    ((Finset.univ : Finset (Fin (k*n))).filter (fun t => t.val%n=i.val)).image
      (runKN σ hσ k hm) = roundRobin σ i := by
  ext g
  rw [roundRobin_mem_iff]
  constructor
  · rintro hg
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hg
    have hi := (Finset.mem_filter.mp ht).2
    refine ⟨t.val, by simp [hm], ?_, pick_runKN σ hσ k hm t⟩
    exact Fin.ext hi
  · rintro ⟨t, ht, hi, hp⟩
    let s : Fin (k*n) := ⟨t, by simpa [hm] using ht⟩
    refine Finset.mem_image.mpr ⟨s, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact congrArg Fin.val hi
    · have hh := pick_runKN σ hσ k hm s
      rw [hp] at hh
      exact (Option.some.inj hh).symm

theorem deviation_ranking (σ : Fin n → List M) (hσ : ∀ i, IsRanking (σ i))
    (i : Fin n) (τ : List M) (hτ : IsRanking τ) :
    ∀ a, IsRanking (Function.update (bluff σ) i τ a) := by
  intro a
  by_cases ha : a=i
  · subst a; simpa using hτ
  · simpa [Function.update_of_ne ha] using bluff_ranking σ hσ a

noncomputable def deviationPerm (σ : Fin n → List M) (hσ : ∀ i, IsRanking (σ i))
    (k : ℕ) (hm : Fintype.card M=k*n) (i : Fin n) (τ : List M) (hτ : IsRanking τ) :
    Fin (k*n) ≃ Fin (k*n) :=
  (runKN (Function.update (bluff σ) i τ) (deviation_ranking σ hσ i τ hτ) k hm).trans
    (runKN σ hσ k hm).symm

theorem deviationPerm_apply (σ : Fin n → List M) (hσ : ∀ i, IsRanking (σ i))
    (k : ℕ) (hm : Fintype.card M=k*n) (i : Fin n) (τ : List M) (hτ : IsRanking τ)
    (t : Fin (k*n)) :
    runKN σ hσ k hm (deviationPerm σ hσ k hm i τ hτ t) =
      runKN (Function.update (bluff σ) i τ) (deviation_ranking σ hσ i τ hτ) k hm t := by
  simp [deviationPerm]

theorem deviationPerm_greedy (σ : Fin n → List M) (hσ : ∀ i, IsRanking (σ i))
    (k : ℕ) (hm : Fintype.card M=k*n) (i : Fin n) (τ : List M) (hτ : IsRanking τ)
    (s t : Fin (k*n)) (hst : s<t) (hsi : s.val%n≠i.val) :
    deviationPerm σ hσ k hm i τ hτ s < deviationPerm σ hσ k hm i τ hτ t := by
  let d := Function.update (bluff σ) i τ
  let hd := deviation_ranking σ hσ i τ hτ
  let w := deviationPerm σ hσ k hm i τ hτ
  have hi : agentAt n s.val≠i := fun h => hsi (congrArg Fin.val h)
  have hp := pick_runKN d hd k hm s
  change top (Function.update (bluff σ) i τ (agentAt n s.val))
    (Finset.univ \ allocBefore d s.val) = _ at hp
  rw [Function.update_of_ne hi] at hp
  change top (pickOrder σ) (Finset.univ \ allocBefore d s.val) = _ at hp
  have heS := deviationPerm_apply σ hσ k hm i τ hτ s
  have heT := deviationPerm_apply σ hσ k hm i τ hτ t
  rw [← heS] at hp
  have ht : runKN σ hσ k hm (w t) ∈ Finset.univ \ allocBefore d s.val := by
    rw [show runKN σ hσ k hm (w t)=runKN d hd k hm t from heT]
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    change runEquiv d hd ((finCongr hm.symm) t) ∉ allocBefore d s.val
    rw [alloc_runEquiv_iff d hd s.val (by simp [hm])]
    exact Nat.not_lt.mpr (Nat.le_of_lt hst)
  have hle := top_common_rank σ hσ (Finset.univ \ allocBefore d s.val) hp ht
  have hle' : w s≤w t := hle
  exact lt_of_le_of_ne hle' (fun he => (ne_of_lt hst) (w.injective he))

theorem deviation_rank_image (σ : Fin n → List M) (hσ : ∀ i, IsRanking (σ i))
    (k : ℕ) (hm : Fintype.card M=k*n) (i : Fin n) (τ : List M) (hτ : IsRanking τ) :
    (ownRanks (deviationPerm σ hσ k hm i τ hτ) i).image (runKN σ hσ k hm) =
      roundRobin (Function.update (bluff σ) i τ) i := by
  rw [ownRanks, Finset.image_image]
  have he : (fun t => runKN σ hσ k hm (deviationPerm σ hσ k hm i τ hτ t)) =
      runKN (Function.update (bluff σ) i τ) (deviation_ranking σ hσ i τ hτ) k hm := by
    funext t
    exact deviationPerm_apply σ hσ k hm i τ hτ t
  simp only [Function.comp_def]
  rw [he]
  exact bundle_runKN_image _ _ k hm i

theorem deviation_singleton_enumeration (v : Fin n → Finset M → ℝ)
    (σ : Fin n → List M) (hσ : IsStrictTruthful v σ)
    (k : ℕ) (hm : Fintype.card M=k*n) (i : Fin n) (τ : List M) (hτ : IsRanking τ) :
    ∃ y : Fin k → M, Function.Injective y ∧
      Finset.univ.image y = roundRobin (Function.update (bluff σ) i τ) i ∧
      ∀ r, v i {y r} ≤ v i {ownPick σ (fun a => (hσ a).1) k hm i r} := by
  let hr := fun a => (hσ a).1
  let w := deviationPerm σ hr k hm i τ hτ
  let e := (ownRanks w i).orderEmbOfFin (ownRanks_card w i)
  let y : Fin k → M := fun r => runKN σ hr k hm (e r)
  refine ⟨y, (runKN σ hr k hm).injective.comp e.injective, ?_, ?_⟩
  · change (Finset.univ.image (fun r => runKN σ hr k hm (e r))) = _
    change Finset.image ((runKN σ hr k hm) ∘ e) Finset.univ = _
    rw [← Finset.image_image, Finset.image_orderEmbOfFin_univ]
    exact deviation_rank_image σ hr k hm i τ hτ
  · intro r
    have hj := sorted_own_rank_lower w i (deviationPerm_greedy σ hr k hm i τ hτ) r
    exact truthful_tail_domination v σ hσ k hm i r ((finCongr hm.symm) (e r)) hj

theorem domination_ordering (k : ℕ) (hm : Fintype.card M=k*n)
    (v : Fin n → Finset M → ℝ) (σ : Fin n → List M) (hσ : IsStrictTruthful v σ)
    (i : Fin n) (τ : List M) (hτ : IsRanking τ) :
    ∃ y : Fin k → M, Function.Injective y ∧
      Finset.univ.image y=roundRobin (Function.update (bluff σ) i τ) i ∧
      ∀ r : Fin k, ∃ h : M, (pickOrder σ)[r.val*n+i.val]?=some h ∧ v i {y r}≤v i {h} := by
  obtain ⟨y,hy,he,hv⟩ := deviation_singleton_enumeration v σ hσ k hm i τ hτ
  refine ⟨y,hy,he,fun r=>⟨ownPick σ (fun a=>(hσ a).1) k hm i r,?_,hv r⟩⟩
  rw [pickOrder_eq σ (fun a=>(hσ a).1)]
  simp [ownPick, ownIndex,
    show r.val*n+i.val<Fintype.card M from (ownIndex k hm i r).isLt]

end RRProof

set_option autoImplicit false
namespace RRProof
open RoundRobinEq.CancelableBluff
variable {M : Type*} [DecidableEq M]

lemma common_insert_le (v : Finset M → ℝ) (hc : IsCancelable v)
    (A B : Finset M) (g : M) (hg : g ∉ A ∪ B) (h : v A ≤ v B) :
    v (insert g A) ≤ v (insert g B) := by
  by_contra hn
  have hh := hc A B g hg (lt_of_not_ge hn)
  exact (not_lt_of_ge h) hh

lemma common_union_le (v : Finset M → ℝ) (hc : IsCancelable v)
    (A B R : Finset M) (hR : Disjoint R (A ∪ B)) (h : v A ≤ v B) :
    v (A ∪ R) ≤ v (B ∪ R) := by
  induction R using Finset.induction_on with
  | empty => simpa using h
  | @insert g R hg ih =>
    have hd := Finset.disjoint_insert_left.mp hR
    have hi := ih hd.2
    have hf : g ∉ (A ∪ R) ∪ (B ∪ R) := by
      simp only [Finset.mem_union, not_or] at hd ⊢
      simp_all
    simpa [Finset.union_insert] using common_insert_le v hc (A ∪ R) (B ∪ R) g hf hi

lemma dominated_bijOn_le (v : Finset M → ℝ) (hc : IsCancelable v)
    (X Y : Finset M) (φ : M → M) (hb : Set.BijOn φ (↑Y) (↑X))
    (hv : ∀ y ∈ Y, v {y} ≤ v {φ y}) : v Y ≤ v X := by
  classical
  induction X using Finset.strongInductionOn generalizing Y φ with
  | _ X ih =>
    by_cases hXY : ∃ g, g ∈ X ∧ g ∈ Y
    · obtain ⟨g, hgX, hgY⟩ := hXY
      let ψ : M → M := fun y => Equiv.swap g (φ g) (φ y)
      have hφg : φ g ∈ X := hb.mapsTo hgY
      have hψg : ψ g = g := by simp [ψ]
      have hs : Set.BijOn (Equiv.swap g (φ g)) (↑X : Set M) (↑X : Set M) := by
        refine ⟨?_, (Equiv.swap g (φ g)).injective.injOn, ?_⟩
        · intro x hx
          by_cases h1 : x = g
          · simpa [h1] using hφg
          by_cases h2 : x = φ g
          · simpa [h2] using hgX
          simpa [Equiv.swap_apply_of_ne_of_ne h1 h2] using hx
        · intro x hx
          refine ⟨Equiv.swap g (φ g) x, ?_, by simp⟩
          by_cases h1 : x = g
          · simpa [h1] using hφg
          by_cases h2 : x = φ g
          · simpa [h2] using hgX
          simpa [Equiv.swap_apply_of_ne_of_ne h1 h2] using hx
      have hbψ : Set.BijOn ψ (↑Y) (↑X) := hs.comp hb
      have hvψ : ∀ y ∈ Y, v {y} ≤ v {ψ y} := by
        intro y hy
        by_cases h1 : φ y = g
        · simpa [ψ, h1] using (hv y hy).trans (by simpa [h1] using hv g hgY)
        by_cases h2 : φ y = φ g
        · have hyEq : y = g := hb.injOn hy hgY h2
          subst y
          simp [hψg]
        simpa [ψ, Equiv.swap_apply_of_ne_of_ne h1 h2] using hv y hy
      have hbr : Set.BijOn ψ (↑(Y.erase g)) (↑(X.erase g)) := by
        simpa [hψg] using hbψ.sdiff_singleton hgY
      have hvr : ∀ y ∈ Y.erase g, v {y} ≤ v {ψ y} := fun y hy => hvψ y (Finset.mem_of_mem_erase hy)
      have hsmall := ih (X.erase g) (Finset.erase_ssubset hgX) (Y.erase g) ψ hbr hvr
      have hf : g ∉ Y.erase g ∪ X.erase g := by simp
      simpa [Finset.insert_erase hgY, Finset.insert_erase hgX] using
        common_insert_le v hc (Y.erase g) (X.erase g) g hf hsmall
    · have hd : Disjoint X Y := by
        rw [Finset.disjoint_left]
        intro g hgX hgY
        exact hXY ⟨g, hgX, hgY⟩
      by_cases hY : Y.Nonempty
      · obtain ⟨y, hy⟩ := hY
        have hx : φ y ∈ X := hb.mapsTo hy
        have hbr : Set.BijOn φ (↑(Y.erase y)) (↑(X.erase (φ y))) := by
          simpa using hb.sdiff_singleton hy
        have hsmall := ih (X.erase (φ y)) (Finset.erase_ssubset hx)
          (Y.erase y) φ hbr (fun z hz => hv z (Finset.mem_of_mem_erase hz))
        have hxy : φ y ∉ Y := fun hm => Finset.disjoint_left.mp hd hx hm
        have h1 := common_insert_le v hc (Y.erase y) (X.erase (φ y)) (φ y)
          (by simp [hxy]) hsmall
        have h2 := common_union_le v hc {y} {φ y} (Y.erase y)
          (by rw [Finset.disjoint_left]; intro z hz; simp only [Finset.mem_union, Finset.mem_singleton];
              intro hh; rcases hh with rfl | rfl
              · simp at hz
              · exact hxy (Finset.mem_of_mem_erase hz)) (hv y hy)
        have h2' : v Y ≤ v (insert (φ y) (Y.erase y)) := by
          simpa [Finset.singleton_union, Finset.insert_erase hy] using h2
        exact h2'.trans (by simpa [Finset.insert_erase hx] using h1)
      · have hYe : Y = ∅ := Finset.not_nonempty_iff_eq_empty.mp hY
        have hXe : X = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro x hx
          obtain ⟨y, hy, _⟩ := hb.surjOn hx
          simp [hYe] at hy
        simp [hYe, hXe]

lemma cancelable_comparison (v : Finset M → ℝ) (_hv : IsValuation v)
    (hc : IsCancelable v) (k : ℕ) (x y : Fin k → M)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (h : ∀ r, v {y r} ≤ v {x r}) :
    v (Finset.univ.image y) ≤ v (Finset.univ.image x) := by
  classical
  let φ : M → M := fun g => if hg : g ∈ Finset.univ.image y then
    x (Classical.choose (Finset.mem_image.mp hg)) else g
  have hφ : ∀ r, φ (y r) = x r := by
    intro r
    have hm : y r ∈ Finset.univ.image y := Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩
    simp only [φ, dif_pos hm]
    congr 1
    exact hy (Classical.choose_spec (Finset.mem_image.mp hm)).2
  apply dominated_bijOn_le v hc _ _ φ
  · refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hg
      simp only [hφ]
      exact Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩
    · intro g hg g' hg' he
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hg
      obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hg'
      rw [hφ, hφ] at he
      exact congrArg y (hx he)
    · intro g hg
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hg
      exact ⟨y r, Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩, hφ r⟩
  · intro g hg
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hg
    simpa only [hφ] using h r
end RRProof

namespace RoundRobinEq.CancelableBluff

theorem theorem_3_2 {n : ℕ} [NeZero n] {M : Type*} [Fintype M] [DecidableEq M]
    (k : ℕ) (hm : Fintype.card M = k * n) (v : Fin n → Finset M → ℝ)
    (hv : ∀ i, IsValuation (v i)) (hc : ∀ i, IsCancelable (v i))
    (σ : Fin n → List M) (hσ : IsStrictTruthful v σ) :
    IsApproxPNE 1 v (bluff σ) := by
  refine ⟨RRProof.bluff_ranking σ (fun a => (hσ a).1), ?_⟩
  intro i τ hτ
  obtain ⟨y, hy, he, hd⟩ := RRProof.deviation_singleton_enumeration v σ hσ k hm i τ hτ
  have hh := RRProof.cancelable_comparison (v i) (hv i) (hc i) k
    (RRProof.ownPick σ (fun a => (hσ a).1) k hm i) y
    (RRProof.ownPick_injective σ (fun a => (hσ a).1) k hm i) hy hd
  rw [he, RRProof.ownPick_image] at hh
  simpa [RRProof.roundRobin_bluff σ (fun a => (hσ a).1)] using hh

end RoundRobinEq.CancelableBluff

open RoundRobinEq.CancelableBluff

theorem solution {n : ℕ} [NeZero n] {M : Type*} [Fintype M] [DecidableEq M]
    (k : ℕ) (hm : Fintype.card M = k * n) (v : Fin n → Finset M → ℝ)
    (hv : ∀ i, IsValuation (v i)) (hc : ∀ i, IsCancelable (v i))
    (σ : Fin n → List M) (hσ : IsStrictTruthful v σ) :
    IsApproxPNE 1 v (bluff σ) :=
  RoundRobinEq.CancelableBluff.theorem_3_2 k hm v hv hc σ hσ
