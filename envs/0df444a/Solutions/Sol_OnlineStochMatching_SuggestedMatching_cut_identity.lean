-- Prove2me | solution 1 for OnlineStochMatching.SuggestedMatching.cut_identity
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T06:09:12.525677+00:00
-- url     : https://prove2.me/submissions/0d80eaf7-0fba-44a8-85b7-5a07d1ef96b5

import Mathlib
import Definitions.Def_OnlineStochMatching_SuggestedMatching_Cut
import Definitions.Def_OnlineStochMatching_SuggestedMatching_Algorithm

open Classical

namespace OnlineStochMatching.SuggestedMatching
variable {A I : Type} [Fintype A] [Fintype I]

noncomputable def degA (N : Finset (A × I)) (a : A) : ℕ := (N.filter fun p => p.1 = a).card
noncomputable def degT (N : Finset (A × I)) (i : I) : ℕ := (N.filter fun p => p.2 = i).card

lemma isBM_iff (inst : Instance A I) (N : Finset (A × I)) :
    IsBMatching inst N ↔ (N ⊆ inst.E ∧ (∀ a, degA N a ≤ 1) ∧ ∀ i, degT N i ≤ inst.e i) := by
  unfold IsBMatching degA degT
  constructor <;> intro h <;> convert h

lemma degA_insert (N : Finset (A × I)) (x : A × I) (hx : x ∉ N) (a : A) :
    degA (insert x N) a = degA N a + if x.1 = a then 1 else 0 := by
  unfold degA
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp [hx])]
  · simp

lemma degT_insert (N : Finset (A × I)) (x : A × I) (hx : x ∉ N) (i : I) :
    degT (insert x N) i = degT N i + if x.2 = i then 1 else 0 := by
  unfold degT
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp [hx])]
  · simp

lemma degA_erase (N : Finset (A × I)) (x : A × I) (hx : x ∈ N) (a : A) :
    degA (N.erase x) a + (if x.1 = a then 1 else 0) = degA N a := by
  unfold degA
  rw [Finset.filter_erase]
  split_ifs with h
  · rw [Finset.card_erase_of_mem (by simp [hx, h])]
    have : 0 < (N.filter fun p => p.1 = a).card := Finset.card_pos.mpr ⟨x, by simp [hx, h]⟩
    omega
  · simp [Finset.erase_eq_of_notMem (by simp [h] : x ∉ N.filter fun p => p.1 = a)]

lemma degT_erase (N : Finset (A × I)) (x : A × I) (hx : x ∈ N) (i : I) :
    degT (N.erase x) i + (if x.2 = i then 1 else 0) = degT N i := by
  unfold degT
  rw [Finset.filter_erase]
  split_ifs with h
  · rw [Finset.card_erase_of_mem (by simp [hx, h])]
    have : 0 < (N.filter fun p => p.2 = i).card := Finset.card_pos.mpr ⟨x, by simp [hx, h]⟩
    omega
  · simp [Finset.erase_eq_of_notMem (by simp [h] : x ∉ N.filter fun p => p.2 = i)]

def Dset (inst : Instance A I) (M : Finset (A × I)) : ℕ → Set (Option (A ⊕ I))
  | 0 => {none}
  | k+1 => Dset inst M k ∪ {y | ∃ x ∈ Dset inst M k, ResidualStep inst M x y}

lemma Dset_mono (inst : Instance A I) (M : Finset (A × I)) {k l : ℕ} (h : k ≤ l) :
    Dset inst M k ⊆ Dset inst M l := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans Set.subset_union_left

lemma reach_Dset (inst : Instance A I) (M : Finset (A × I)) (y : Option (A ⊕ I))
    (h : Relation.ReflTransGen (ResidualStep inst M) none y) : ∃ k, y ∈ Dset inst M k := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hr ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k+1, Or.inr ⟨_, hk, hr⟩⟩

def Good (inst : Instance A I) (M N : Finset (A × I)) : Prop :=
  N ⊆ inst.E ∧ (∀ a, degA N a ≤ 1) ∧ (∀ i, degT N i = degT M i) ∧ N.card = M.card

def Cond (inst : Instance A I) (M : Finset (A × I)) : Option (A ⊕ I) → Finset (A × I) → Prop
  | none, N => Good inst M N
  | some (.inl a), N => Good inst M N ∧ degA N a = 0
  | some (.inr t), N => N ⊆ inst.E ∧ (∀ a, degA N a ≤ 1) ∧ (∀ i, i ≠ t → degT N i = degT M i) ∧
      degT N t = degT M t + 1 ∧ N.card = M.card + 1

lemma main_inv (inst : Instance A I) (M : Finset (A × I)) (hM : IsBMatching inst M) (k : ℕ) :
    ∀ x ∈ Dset inst M k, ∃ N : Finset (A × I), Cond inst M x N ∧
      ∀ b : A, some (Sum.inl b) ∉ Dset inst M k →
        N.filter (fun p => p.1 = b) = M.filter (fun p => p.1 = b) := by
  obtain ⟨hME, hMA, hMT⟩ := (isBM_iff inst M).mp hM
  induction k with
  | zero =>
    intro x hx
    have : x = none := hx
    subst this
    refine ⟨M, ⟨hME, hMA, fun i => rfl, rfl⟩, fun b _ => rfl⟩
  | succ k ih =>
    intro x hx
    rcases hx with hx | ⟨y, hy, hR⟩
    · obtain ⟨N, hN, ht⟩ := ih x hx
      exact ⟨N, hN, fun b hb => ht b (fun h => hb (Dset_mono inst M (Nat.le_succ k) h))⟩
    · by_cases hxk : x ∈ Dset inst M k
      · obtain ⟨N, hN, ht⟩ := ih x hxk
        exact ⟨N, hN, fun b hb => ht b (fun h => hb (Dset_mono inst M (Nat.le_succ k) h))⟩
      obtain ⟨N, hN, ht⟩ := ih y hy
      rcases y with _ | (a | t) <;> rcases x with _ | (a' | t') <;> simp only [ResidualStep] at hR
      · -- none -> inl a'
        refine ⟨N, ⟨hN, ?_⟩, fun b hb => ht b (fun h => hb (Dset_mono inst M (Nat.le_succ k) h))⟩
        have h1 := ht a' hxk
        have : degA N a' = degA M a' := by unfold degA; rw [h1]
        rw [this]
        unfold degA; exact hR
      · -- inl a -> inr t'
        obtain ⟨hEa, hnM⟩ := hR
        obtain ⟨hN1, hN2⟩ := hN
        obtain ⟨hNE, hNA, hNT, hNc⟩ := hN1
        have hnot : (a, t') ∉ N := by
          intro hmem
          have : 0 < degA N a := Finset.card_pos.mpr ⟨(a, t'), by simp [hmem]⟩
          omega
        refine ⟨insert (a, t') N, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · exact Finset.insert_subset hEa hNE
        · intro b
          rw [degA_insert N _ hnot]
          by_cases hab : a = b
          · subst hab; simp [hN2]
          · simp [hab]; exact hNA b
        · intro i hi
          rw [degT_insert N _ hnot]
          have : ¬ (t' = i) := fun h => hi h.symm
          simp [this, hNT i]
        · rw [degT_insert N _ hnot]; simp [hNT t']
        · rw [Finset.card_insert_of_notMem hnot, hNc]
        · intro b hb
          have hba : b ≠ a := fun h => hb (Dset_mono inst M (Nat.le_succ k) (h ▸ hy))
          rw [Finset.filter_insert]
          simp only [hba.symm, if_false]
          exact ht b (fun h => hb (Dset_mono inst M (Nat.le_succ k) h))
      · -- inr t -> inl a'
        obtain ⟨hNE, hNA, hNT, hNt, hNc⟩ := hN
        have hmemM : (a', t) ∈ M := hR
        have h1 := ht a' hxk
        have hmemN : (a', t) ∈ N := by
          have : (a', t) ∈ M.filter (fun p => p.1 = a') := by simp [hmemM]
          rw [← h1] at this
          exact (Finset.mem_filter.mp this).1
        have hdA : degA N a' = degA M a' := by unfold degA; rw [h1]
        refine ⟨N.erase (a', t), ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
        · exact (Finset.erase_subset _ _).trans hNE
        · intro b
          have := degA_erase N (a', t) hmemN b
          have := hNA b
          omega
        · intro i
          have := degT_erase N (a', t) hmemN i
          by_cases hi : t = i
          · subst hi; simp at this; omega
          · simp [hi] at this
            have hi' : i ≠ t := fun h => hi h.symm
            rw [this]; exact hNT i hi'
        · rw [Finset.card_erase_of_mem hmemN]; omega
        · have := degA_erase N (a', t) hmemN a'
          simp at this
          have h2 := hMA a'
          have h3 : 0 < degA M a' := Finset.card_pos.mpr ⟨(a', t), by simp [hmemM]⟩
          omega
        · intro b hb
          have hba : b ≠ a' := fun h => hb (Or.inr ⟨_, hy, by rw [h]; exact hR⟩)
          rw [Finset.filter_erase]
          have h2 := ht b (fun h => hb (Dset_mono inst M (Nat.le_succ k) h))
          rw [h2]
          have : (a', t) ∉ M.filter (fun p => p.1 = b) := by simp [hba.symm]
          exact Finset.erase_eq_of_notMem this

lemma sat_type (inst : Instance A I) (M : Finset (A × I)) (hM : IsMaxBMatching inst M) (t : I)
    (h : typeInSourceSide inst M t) : degT M t = inst.e t := by
  obtain ⟨k, hk⟩ := reach_Dset inst M _ h
  obtain ⟨N, hN, _⟩ := main_inv inst M hM.1 k _ hk
  obtain ⟨hNE, hNA, hNT, hNt, hNc⟩ := hN
  obtain ⟨hME, hMA, hMT⟩ := (isBM_iff inst M).mp hM.1
  by_contra hne
  have hlt : degT M t < inst.e t := lt_of_le_of_ne (hMT t) hne
  have hNB : IsBMatching inst N := by
    rw [isBM_iff]
    refine ⟨hNE, hNA, fun i => ?_⟩
    by_cases hi : i = t
    · subst hi; omega
    · rw [hNT i hi]; exact hMT i
  have := hM.2 N hNB
  omega

lemma ad_fact1 (inst : Instance A I) (M : Finset (A × I)) (a : A) (h : degA M a = 0) :
    adInSourceSide inst M a := by
  apply Relation.ReflTransGen.single
  show (M.filter fun (p : A × I) => p.1 = a).card = 0
  exact h

lemma ad_fact2 (inst : Instance A I) (M : Finset (A × I)) (a : A) (i : I) (h : (a, i) ∈ M)
    (hi : typeInSourceSide inst M i) : adInSourceSide inst M a :=
  Relation.ReflTransGen.tail hi (show (a, i) ∈ M from h)

lemma ad_fact3 (inst : Instance A I) (M : Finset (A × I)) (hM : IsBMatching inst M)
    (a : A) (i : I) (h : (a, i) ∈ M) (ha : adInSourceSide inst M a) :
    typeInSourceSide inst M i := by
  obtain ⟨hME, hMA, hMT⟩ := (isBM_iff inst M).mp hM
  rcases Relation.ReflTransGen.cases_tail ha with h0 | ⟨c, hc, hr⟩
  · exact absurd h0 (by simp)
  · rcases c with _ | (a1 | i1)
    · exfalso
      have h1 : (M.filter fun (p : A × I) => p.1 = a).card = 0 := hr
      have : 0 < degA M a := Finset.card_pos.mpr ⟨(a, i), by simp [h]⟩
      unfold degA at this
      omega
    · exact absurd hr (by simp [ResidualStep])
    · have h1 : (a, i1) ∈ M := hr
      have : (a, i) = (a, i1) := by
        have := Finset.card_le_one.mp (hMA a) (a, i) (by simp [h]) (a, i1) (by simp [h1])
        exact this
      have e : i = i1 := (Prod.mk.inj this).2
      subst e
      exact hc

lemma ad_to_type (inst : Instance A I) (M : Finset (A × I)) (hM : IsBMatching inst M)
    (a : A) (i : I) (hE : (a, i) ∈ inst.E) (ha : adInSourceSide inst M a) :
    typeInSourceSide inst M i := by
  by_cases hmem : (a, i) ∈ M
  · exact ad_fact3 inst M hM a i hmem ha
  · exact Relation.ReflTransGen.tail ha (show (a, i) ∈ inst.E ∧ (a, i) ∉ M from ⟨hE, hmem⟩)

lemma coveredAds_eq_image (M : Finset (A × I)) : coveredAds M = M.image Prod.fst := by
  ext a
  simp [coveredAds]

theorem cut_identity_core (A I : Type) [Fintype A] [Fintype I]
    (inst : Instance A I) (M : Finset (A × I)) (hM : IsMaxBMatching inst M) :
    (∀ a i, (a, i) ∈ inst.E → adInSourceSide inst M a → typeInSourceSide inst M i) ∧
      (coveredAds M).card =
        (adsInSinkSide inst M).card +
          ∑ i ∈ typesInSourceSide inst M, inst.e i := by
  refine ⟨fun a i hE ha => ad_to_type inst M hM.1 a i hE ha, ?_⟩
  obtain ⟨hME, hMA, hMT⟩ := (isBM_iff inst M).mp hM.1
  have hinj : Set.InjOn Prod.fst (M : Set (A × I)) := by
    intro p hp q hq hpq
    exact Finset.card_le_one.mp (hMA p.1) p (by simp [Finset.mem_coe.mp hp])
      q (by simp [Finset.mem_coe.mp hq]; exact hpq.symm)
  have h1 : (coveredAds M).card = M.card := by
    rw [coveredAds_eq_image, Finset.card_image_of_injOn hinj]
  have h2 := Finset.card_filter_add_card_filter_not (s := M) (fun p : A × I => typeInSourceSide inst M p.2)
  -- reachable-type edges
  have h3 : (M.filter fun p : A × I => typeInSourceSide inst M p.2).card =
      ∑ i ∈ typesInSourceSide inst M, inst.e i := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := typesInSourceSide inst M)]
    · apply Finset.sum_congr rfl
      intro i hi
      have hi' : typeInSourceSide inst M i := by simpa [typesInSourceSide] using hi
      rw [← sat_type inst M hM i hi']
      unfold degT
      congr 1
      ext p
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨h, _⟩, h'⟩; exact ⟨h, h'⟩
      · rintro ⟨h, h'⟩; exact ⟨⟨h, by rw [h']; exact hi'⟩, h'⟩
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp
      simp [typesInSourceSide, hp.2]
  have h4 : (M.filter fun p : A × I => ¬ typeInSourceSide inst M p.2).card =
      (adsInSinkSide inst M).card := by
    have himg : (M.filter fun p : A × I => ¬ typeInSourceSide inst M p.2).image Prod.fst
        = adsInSinkSide inst M := by
      ext a
      simp only [Finset.mem_image, Finset.mem_filter, adsInSinkSide, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨p, ⟨hp, hpt⟩, rfl⟩ hra
        exact hpt (ad_fact3 inst M hM.1 p.1 p.2 hp hra)
      · intro hra
        have hdeg : degA M a ≠ 0 := fun h => hra (ad_fact1 inst M a h)
        obtain ⟨p, hp⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hdeg)
        rw [Finset.mem_filter] at hp
        refine ⟨p, ⟨hp.1, fun hpt => hra ?_⟩, hp.2⟩
        rw [← hp.2]
        exact ad_fact2 inst M p.1 p.2 hp.1 hpt
    rw [← himg, Finset.card_image_of_injOn]
    intro p hp q hq hpq
    exact hinj (Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).1)
      (Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).1) hpq
  omega

end OnlineStochMatching.SuggestedMatching

open OnlineStochMatching.SuggestedMatching


theorem solution (A I : Type) [Fintype A] [Fintype I]
    (inst : Instance A I) (M : Finset (A × I)) (hM : IsMaxBMatching inst M) :
    (∀ a i, (a, i) ∈ inst.E → adInSourceSide inst M a → typeInSourceSide inst M i) ∧
      (coveredAds M).card =
        (adsInSinkSide inst M).card +
          ∑ i ∈ typesInSourceSide inst M, inst.e i := by
  exact cut_identity_core A I inst M hM
