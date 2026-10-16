-- Prove2me | solution 2 for StrategicAlloc.RRExists.theorem_A_3
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-15T18:09:45.854997+00:00
-- url     : https://prove2.me/submissions/07b26bc4-7440-4a8e-886e-efb0c1d0dc55

import Definitions.Def_StrategicAlloc_RRExists_Setting

namespace StrategicAlloc.RRExists

open StrategicAlloc.RRFair
open Finset hiding val

variable {n m : ℕ}

lemma rrx_rank_perm (c : Fin m → ℝ) : (rank c).Perm (List.finRange m) := List.mergeSort_perm _ _

lemma rrx_mem_rank (c : Fin m → ℝ) (x : Fin m) : x ∈ rank c :=
  (rrx_rank_perm c).mem_iff.2 (List.mem_finRange x)

lemma rrx_rank_pairwise (c : Fin m → ℝ) : (rank c).Pairwise (fun g h => c h ≤ c g) := by
  have := List.pairwise_mergeSort (le := fun g h => decide (c h ≤ c g)) ?_ ?_ (List.finRange m)
  · unfold rank
    exact this.imp (by intro a b h; simpa using h)
  · intro a b d h1 h2
    simp only [decide_eq_true_eq] at *
    linarith
  · intro a b
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact le_total _ _

lemma rrx_find {α : Type*} (r : α → α → Prop) (p : α → Bool) :
    ∀ l : List α, l.Pairwise r → (∃ x ∈ l, p x = true) →
      ∃ g, l.find? p = some g ∧ g ∈ l ∧ p g = true ∧ ∀ x ∈ l, p x = true → x = g ∨ r g x
  | [], _, ⟨x, hx, _⟩ => by simp at hx
  | a :: l, hpw, ⟨x, hx, hpx⟩ => by
    rw [List.pairwise_cons] at hpw
    by_cases ha : p a = true
    · refine ⟨a, by simp [List.find?_cons, ha], by simp, ha, ?_⟩
      intro y hy _
      rcases List.mem_cons.1 hy with rfl | hy
      · exact Or.inl rfl
      · exact Or.inr (hpw.1 y hy)
    · have hx' : x ∈ l := by
        rcases List.mem_cons.1 hx with rfl | hx
        · exact absurd hpx ha
        · exact hx
      obtain ⟨g, hg, hgl, hpg, hall⟩ := rrx_find r p l hpw.2 ⟨x, hx', hpx⟩
      refine ⟨g, by simp [List.find?_cons, ha, hg], List.mem_cons_of_mem _ hgl, hpg, ?_⟩
      intro y hy hpy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact absurd hpy ha
      · exact hall y hy hpy

lemma rrx_top_spec (c : Fin m → ℝ) (T : Finset (Fin m)) (hT : T.Nonempty) :
    ∃ g, top (rank c) T = some g ∧ g ∈ T ∧ ∀ x ∈ T, c x ≤ c g := by
  obtain ⟨x, hx⟩ := hT
  obtain ⟨g, hg, -, hpg, hall⟩ := rrx_find (fun g h => c h ≤ c g) (fun y => decide (y ∈ T))
    (rank c) (rrx_rank_pairwise c) ⟨x, rrx_mem_rank c x, by simpa using hx⟩
  refine ⟨g, hg, by simpa using hpg, ?_⟩
  intro y hy
  rcases hall y (rrx_mem_rank c y) (by simpa using hy) with rfl | h
  · exact le_rfl
  · exact h

variable [NeZero n]

/-- allocated set -/
noncomputable abbrev AB (b : Fin n → Fin m → ℝ) (t : ℕ) : Finset (Fin m) :=
  allocBefore (0 : Fin n) Finset.univ b t

noncomputable abbrev PK (b : Fin n → Fin m → ℝ) (t : ℕ) : Option (Fin m) :=
  pick (0 : Fin n) Finset.univ b t

lemma rrx_ab_succ (b : Fin n → Fin m → ℝ) (t : ℕ) :
    AB b (t + 1) = match PK b t with
      | some g => insert g (AB b t)
      | none => AB b t := rfl

lemma rrx_pk_spec (b : Fin n → Fin m → ℝ) (t : ℕ) (h : AB b t ≠ Finset.univ) :
    ∃ g, PK b t = some g ∧ g ∉ AB b t ∧ AB b (t + 1) = insert g (AB b t) ∧
      ∀ x ∉ AB b t, b (agentAt 0 t) x ≤ b (agentAt 0 t) g := by
  have hne : (Finset.univ \ AB b t).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hs
    exact h (Finset.eq_univ_of_forall fun x => hs (Finset.mem_univ x))
  obtain ⟨g, hg, hgT, hmax⟩ := rrx_top_spec (b (agentAt 0 t)) _ hne
  have hpk : PK b t = some g := hg
  refine ⟨g, hpk, by simpa using hgT, ?_, ?_⟩
  · rw [rrx_ab_succ, hpk]
  · intro x hx
    exact hmax x (by simpa using hx)

lemma rrx_ab_mono_succ (b : Fin n → Fin m → ℝ) (t : ℕ) : AB b t ⊆ AB b (t + 1) := by
  rw [rrx_ab_succ]
  rcases PK b t with _ | g
  · exact subset_rfl
  · exact Finset.subset_insert _ _

lemma rrx_ab_mono (b : Fin n → Fin m → ℝ) {s t : ℕ} (h : s ≤ t) : AB b s ⊆ AB b t :=
  (monotone_nat_of_le_succ (f := fun t => AB b t) (rrx_ab_mono_succ b)) h

lemma rrx_ab_card (b : Fin n → Fin m → ℝ) : ∀ t, t ≤ m → (AB b t).card = t
  | 0, _ => rfl
  | t + 1, ht => by
    have ih := rrx_ab_card b t (by omega)
    have hne : AB b t ≠ Finset.univ := by
      intro h
      rw [h, Finset.card_univ, Fintype.card_fin] at ih
      omega
    obtain ⟨g, -, hg, hs, -⟩ := rrx_pk_spec b t hne
    rw [hs, Finset.card_insert_of_notMem hg, ih]

lemma rrx_ab_ne_univ (b : Fin n → Fin m → ℝ) {t : ℕ} (ht : t < m) : AB b t ≠ Finset.univ := by
  intro h
  have := rrx_ab_card b t ht.le
  rw [h, Finset.card_univ, Fintype.card_fin] at this
  omega

lemma rrx_ab_univ (b : Fin n → Fin m → ℝ) {t : ℕ} (ht : m ≤ t) : AB b t = Finset.univ := by
  apply Finset.eq_univ_of_card
  have h1 := rrx_ab_card b m le_rfl
  have h2 := Finset.card_le_card (rrx_ab_mono b ht)
  have h3 := Finset.card_le_univ (AB b t)
  simp only [Fintype.card_fin] at *
  omega

lemma rrx_rr_eq (b : Fin n → Fin m → ℝ) (i : Fin n) :
    roundRobin b i = ((Finset.range m).filter (fun t => agentAt (0 : Fin n) t = i)).biUnion
      (fun t => (PK b t).toFinset) := by
  simp [roundRobin, rrFrom, Finset.card_univ, Fintype.card_fin]

/-- common bluff bid: number of truthful steps after which `g` is already allocated -/
noncomputable def cB (v : Fin n → Fin m → ℝ) (g : Fin m) : ℝ :=
  (((Finset.range m).filter (fun t => g ∈ AB v t)).card : ℝ)

lemma rrx_c_lt (v : Fin n → Fin m → ℝ) {t : ℕ} {x y : Fin m} (hx : x ∈ AB v t)
    (hy : y ∉ AB v t) : cB v y < cB v x := by
  unfold cB
  have htm : t < m := by
    by_contra h
    exact hy (by rw [rrx_ab_univ v (not_lt.1 h)]; exact Finset.mem_univ _)
  apply Nat.cast_lt.2
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨t, by simp [htm, hx], by simp [hy]⟩
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_range] at hs ⊢
    refine ⟨hs.1, ?_⟩
    rcases le_total t s with h | h
    · exact rrx_ab_mono v h hx
    · exact absurd (rrx_ab_mono v h hs.2) hy

lemma rrx_bluff_ab (v : Fin n → Fin m → ℝ) :
    ∀ t, t ≤ m → AB (fun _ : Fin n => cB v) t = AB v t
  | 0, _ => rfl
  | t + 1, ht => by
    have ih := rrx_bluff_ab v t (by omega)
    obtain ⟨g0, -, hg0, hs0, -⟩ := rrx_pk_spec v t (rrx_ab_ne_univ v (by omega))
    obtain ⟨g, -, hg, hs, hmax⟩ := rrx_pk_spec (fun _ : Fin n => cB v) t
      (by rw [ih]; exact rrx_ab_ne_univ v (by omega))
    rw [ih] at hg hmax hs
    have : g = g0 := by
      by_contra hne
      have h1 := hmax g0 hg0
      have h2 : cB v g < cB v g0 :=
        rrx_c_lt v (t := t + 1) (by rw [hs0]; exact Finset.mem_insert_self _ _)
          (by rw [hs0]; simp [hne, hg])
      linarith
    rw [hs, hs0, this]

lemma rrx_bluff_pk (v : Fin n → Fin m → ℝ) {t : ℕ} (ht : t < m) :
    PK (fun _ : Fin n => cB v) t = PK v t := by
  have ih := rrx_bluff_ab v t ht.le
  obtain ⟨g0, hp0, hg0, hs0, -⟩ := rrx_pk_spec v t (rrx_ab_ne_univ v ht)
  obtain ⟨g, hp, hg, hs, hmax⟩ := rrx_pk_spec (fun _ : Fin n => cB v) t
    (by rw [ih]; exact rrx_ab_ne_univ v ht)
  rw [ih] at hg hmax hs
  have : g = g0 := by
    by_contra hne
    have h1 := hmax g0 hg0
    have h2 : cB v g < cB v g0 :=
      rrx_c_lt v (t := t + 1) (by rw [hs0]; exact Finset.mem_insert_self _ _)
        (by rw [hs0]; simp [hne, hg])
    linarith
  rw [hp, hp0, this]

lemma rrx_count (v : Fin n → Fin m → ℝ) (i : Fin n) (b1 : Fin n → Fin m → ℝ)
    (hb1 : ∀ t, agentAt (0 : Fin n) t ≠ i → b1 (agentAt 0 t) = cB v) {p : ℕ} (hp : p ≤ m) :
    ((roundRobin b1 i) ∩ AB v p).card ≤
      ((Finset.range p).filter (fun t => agentAt (0 : Fin n) t = i)).card := by
  classical
  set Q := AB v p with hQ
  have hQc : Q.card = p := rrx_ab_card v p hp
  -- E s
  have hE : ∀ s, s ≤ m → ((Finset.range s).filter (fun t => ∃ g ∈ Q, PK b1 t = some g)).card
      = (AB b1 s ∩ Q).card := by
    intro s
    induction s with
    | zero => intro _; show 0 = ((∅ : Finset (Fin m)) ∩ Q).card; simp
    | succ s ih =>
      intro hs
      obtain ⟨g, hp1, hg, hs1, -⟩ := rrx_pk_spec b1 s (rrx_ab_ne_univ b1 (by omega))
      rw [Finset.range_add_one, Finset.filter_insert, hs1]
      by_cases hgQ : g ∈ Q
      · rw [if_pos ⟨g, hgQ, hp1⟩, Finset.insert_inter_of_mem hgQ,
          Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem
            (by simp [hg]), ih (by omega)]
      · have : ¬ ∃ g' ∈ Q, PK b1 s = some g' := by
          rintro ⟨g', hg', h'⟩
          rw [hp1] at h'
          cases h'
          exact hgQ hg'
        rw [if_neg this, Finset.insert_inter_of_notMem hgQ, ih (by omega)]
  have hbi : ∀ s, s ≤ m →
      ((Finset.range s).filter (fun t => agentAt (0 : Fin n) t = i ∧
        ∃ g ∈ Q, PK b1 t = some g)).card ≤
      ((Finset.range p).filter (fun t => agentAt (0 : Fin n) t = i)).card := by
    intro s
    induction s with
    | zero => intro _; simp
    | succ s ih =>
      intro hs
      by_cases hc : agentAt (0 : Fin n) s = i ∧ ∃ g ∈ Q, PK b1 s = some g
      · by_cases hsp : s + 1 ≤ p
        · calc _ ≤ ((Finset.range (s + 1)).filter (fun t => agentAt (0 : Fin n) t = i)).card :=
                Finset.card_le_card (fun t ht => by simp only [Finset.mem_filter] at ht ⊢; exact ⟨ht.1, ht.2.1⟩)
            _ ≤ _ := Finset.card_le_card (Finset.filter_subset_filter _
                (Finset.range_subset_range.2 hsp))
        · obtain ⟨hai, g, hgQ, hpg⟩ := hc
          obtain ⟨g', hpg', hg', -, -⟩ := rrx_pk_spec b1 s (rrx_ab_ne_univ b1 (by omega))
          rw [hpg] at hpg'
          cases hpg'
          have hoth : ∀ t ∈ Finset.range s, agentAt (0 : Fin n) t ≠ i →
              ∃ g ∈ Q, PK b1 t = some g := by
            intro t ht hti
            rw [Finset.mem_range] at ht
            obtain ⟨g2, hp2, -, -, hmax⟩ := rrx_pk_spec b1 t (rrx_ab_ne_univ b1 (by omega))
            refine ⟨g2, ?_, hp2⟩
            by_contra hg2
            have h1 := hmax g (fun h => hg' (rrx_ab_mono b1 ht.le h))
            rw [hb1 t hti] at h1
            have h2 := rrx_c_lt v hgQ hg2
            linarith
          have hsub : (Finset.range s).filter (fun t => agentAt (0 : Fin n) t ≠ i) ∪
              (Finset.range s).filter (fun t => agentAt (0 : Fin n) t = i ∧
                ∃ g ∈ Q, PK b1 t = some g) ⊆
              (Finset.range s).filter (fun t => ∃ g ∈ Q, PK b1 t = some g) := by
            intro t ht
            simp only [Finset.mem_union, Finset.mem_filter] at ht ⊢
            rcases ht with ⟨h1, h2⟩ | ⟨h1, -, h2⟩
            · exact ⟨h1, hoth t h1 h2⟩
            · exact ⟨h1, h2⟩
          have hdisj : Disjoint ((Finset.range s).filter (fun t => agentAt (0 : Fin n) t ≠ i))
              ((Finset.range s).filter (fun t => agentAt (0 : Fin n) t = i ∧
                ∃ g ∈ Q, PK b1 t = some g)) := by
            rw [Finset.disjoint_filter]
            intro t _ h1 h2
            exact h1 h2.1
          have hc1 := Finset.card_le_card hsub
          rw [Finset.card_union_of_disjoint hdisj, hE s (by omega)] at hc1
          have hlt : (AB b1 s ∩ Q).card < Q.card := by
            apply Finset.card_lt_card
            rw [Finset.ssubset_iff_of_subset Finset.inter_subset_right]
            exact ⟨g, hgQ, by simp [hg']⟩
          have hsplit := Finset.card_filter_add_card_filter_not
            (s := Finset.range s) (fun t => agentAt (0 : Fin n) t = i)
          rw [Finset.card_range] at hsplit
          have hks : ((Finset.range s).filter (fun t => agentAt (0 : Fin n) t = i)).card ≤
              ((Finset.range p).filter (fun t => agentAt (0 : Fin n) t = i)).card + (s - p) := by
            calc _ ≤ ((Finset.range p).filter (fun t => agentAt (0 : Fin n) t = i) ∪
                  Finset.Ico p s).card := by
                  apply Finset.card_le_card
                  intro t ht
                  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union,
                    Finset.mem_Ico] at ht ⊢
                  by_cases htp : t < p
                  · exact Or.inl ⟨htp, ht.2⟩
                  · exact Or.inr ⟨by omega, ht.1⟩
              _ ≤ _ := by
                  refine (Finset.card_union_le _ _).trans ?_
                  rw [Nat.card_Ico]
          rw [Finset.range_add_one, Finset.filter_insert, if_pos ⟨hai, g, hgQ, hpg⟩,
            Finset.card_insert_of_notMem (by simp)]
          rw [hQc] at hlt
          have hne : ((Finset.range s).filter (fun t => agentAt (0 : Fin n) t ≠ i)).card =
              ((Finset.range s).filter (fun t => ¬ agentAt (0 : Fin n) t = i)).card := rfl
          omega
      · rw [Finset.range_add_one, Finset.filter_insert, if_neg hc]
        exact ih (by omega)
  calc ((roundRobin b1 i) ∩ Q).card
      ≤ (((Finset.range m).filter (fun t => agentAt (0 : Fin n) t = i ∧
          ∃ g ∈ Q, PK b1 t = some g)).biUnion (fun t => (PK b1 t).toFinset)).card := by
        apply Finset.card_le_card
        intro x hx
        rw [Finset.mem_inter, rrx_rr_eq, Finset.mem_biUnion] at hx
        obtain ⟨⟨t, ht, hxt⟩, hxQ⟩ := hx
        rw [Finset.mem_filter] at ht
        have hxt' : PK b1 t = some x := by simpa using hxt
        exact Finset.mem_biUnion.2 ⟨t, Finset.mem_filter.2 ⟨ht.1, ht.2, x, hxQ, hxt'⟩, hxt⟩
    _ ≤ ((Finset.range m).filter (fun t => agentAt (0 : Fin n) t = i ∧
          ∃ g ∈ Q, PK b1 t = some g)).card * 1 := by
        apply Finset.card_biUnion_le_card_mul
        intro t _
        rw [Option.card_toFinset]
        cases PK b1 t <;> simp
    _ ≤ _ := by rw [mul_one]; exact hbi m le_rfl

lemma rrx_main (v : Fin n → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g) (hm : 0 < m) (i : Fin n)
    (b1 : Fin n → Fin m → ℝ)
    (hb1 : ∀ t, agentAt (0 : Fin n) t ≠ i → b1 (agentAt 0 t) = cB v) :
    val v i (roundRobin b1 i) ≤ val v i (roundRobin (fun _ : Fin n => cB v) i) := by
  classical
  set g0 : Fin m := ⟨0, hm⟩
  set h : ℕ → Fin m := fun t => (PK v t).getD g0 with hh
  have hspec : ∀ t, t < m → PK v t = some (h t) ∧ h t ∉ AB v t ∧
      AB v (t + 1) = insert (h t) (AB v t) ∧
      ∀ y ∉ AB v t, v (agentAt 0 t) y ≤ v (agentAt 0 t) (h t) := by
    intro t ht
    obtain ⟨g, hp, hg, hs, hmax⟩ := rrx_pk_spec v t (rrx_ab_ne_univ v ht)
    have : h t = g := by simp [hh, hp]
    rw [this]
    exact ⟨hp, hg, hs, hmax⟩
  set Tu := (Finset.range m).filter (fun t => agentAt (0 : Fin n) t = i) with hTu
  have hA : roundRobin (fun _ : Fin n => cB v) i = Tu.image h := by
    rw [rrx_rr_eq, ← Finset.biUnion_singleton]
    apply Finset.biUnion_congr rfl
    intro t ht
    have htm : t < m := Finset.mem_range.1 (Finset.mem_filter.1 ht).1
    rw [rrx_bluff_pk v htm, (hspec t htm).1]
    rfl
  have hinj : Set.InjOn h Tu := by
    have key : ∀ t ∈ Tu, ∀ t' ∈ Tu, t < t' → h t ≠ h t' := by
      intro t ht t' ht' hlt heq
      have ht'm : t' < m := Finset.mem_range.1 (Finset.mem_filter.1 ht').1
      have h1 : h t ∈ AB v (t + 1) := by
        rw [(hspec t (by omega)).2.2.1]; exact Finset.mem_insert_self _ _
      exact (hspec t' ht'm).2.1 (heq ▸ rrx_ab_mono v hlt h1)
    intro t ht t' ht' heq
    rcases lt_trichotomy t t' with hlt | rfl | hlt
    · exact absurd heq (key t ht t' ht' hlt)
    · rfl
    · exact absurd heq.symm (key t' ht' t ht hlt)
  set B := roundRobin b1 i with hB
  let N : B → Finset ℕ := fun x => Tu.filter (fun t => x.1 ∉ AB v t)
  have hall : ∀ X : Finset B, X.card ≤ (X.biUnion N).card := by
    intro X
    rcases X.eq_empty_or_nonempty with rfl | hXne
    · simp
    set Y := X.map (Function.Embedding.subtype _) with hY
    have hex : ∃ p, Y ⊆ AB v p := ⟨m, by rw [rrx_ab_univ v le_rfl]; exact Finset.subset_univ _⟩
    have hpY : Y ⊆ AB v (Nat.find hex) := Nat.find_spec hex
    have hpm : Nat.find hex ≤ m :=
      Nat.find_min' hex (by rw [rrx_ab_univ v le_rfl]; exact Finset.subset_univ _)
    have hp0 : Nat.find hex ≠ 0 := by
      intro h0
      rw [h0] at hpY
      obtain ⟨x, hx⟩ := hXne
      have : (x : Fin m) ∈ Y := Finset.mem_map_of_mem _ hx
      exact absurd (hpY this) (by simp [AB, allocBefore])
    have hnot : ¬ Y ⊆ AB v (Nat.find hex - 1) := Nat.find_min hex (by omega)
    obtain ⟨y, hyY, hy⟩ := Finset.not_subset.1 hnot
    have hc := rrx_count v i b1 hb1 hpm
    calc X.card = Y.card := (Finset.card_map _).symm
      _ ≤ (B ∩ AB v (Nat.find hex)).card := by
          apply Finset.card_le_card
          intro z hz
          refine Finset.mem_inter.2 ⟨?_, hpY hz⟩
          obtain ⟨w, -, rfl⟩ := Finset.mem_map.1 hz
          exact w.2
      _ ≤ _ := hc
      _ ≤ _ := by
          apply Finset.card_le_card
          intro t ht
          rw [Finset.mem_filter, Finset.mem_range] at ht
          obtain ⟨x, hxX, hxy⟩ := Finset.mem_map.1 hyY
          refine Finset.mem_biUnion.2 ⟨x, hxX, ?_⟩
          simp only [N, Finset.mem_filter, Tu, Finset.mem_range]
          refine ⟨⟨by omega, ht.2⟩, ?_⟩
          intro hxt
          apply hy
          rw [← hxy]
          exact rrx_ab_mono v (by omega) hxt
  obtain ⟨f, hfinj, hfN⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective N).1 hall
  have hfTu : ∀ x : B, f x ∈ Tu ∧ x.1 ∉ AB v (f x) := fun x => by
    have := hfN x
    simp only [N, Finset.mem_filter] at this
    exact this
  calc val v i B = ∑ x : B, v i x := (Finset.sum_coe_sort B (fun x => v i x)).symm
    _ ≤ ∑ x : B, v i (h (f x)) := by
        apply Finset.sum_le_sum
        intro x _
        obtain ⟨h1, h2⟩ := hfTu x
        rw [Finset.mem_filter, Finset.mem_range] at h1
        have := (hspec (f x) h1.1).2.2.2 x h2
        rwa [h1.2] at this
    _ = ∑ t ∈ Finset.univ.image f, v i (h t) := by
        rw [Finset.sum_image (fun x _ y _ hxy => hfinj hxy)]
    _ ≤ ∑ t ∈ Tu, v i (h t) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro t ht
          obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 ht
          exact (hfTu x).1
        · intro t _ _; exact hv _ _
    _ = val v i (roundRobin (fun _ : Fin n => cB v) i) := by
        rw [hA, val, Finset.sum_image hinj]

theorem theorem_A_3 {n m : ℕ} [NeZero n] (v : Fin n → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g) :
    ∃ b : Fin n → Fin m → ℝ, StrategicAlloc.RRFair.IsPNE StrategicAlloc.RRFair.roundRobin v b := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨fun _ _ => 0, fun _ _ => le_rfl, fun i b' _ => ?_⟩
    simp [val, Finset.eq_empty_of_isEmpty]
  · refine ⟨fun _ => cB v, fun _ g => Nat.cast_nonneg _, fun i b' _ => ?_⟩
    apply rrx_main v hv hm i
    intro t ht
    exact Function.update_of_ne ht _ _

end StrategicAlloc.RRExists


-- Platform entry point: restates the target verbatim.
namespace StrategicAlloc.RRExists

/-- Theorem A.3 (p. 24): for every instance with additive non-negative valuations, Round-Robin
(Mechanism 1, lexicographic tie-breaking) has at least one pure Nash equilibrium. -/
theorem _root_.solution {n m : ℕ} [NeZero n] (v : Fin n → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g) :
    ∃ b : Fin n → Fin m → ℝ, StrategicAlloc.RRFair.IsPNE StrategicAlloc.RRFair.roundRobin v b := by
  apply @StrategicAlloc.RRExists.theorem_A_3 <;> assumption

end StrategicAlloc.RRExists
