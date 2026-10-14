-- Prove2me | solution 1 for WeberGittins.Submodular.eq10_partial_sums_submodular
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T01:05:05.961025+00:00
-- url     : https://prove2.me/submissions/19b33a53-aa41-4750-8375-7f97eb917d54

import Definitions.Def_WeberGittins_Submodular_PartialInterleavedSum



namespace WeberGittins.Submodular

/-- partial sums of a sequence -/
noncomputable def psum (H : ℕ → ℝ) (k : ℕ) : ℝ := ∑ u ∈ Finset.range k, H u

lemma psum_shift_le (H : ℕ → ℝ) (hanti : Antitone H) {a d : ℕ} (had : a ≤ d) (k : ℕ) :
    psum H (d + k) - psum H d ≤ psum H (a + k) - psum H a := by
  induction k with
  | zero => simp [psum]
  | succ k ih =>
    have h1 : psum H (d + (k+1)) = psum H (d + k) + H (d + k) := by
      simp [psum, ← add_assoc, Finset.sum_range_succ]
    have h2 : psum H (a + (k+1)) = psum H (a + k) + H (a + k) := by
      simp [psum, ← add_assoc, Finset.sum_range_succ]
    have := hanti (show a + k ≤ d + k by omega)
    rw [h1, h2]; linarith

lemma psum_pair (H : ℕ → ℝ) (hanti : Antitone H) {a b c d : ℕ} (hac : a ≤ c) (hcb : c ≤ b)
    (hsum : c + d = a + b) : psum H a + psum H b ≤ psum H c + psum H d := by
  have hda : a ≤ d := by omega
  have key := psum_shift_le H hanti hda (c - a)
  have e1 : d + (c - a) = b := by omega
  have e2 : a + (c - a) = c := by omega
  rw [e1, e2] at key
  linarith

lemma psum_pair' (H : ℕ → ℝ) (hanti : Antitone H) {a b c d : ℕ} (hlo : min a b ≤ c)
    (hhi : c ≤ max a b) (hsum : c + d = a + b) : psum H a + psum H b ≤ psum H c + psum H d := by
  rcases le_total a b with h | h
  · rw [min_eq_left h] at hlo; rw [max_eq_right h] at hhi
    exact psum_pair H hanti hlo hhi hsum
  · rw [min_eq_right h] at hlo; rw [max_eq_left h] at hhi
    have := psum_pair H hanti (a := b) (b := a) (c := c) (d := d) hlo hhi (by omega)
    linarith

lemma psum_mono (H : ℕ → ℝ) (hnn : ∀ k, 0 ≤ H k) {a b : ℕ} (h : a ≤ b) : psum H a ≤ psum H b := by
  unfold psum
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) (fun i _ _ => hnn i)

lemma exists_split {ι : Type*} [DecidableEq ι] (s : Finset ι) (lo up : ι → ℕ) (hl : ∀ j, lo j ≤ up j) :
    ∀ T : ℕ, ∑ j ∈ s, lo j ≤ T → T ≤ ∑ j ∈ s, up j →
      ∃ c : ι → ℕ, (∀ j ∈ s, lo j ≤ c j ∧ c j ≤ up j) ∧ ∑ j ∈ s, c j = T := by
  induction s using Finset.induction_on with
  | empty => intro T h1 h2; exact ⟨fun _ => 0, by simp, by simp at h1 h2 ⊢; omega⟩
  | insert i s hnot ih =>
    intro T h1 h2
    rw [Finset.sum_insert hnot] at h1 h2
    set Sl := ∑ j ∈ s, lo j
    set Sh := ∑ j ∈ s, up j
    have hli := hl i
    have hSS : Sl ≤ Sh := Finset.sum_le_sum (fun j _ => hl j)
    obtain ⟨c, hc, hcs⟩ := ih (T - min (up i) (T - Sl)) (by omega) (by omega)
    refine ⟨fun j => if j = i then min (up i) (T - Sl) else c j, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.1 hj with rfl | hj'
      · simp; omega
      · have : j ≠ i := fun h => hnot (h ▸ hj')
        simpa [this] using hc j hj'
    · rw [Finset.sum_insert hnot]
      have : ∑ j ∈ s, (if j = i then min (up i) (T - Sl) else c j) = ∑ j ∈ s, c j := by
        apply Finset.sum_congr rfl
        intro j hj
        have : j ≠ i := fun h => hnot (h ▸ hj)
        simp [this]
      rw [this, hcs]; simp

variable {n : ℕ}

lemma mem_playAllocations {I : Finset (Fin n)} {t : ℕ} {m : Fin n → ℕ} :
    m ∈ playAllocations I t ↔ (∀ j, j ∉ I → m j = 0) ∧ ∑ j, m j = t := by
  simp only [playAllocations, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · rintro ⟨_, h⟩; exact h
  · rintro ⟨h1, h2⟩
    refine ⟨fun j => ?_, h1, h2⟩
    have : m j ≤ ∑ j, m j := Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    omega

lemma sum_supp (I : Finset (Fin n)) (m : Fin n → ℕ) (h : ∀ j, j ∉ I → m j = 0) :
    ∑ j, m j = ∑ j ∈ I, m j := by
  symm; apply Finset.sum_subset (Finset.subset_univ _)
  intro j _ hj; exact h j hj

variable (H : Fin n → ℕ → ℝ)

lemma pis_obj {I : Finset (Fin n)} (hI : I ≠ ∅) (t : ℕ) :
    (∃ m ∈ playAllocations I t, partialInterleavedSum H I t = ∑ j, psum (H j) (m j)) ∧
    (∀ m ∈ playAllocations I t, ∑ j, psum (H j) (m j) ≤ partialInterleavedSum H I t) := by
  have hobj : ∀ m ∈ playAllocations I t,
      ∑ j ∈ I, ∑ u ∈ Finset.range (m j), H j u = ∑ j, psum (H j) (m j) := by
    intro m hm
    rw [mem_playAllocations] at hm
    unfold psum
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj; simp [hm.1 j hj]
  have hdef : partialInterleavedSum H I t = (playAllocations I t).sup' (playAllocations_nonempty hI t)
      fun m => ∑ j ∈ I, ∑ u ∈ Finset.range (m j), H j u := by
    unfold partialInterleavedSum; simp [hI]
  constructor
  · obtain ⟨m, hm, he⟩ := Finset.exists_mem_eq_sup' (playAllocations_nonempty hI t)
      (fun m => ∑ j ∈ I, ∑ u ∈ Finset.range (m j), H j u)
    exact ⟨m, hm, by rw [hdef, he, hobj m hm]⟩
  · intro m hm
    rw [hdef, ← hobj m hm]
    exact Finset.le_sup' (fun m => ∑ j ∈ I, ∑ u ∈ Finset.range (m j), H j u) hm

lemma pis_empty (t : ℕ) : partialInterleavedSum H (∅ : Finset (Fin n)) t = 0 := by
  simp [partialInterleavedSum]


lemma sum_three (I J : Finset (Fin n)) (b : Fin n → ℕ) (hb : ∀ j, j ∉ I ∪ J → b j = 0) :
    ∑ j, b j = ∑ j ∈ I ∩ J, b j + ∑ j ∈ I \ J, b j + ∑ j ∈ J \ I, b j := by
  rw [sum_supp (I ∪ J) b hb]
  have h1 := Finset.sum_union_inter (s₁ := I) (s₂ := J) (f := b)
  have h2 := Finset.sum_inter_add_sum_sdiff I J b
  have h3 := Finset.sum_inter_add_sum_sdiff J I b
  rw [Finset.inter_comm J I] at h3
  omega

lemma eq10_disjoint (_hanti : ∀ j, Antitone (H j)) (hnn : ∀ j k, 0 ≤ H j k)
    (I J : Finset (Fin n)) (hIJ : I ∩ J = ∅) (t : ℕ) :
    partialInterleavedSum H (I ∪ J) t ≤ partialInterleavedSum H I t + partialInterleavedSum H J t := by
  classical
  by_cases hI : I = ∅
  · subst hI; simp [pis_empty]
  by_cases hJ : J = ∅
  · subst hJ; simp [pis_empty]
  have hUne : I ∪ J ≠ ∅ := by
    intro h; apply hI; exact Finset.subset_empty.1 (h ▸ Finset.subset_union_left)
  obtain ⟨⟨b, hb, hbe⟩, _⟩ := pis_obj H hUne t
  rw [mem_playAllocations] at hb
  obtain ⟨hb1, hb2⟩ := hb
  have hb1' : ∀ j, j ∉ I ∪ J → b j = 0 := fun j hj => hb1 j hj
  obtain ⟨i0, hi0⟩ := Finset.nonempty_iff_ne_empty.2 hI
  obtain ⟨j0, hj0⟩ := Finset.nonempty_iff_ne_empty.2 hJ
  have hdisj : ∀ j, j ∈ I → j ∉ J := fun j hj hj' => by
    have : j ∈ I ∩ J := Finset.mem_inter.2 ⟨hj, hj'⟩
    rw [hIJ] at this; simp at this
  let c1 : Fin n → ℕ := fun j => if j ∈ I then b j else 0
  let d1 : Fin n → ℕ := fun j => if j ∈ J then b j else 0
  have hcd1 : ∀ j, c1 j + d1 j = b j := by
    intro j
    by_cases h1 : j ∈ I
    · have := hdisj j h1; simp [c1, d1, h1, this]
    · by_cases h2 : j ∈ J
      · simp [c1, d1, h1, h2]
      · simp [c1, d1, h1, h2, hb1 j (by simp [h1, h2])]
  have hsum1 : ∑ j, c1 j + ∑ j, d1 j = t := by
    rw [← Finset.sum_add_distrib, ← hb2]; exact Finset.sum_congr rfl (fun j _ => hcd1 j)
  let c : Fin n → ℕ := fun j => c1 j + (if j = i0 then t - ∑ j, c1 j else 0)
  let d : Fin n → ℕ := fun j => d1 j + (if j = j0 then t - ∑ j, d1 j else 0)
  have hc : c ∈ playAllocations I t := by
    rw [mem_playAllocations]
    refine ⟨fun j hj => ?_, ?_⟩
    · have : j ≠ i0 := fun h => hj (h ▸ hi0)
      simp [c, c1, hj, this]
    · simp only [c, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      omega
  have hd : d ∈ playAllocations J t := by
    rw [mem_playAllocations]
    refine ⟨fun j hj => ?_, ?_⟩
    · have : j ≠ j0 := fun h => hj (h ▸ hj0)
      simp [d, d1, hj, this]
    · simp only [d, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      omega
  have h1 := (pis_obj H hI t).2 c hc
  have h2 := (pis_obj H hJ t).2 d hd
  have key : ∀ j, psum (H j) (b j) ≤ psum (H j) (c j) + psum (H j) (d j) := by
    intro j
    have e0 : psum (H j) 0 = 0 := by simp [psum]
    have m1 : psum (H j) (c1 j) ≤ psum (H j) (c j) := psum_mono _ (hnn j) (Nat.le_add_right _ _)
    have m2 : psum (H j) (d1 j) ≤ psum (H j) (d j) := psum_mono _ (hnn j) (Nat.le_add_right _ _)
    by_cases h1 : j ∈ I
    · have h2 := hdisj j h1
      have : c1 j = b j := by simp [c1, h1]
      have : d1 j = 0 := by simp [d1, h2]
      have hn := hnn j
      have : psum (H j) (d j) ≥ 0 := Finset.sum_nonneg (fun i _ => hnn j i)
      simp_all
      linarith
    · by_cases h2 : j ∈ J
      · have : c1 j = 0 := by simp [c1, h1]
        have : d1 j = b j := by simp [d1, h2]
        have : psum (H j) (c j) ≥ 0 := Finset.sum_nonneg (fun i _ => hnn j i)
        simp_all
        linarith
      · have : b j = 0 := hb1 j (by simp [h1, h2])
        have : psum (H j) (c j) ≥ 0 := Finset.sum_nonneg (fun i _ => hnn j i)
        have : psum (H j) (d j) ≥ 0 := Finset.sum_nonneg (fun i _ => hnn j i)
        simp_all
        linarith
  rw [hbe]
  calc ∑ j, psum (H j) (b j) ≤ ∑ j, (psum (H j) (c j) + psum (H j) (d j)) :=
        Finset.sum_le_sum (fun j _ => key j)
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := add_le_add h1 h2

theorem eq10_core (hanti : ∀ j, Antitone (H j)) (hnn : ∀ j k, 0 ≤ H j k)
    (I J : Finset (Fin n)) (t : ℕ) :
    partialInterleavedSum H (I ∩ J) t + partialInterleavedSum H (I ∪ J) t ≤
      partialInterleavedSum H I t + partialInterleavedSum H J t := by
  classical
  by_cases hIJ : I ∩ J = ∅
  · rw [hIJ, pis_empty, zero_add]
    exact eq10_disjoint H hanti hnn I J hIJ t
  have hUne : I ∪ J ≠ ∅ := by
    intro h; apply hIJ
    have : I ∩ J ⊆ I ∪ J := (Finset.inter_subset_left).trans Finset.subset_union_left
    exact Finset.subset_empty.1 (h ▸ this)
  have hI : I ≠ ∅ := fun h => hIJ (by simp [h])
  have hJ : J ≠ ∅ := fun h => hIJ (by simp [h])
  obtain ⟨⟨a, ha, hae⟩, _⟩ := pis_obj H hIJ t
  obtain ⟨⟨b, hb, hbe⟩, _⟩ := pis_obj H hUne t
  rw [mem_playAllocations] at ha hb
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  have hb1' : ∀ j, j ∉ I ∪ J → b j = 0 := fun j hj => hb1 j hj
  have h3 := sum_three I J b hb1'
  have hasum : ∑ j ∈ I ∩ J, a j = t := by rw [← sum_supp _ a ha1]; exact ha2
  have hT1 : ∑ j ∈ I ∩ J, min (a j) (b j) ≤ t - ∑ j ∈ I \ J, b j := by
    have : ∑ j ∈ I ∩ J, min (a j) (b j) ≤ ∑ j ∈ I ∩ J, b j :=
      Finset.sum_le_sum (fun j _ => min_le_right _ _)
    omega
  have hT2 : t - ∑ j ∈ I \ J, b j ≤ ∑ j ∈ I ∩ J, max (a j) (b j) := by
    have : ∑ j ∈ I ∩ J, a j ≤ ∑ j ∈ I ∩ J, max (a j) (b j) :=
      Finset.sum_le_sum (fun j _ => le_max_left _ _)
    omega
  obtain ⟨c0, hc0, hc0s⟩ := exists_split (I ∩ J) (fun j => min (a j) (b j)) (fun j => max (a j) (b j))
    (fun j => min_le_max) _ hT1 hT2
  let c : Fin n → ℕ := fun j => if j ∈ I ∩ J then c0 j else if j ∈ I then b j else 0
  have hcA : ∀ j, j ∈ I ∩ J → c j = c0 j := fun j hj => by simp only [c]; rw [if_pos hj]
  have hcB : ∀ j, j ∈ I → j ∉ J → c j = b j := fun j hj hj' => by
    have : j ∉ I ∩ J := fun h => hj' (Finset.mem_inter.1 h).2
    simp only [c]; rw [if_neg this, if_pos hj]
  have hcC : ∀ j, j ∉ I → c j = 0 := fun j hj => by
    have : j ∉ I ∩ J := fun h => hj (Finset.mem_inter.1 h).1
    simp only [c]; rw [if_neg this, if_neg hj]
  have hcle : ∀ j, c j ≤ a j + b j := by
    intro j
    by_cases h : j ∈ I ∩ J
    · have h5 := (hc0 j h).2
      rw [hcA j h]
      omega
    · by_cases h' : j ∈ I
      · have := hcB j h' (fun hJ => h (Finset.mem_inter.2 ⟨h', hJ⟩))
        omega
      · have := hcC j h'
        omega
  let d : Fin n → ℕ := fun j => a j + b j - c j
  have hcd : ∀ j, c j + d j = a j + b j := fun j => by have := hcle j; simp only [d]; omega
  have hsc' : ∑ j, c j = t := by
    rw [sum_supp I c hcC]
    rw [← Finset.sum_inter_add_sum_sdiff I J c]
    have e1 : ∑ j ∈ I ∩ J, c j = ∑ j ∈ I ∩ J, c0 j :=
      Finset.sum_congr rfl (fun j hj => hcA j hj)
    have e2 : ∑ j ∈ I \ J, c j = ∑ j ∈ I \ J, b j :=
      Finset.sum_congr rfl (fun j hj => hcB j (Finset.mem_sdiff.1 hj).1 (Finset.mem_sdiff.1 hj).2)
    rw [e1, e2, hc0s]
    omega
  have hc : c ∈ playAllocations I t := by
    rw [mem_playAllocations]
    exact ⟨hcC, hsc'⟩
  have hd : d ∈ playAllocations J t := by
    rw [mem_playAllocations]
    have hsc : ∑ j, c j + ∑ j, d j = t + t := by
      rw [← Finset.sum_add_distrib]
      rw [Finset.sum_congr rfl (fun j _ => hcd j), Finset.sum_add_distrib, ha2, hb2]
    refine ⟨fun j hj => ?_, by omega⟩
    have haj : a j = 0 := ha1 j (fun h => hj (Finset.mem_inter.1 h).2)
    by_cases h' : j ∈ I
    · have := hcB j h' hj
      simp only [d]; omega
    · have := hcC j h'
      have : b j = 0 := hb1 j (by simp [h', hj])
      simp only [d]; omega
  have h1 := (pis_obj H hI t).2 c hc
  have h2 := (pis_obj H hJ t).2 d hd
  have key : ∀ j, psum (H j) (a j) + psum (H j) (b j) ≤ psum (H j) (c j) + psum (H j) (d j) := by
    intro j
    have e0 : psum (H j) 0 = 0 := by simp [psum]
    by_cases h : j ∈ I ∩ J
    · have hh := hc0 j h
      have hcj : c j = c0 j := hcA j h
      exact psum_pair' (H j) (hanti j) (by rw [hcj]; exact hh.1) (by rw [hcj]; exact hh.2) (hcd j)
    · have haj : a j = 0 := ha1 j h
      by_cases h' : j ∈ I
      · have hcj : c j = b j := hcB j h' (fun hJ => h (Finset.mem_inter.2 ⟨h', hJ⟩))
        have hdj : d j = 0 := by simp [d, hcj, haj]
        rw [haj, hcj, hdj, e0]; linarith
      · have hcj : c j = 0 := hcC j h'
        have hdj : d j = b j := by simp [d, hcj, haj]
        rw [haj, hcj, hdj, e0]
  rw [hae, hbe]
  calc ∑ j, psum (H j) (a j) + ∑ j, psum (H j) (b j)
      = ∑ j, (psum (H j) (a j) + psum (H j) (b j)) := Finset.sum_add_distrib.symm
    _ ≤ ∑ j, (psum (H j) (c j) + psum (H j) (d j)) := Finset.sum_le_sum (fun j _ => key j)
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := add_le_add h1 h2

end WeberGittins.Submodular

open WeberGittins.Submodular


theorem solution {n : ℕ} (H : Fin n → ℕ → ℝ)
    (hanti : ∀ j, Antitone (H j)) (hnonneg : ∀ j k, 0 ≤ H j k)
    (I J : Finset (Fin n)) (t : ℕ) :
    partialInterleavedSum H (I ∩ J) t + partialInterleavedSum H (I ∪ J) t ≤
      partialInterleavedSum H I t + partialInterleavedSum H J t := by
  exact eq10_core H hanti hnonneg I J t
