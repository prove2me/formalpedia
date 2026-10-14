-- Prove2me | solution 1 for WagelmansELS.Efficient.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T22:18:01.016231+00:00
-- url     : https://prove2.me/submissions/f010ae17-0298-4e08-8655-ffd410affaa3

import Mathlib
import Definitions.Def_WagelmansELS_Efficient_ThresholdRule
import Definitions.Def_WagelmansELS_Efficient_EfficientPeriods



namespace WagelmansELS.Efficient
namespace Instance
variable (P : Instance)

lemma Gtable_succ_ne (m s : ℕ) (h : s ≠ P.n - m) : P.Gtable (m+1) s = P.Gtable m s := by
  simp [Gtable, h]

lemma Gtable_stable (k : ℕ) : ∀ m, m + k ≤ P.n → ∀ s, P.n - m < s →
    P.Gtable (m+k) s = P.Gtable m s := by
  induction k with
  | zero => intro m _ s _; rfl
  | succ k ih =>
    intro m hm s hs
    rw [← add_assoc, Gtable_succ_ne P (m+k) s (by omega)]
    exact ih m (by omega) s hs

lemma G_eq_stage (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ P.n) :
    P.G i = P.Gtable (P.n - i + 1) i := by
  have := Gtable_stable P (i-1) (P.n - i + 1) (by omega) i (by omega)
  have h2 : P.n - i + 1 + (i - 1) = P.n := by omega
  rw [h2] at this
  exact this

lemma G_old (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ P.n) (s : ℕ) (hs : i < s) :
    P.Gtable (P.n - i) s = P.G s := by
  have := Gtable_stable P i (P.n - i) (by omega) s (by omega)
  have h2 : P.n - i + i = P.n := by omega
  rw [h2] at this
  exact this.symm

lemma G_le_succ (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ P.n) (hd : P.d i = 0) :
    P.G i ≤ P.G (i+1) := by
  rw [G_eq_stage P i hi hin]
  have hm : P.n - (P.n - i) = i := by omega
  have hd' : ¬ 0 < P.d i := by simp [hd]
  simp only [Gtable, hm, if_true, hd', if_false]
  have h1 : P.Gtable (P.n - i) (i+1) = P.G (i+1) := G_old P i hi hin (i+1) (by omega)
  rw [h1]
  exact min_le_left _ _

lemma D_succ (i : ℕ) (hin : i ≤ P.n) : P.D i = P.d i + P.D (i+1) := by
  unfold D
  have : Finset.Icc i P.n = insert i (Finset.Icc (i+1) P.n) := by
    ext x; simp; omega
  rw [this, Finset.sum_insert (by simp)]

lemma D_nonneg (t : ℕ) (ht : 1 ≤ t) : 0 ≤ P.D t := by
  unfold D
  apply Finset.sum_nonneg
  intro j hj
  simp at hj
  exact P.d_nonneg j (by omega) hj.2

lemma D_anti (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) : P.D b ≤ P.D a := by
  unfold D
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx; simp at hx ⊢; omega
  · intro j hj _
    simp at hj
    exact P.d_nonneg j (by omega) hj.2

lemma D_last : P.D (P.n + 1) = 0 := by
  unfold D
  simp

lemma D_pos (t : ℕ) (ht1 : 1 ≤ t) (ht : t ≤ P.n) : 0 < P.D t := by
  unfold D
  have h1 : 0 < P.d P.n := P.d_last_pos
  calc 0 < P.d P.n := h1
    _ ≤ _ := Finset.single_le_sum (f := P.d) (fun j hj => by
        simp at hj; exact P.d_nonneg j (by omega) hj.2) (by simp; omega)

lemma G_chain (i : ℕ) (hi : 1 ≤ i) : ∀ k, i + 1 + k ≤ P.n + 1 → P.D (i+1+k) = P.D (i+1) →
    P.G (i+1) ≤ P.G (i+1+k) := by
  intro k
  induction k with
  | zero => intro _ _; exact le_rfl
  | succ k ih =>
    intro hk hD
    have hle : P.D (i+1+(k+1)) ≤ P.D (i+1+k) := P.D_anti _ _ (by omega) (by omega)
    have hle2 : P.D (i+1+k) ≤ P.D (i+1) := P.D_anti _ _ (by omega) (by omega)
    have heq : P.D (i+1+k) = P.D (i+1) := by
      have := P.D_nonneg (i+1+(k+1)) (by omega); linarith
    have h1 := ih (by omega) heq
    have hs := P.D_succ (i+1+k) (by omega)
    have hd0 : P.d (i+1+k) = 0 := by
      have : i + 1 + k + 1 = i + 1 + (k+1) := by omega
      rw [this] at hs; linarith
    have h2 := G_le_succ P (i+1+k) (by omega) (by omega) hd0
    have : i + 1 + k + 1 = i + 1 + (k+1) := by omega
    rw [this] at h2
    exact h1.trans h2

theorem endpoint_efficient_core (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ P.n) :
    (∀ t ∈ Finset.Ioc i (P.n + 1), i + 1 < t → P.D t = P.D (i + 1) →
      P.G (i + 1) ≤ P.G t) ∧
    P.IsEfficient i (i + 1) ∧ P.IsEfficient i (P.n + 1) := by
  have key : ∀ t ∈ Finset.Ioc i (P.n + 1), i + 1 < t → P.D t = P.D (i + 1) →
      P.G (i + 1) ≤ P.G t := by
    intro t ht hlt hD
    simp at ht
    have := G_chain P i hi (t - (i+1)) (by omega)
    have e : i + 1 + (t - (i+1)) = t := by omega
    rw [e] at this
    exact this hD
  refine ⟨key, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · simp; omega
  · intro u hu hne hD
    have hu' := hu
    simp at hu'
    have hlt : i + 1 < u := by omega
    have := key u hu hlt hD
    rcases this.lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, by omega⟩
  · rintro ⟨u, hu, w, hw, h1, h2, _⟩
    simp at hw
    have := P.D_anti (i+1) w (by omega) (by omega)
    linarith
  · simp; omega
  · intro u hu hne hD
    simp at hu
    exfalso
    have : u ≤ P.n := by omega
    have := P.D_pos u (by omega) this
    rw [D_last] at hD
    linarith
  · rintro ⟨u, hu, w, hw, h1, h2, _⟩
    simp at hu
    have := P.D_nonneg u (by omega)
    rw [D_last] at h1
    linarith

lemma mem_E (i t : ℕ) : t ∈ P.E i ↔ P.IsEfficient i t := by
  unfold E
  simp only [Finset.mem_filter]
  constructor
  · intro h; exact h.2
  · intro h; exact ⟨h.1, h⟩

lemma D_strict (i t u : ℕ) (hi : 1 ≤ i) (ht : t ∈ P.E i) (hu : u ∈ P.E i) (htu : t < u) :
    P.D u < P.D t := by
  rw [mem_E] at ht hu
  have h1 := P.D_anti t u (by have := ht.1; simp at this; omega) htu.le
  rcases h1.lt_or_eq with h | h
  · exact h
  · exfalso
    have a := ht.2.1 u hu.1 (by omega) h
    have b := hu.2.1 t ht.1 (by omega) h.symm
    rcases a with a | a <;> rcases b with b | b
    · linarith
    · linarith [b.1]
    · linarith [a.1]
    · omega

lemma last_mem_E (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ P.n) : P.n + 1 ∈ P.E i := by
  rw [mem_E]; exact (endpoint_efficient_core P i hi hin).2.2

lemma succ_spec (i k : ℕ) (hi : 1 ≤ i) (hin : i ≤ P.n) (hk : k ∈ P.E i) (hnext : k < P.n + 1) :
    P.succ i k ∈ P.E i ∧ k < P.succ i k := by
  have hS : ((P.E i).filter (fun u => k < u)).Nonempty :=
    ⟨P.n + 1, by simp only [Finset.mem_filter]; exact ⟨P.last_mem_E i hi hin, hnext⟩⟩
  unfold succ
  simp only [dif_pos hS]
  have := Finset.min'_mem _ hS
  simp only [Finset.mem_filter] at this
  exact this

theorem proposition_2_core (i k : ℕ)
    (hi : 1 ≤ i) (hin : i ≤ P.n)
    (hk : k ∈ P.E i) (hnext : k < P.n + 1) :
    (P.ratio i k < P.c i → P.score i k < P.score i (P.succ i k)) ∧
    (¬ P.ratio i k < P.c i → P.score i (P.succ i k) ≤ P.score i k) := by
  obtain ⟨h1, h2⟩ := P.succ_spec i k hi hin hk hnext
  have hD := P.D_strict i k _ hi hk h1 h2
  have hpos : 0 < P.D k - P.D (P.succ i k) := by linarith
  unfold ratio score
  constructor
  · intro h
    rw [div_lt_iff₀ hpos] at h
    nlinarith
  · intro h
    rw [not_lt, le_div_iff₀ hpos] at h
    nlinarith

theorem ordered_ratios_core (i t t' : ℕ)
    (hi : 1 ≤ i) (hin : i ≤ P.n)
    (ht : t ∈ P.E i) (ht' : t' ∈ P.E i)
    (hs : t' = P.succ i t) (hnext : t' < P.n + 1) :
    P.ratio i t > P.ratio i t' := by
  have htn : t < P.n + 1 := by
    by_contra hcon
    have hm := ((P.mem_E i t).1 ht).1
    simp at hm
    have he : t = P.n + 1 := by omega
    have hsn : P.succ i t = P.n + 1 := by
      unfold succ
      have : ¬ ((P.E i).filter (fun u => t < u)).Nonempty := by
        rintro ⟨u, hu⟩
        simp only [Finset.mem_filter] at hu
        have := ((P.mem_E i u).1 hu.1).1
        simp at this
        omega
      simp only [dif_neg this]
    omega
  have hS := P.succ_spec i t hi hin ht htn
  rw [← hs] at hS
  obtain ⟨h1, h2⟩ := hS
  obtain ⟨h3, h4⟩ := P.succ_spec i t' hi hin ht' hnext
  set t'' := P.succ i t' with ht''
  have hDa := P.D_strict i t t' hi ht ht' h2
  have hDb := P.D_strict i t' t'' hi ht' h3 h4
  have hneg := ((P.mem_E i t').1 ht').2.2
  have hm1 := ((P.mem_E i t).1 ht).1
  have hm3 := ((P.mem_E i t'').1 h3).1
  have hrt : P.ratio i t = (P.G t - P.G t') / (P.D t - P.D t') := by
    unfold ratio; rw [← hs]
  have hrt' : P.ratio i t' = (P.G t' - P.G t'') / (P.D t' - P.D t'') := by
    unfold ratio; rw [ht'']
  rw [gt_iff_lt, hrt, hrt', div_lt_div_iff₀ (by linarith) (by linarith)]
  by_contra hcon
  apply hneg
  refine ⟨t'', hm3, t, hm1, hDb, hDa, ?_⟩
  push_neg at hcon
  nlinarith

theorem proposition_1_core (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ P.n) :
    (P.E i).Nonempty ∧
    ∀ h : (P.E i).Nonempty,
      (Finset.Ioc i (P.n + 1)).inf' (by simp; omega) (P.score i) =
        (P.E i).inf' h (P.score i) := by
  have hne : (Finset.Ioc i (P.n + 1)).Nonempty := ⟨P.n + 1, by simp; omega⟩
  set m := (Finset.Ioc i (P.n + 1)).inf' hne (P.score i) with hm
  set S1 := (Finset.Ioc i (P.n + 1)).filter (fun t => P.score i t = m) with hS1
  have hS1ne : S1.Nonempty := by
    obtain ⟨t, ht, h⟩ := Finset.exists_mem_eq_inf' hne (P.score i)
    exact ⟨t, by simp only [hS1, Finset.mem_filter]; exact ⟨ht, h.symm⟩⟩
  obtain ⟨t0, ht0, hmin⟩ := Finset.exists_min_image S1 P.D hS1ne
  set S2 := S1.filter (fun t => P.D t = P.D t0) with hS2
  have hS2ne : S2.Nonempty := ⟨t0, Finset.mem_filter.2 ⟨ht0, rfl⟩⟩
  set ts := S2.min' hS2ne with hts
  have hts2 : ts ∈ S2 := Finset.min'_mem _ _
  have hts1 : ts ∈ S1 := (Finset.mem_filter.1 hts2).1
  have htsD : P.D ts = P.D t0 := (Finset.mem_filter.1 hts2).2
  have hI : ts ∈ Finset.Ioc i (P.n + 1) := (Finset.mem_filter.1 hts1).1
  have hsc : P.score i ts = m := (Finset.mem_filter.1 hts1).2
  have hge : ∀ u ∈ Finset.Ioc i (P.n + 1), m ≤ P.score i u := fun u hu =>
    Finset.inf'_le _ hu
  have hEff : ts ∈ P.E i := by
    rw [mem_E]
    refine ⟨hI, ?_, ?_⟩
    · intro u hu hne' hD
      have hGu : P.G u = P.G ts ∨ P.G ts < P.G u := by
        have := hge u hu
        unfold score at this hsc
        rw [hD] at this
        rcases le_or_gt (P.G ts) (P.G u) with h | h
        · rcases h.lt_or_eq with h | h
          · exact Or.inr h
          · exact Or.inl h.symm
        · linarith
      rcases hGu with h | h
      · right
        refine ⟨h.symm, ?_⟩
        by_contra hlt
        have hlt' : u < ts := by omega
        have hus : u ∈ S2 := by
          simp only [hS2, hS1, Finset.mem_filter]
          refine ⟨⟨hu, ?_⟩, by rw [hD, htsD]⟩
          unfold score at hsc ⊢; rw [hD, h, ← hsc]
        have := Finset.min'_le _ _ hus
        omega
      · exact Or.inl h
    · rintro ⟨u, hu, w, hw, h1, h2, h3⟩
      have hsu := hge u hu
      have hsw := hge w hw
      have hsu' : m ≤ P.c i * (P.D i - P.D u) + P.G u := hsu
      have hsw' : m ≤ P.c i * (P.D i - P.D w) + P.G w := hsw
      have hsc' : P.c i * (P.D i - P.D ts) + P.G ts = m := hsc
      have key : (P.D w - P.D ts) * (P.c i * (P.D i - P.D u) + P.G u - m) +
          (P.D ts - P.D u) * (P.c i * (P.D i - P.D w) + P.G w - m) ≤ 0 := by
        have e : m = P.c i * (P.D i - P.D ts) + P.G ts := hsc'.symm
        rw [e]
        nlinarith [h3]
      have hu1 : P.c i * (P.D i - P.D u) + P.G u ≤ m := by
        by_contra hc
        push_neg at hc
        nlinarith [mul_pos (sub_pos.2 h2) (sub_pos.2 hc),
          mul_nonneg (sub_pos.2 h1).le (sub_nonneg.2 hsw')]
      have hui := (Finset.mem_Ioc.1 hu)
      have hu1' : P.score i u = m := le_antisymm hu1 hsu
      have huS1 : u ∈ S1 := Finset.mem_filter.2 ⟨hu, hu1'⟩
      have := hmin u huS1
      linarith
  have hEne : (P.E i).Nonempty := ⟨ts, hEff⟩
  refine ⟨hEne, fun h => ?_⟩
  apply le_antisymm
  · exact Finset.inf'_mono _ (fun x hx => ((P.mem_E i x).1 hx).1) h
  · calc (P.E i).inf' h (P.score i) ≤ P.score i ts := Finset.inf'_le _ hEff
      _ = _ := hsc

end Instance
end WagelmansELS.Efficient

open WagelmansELS.Efficient


theorem solution (P : Instance) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ P.n) :
    (P.E i).Nonempty ∧
    ∀ h : (P.E i).Nonempty,
      (Finset.Ioc i (P.n + 1)).inf' (by simp; omega) (P.score i) =
        (P.E i).inf' h (P.score i) := by
  exact Instance.proposition_1_core P i hi hin
