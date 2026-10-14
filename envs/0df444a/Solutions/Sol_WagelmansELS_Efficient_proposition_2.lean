-- Prove2me | solution 1 for WagelmansELS.Efficient.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T22:15:58.928109+00:00
-- url     : https://prove2.me/submissions/8c3f3567-17f9-488e-b078-c1b70a8b2851

import Mathlib
import Definitions.Def_WagelmansELS_Efficient_ThresholdRule



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

end Instance
end WagelmansELS.Efficient

open WagelmansELS.Efficient


theorem solution (P : Instance) (i k : ℕ)
    (hi : 1 ≤ i) (hin : i ≤ P.n)
    (hk : k ∈ P.E i) (hnext : k < P.n + 1) :
    (P.ratio i k < P.c i → P.score i k < P.score i (P.succ i k)) ∧
    (¬ P.ratio i k < P.c i → P.score i (P.succ i k) ≤ P.score i k) := by
  exact Instance.proposition_2_core P i k hi hin hk hnext
