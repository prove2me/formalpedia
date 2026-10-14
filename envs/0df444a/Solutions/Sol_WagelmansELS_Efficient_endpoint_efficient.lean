-- Prove2me | solution 1 for WagelmansELS.Efficient.endpoint_efficient
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T22:14:20.645979+00:00
-- url     : https://prove2.me/submissions/8a38cf97-777e-4bdc-89e2-71b5a97ba6f0

import Mathlib
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

end Instance
end WagelmansELS.Efficient

open WagelmansELS.Efficient


theorem solution (P : Instance) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ P.n) :
    (∀ t ∈ Finset.Ioc i (P.n + 1), i + 1 < t → P.D t = P.D (i + 1) →
      P.G (i + 1) ≤ P.G t) ∧
    P.IsEfficient i (i + 1) ∧ P.IsEfficient i (P.n + 1) := by
  exact Instance.endpoint_efficient_core P i hi hin
