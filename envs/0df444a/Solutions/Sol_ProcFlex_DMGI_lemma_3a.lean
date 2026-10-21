-- Prove2me | solution 1 for ProcFlex.DMGI.lemma_3a
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:34:03.175537+00:00
-- url     : https://prove2.me/submissions/78b9ef55-d81f-45f4-a2dd-8542637120ef

import Mathlib
set_option autoImplicit false
open Finset

theorem dmgi_ivt (g : ℕ → ℤ) (hg : ∀ s, g (s+1) - g s ≤ 1 ∧ g s - g (s+1) ≤ 1) (l : ℤ) :
    ∀ d a : ℕ, g a ≤ l → l ≤ g (a+d) → ∃ s, g s = l := by
  intro d
  induction d with
  | zero => intro a h1 h2; exact ⟨a, le_antisymm h1 h2⟩
  | succ d ih =>
    intro a h1 h2
    by_cases h : l ≤ g (a+d)
    · exact ih a h1 h
    · rw [not_le] at h
      refine ⟨a+(d+1), ?_⟩
      have := hg (a+d)
      rw [← add_assoc] at h2 ⊢
      omega

theorem dmgi_ivt2 (g : ℕ → ℤ) (hg : ∀ s, g (s+1) - g s ≤ 1 ∧ g s - g (s+1) ≤ 1) (l : ℤ)
    (a b : ℕ) (h1 : g a ≤ l) (h2 : l ≤ g b) : ∃ s, g s = l := by
  rcases le_total a b with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    exact dmgi_ivt g hg l d a h1 h2
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have := dmgi_ivt (fun s => - g s) (fun s => by have := hg s; constructor <;> omega) (-l) d b
      (by simpa using h2) (by simpa using h1)
    obtain ⟨s, hs⟩ := this
    exact ⟨s, by simpa using hs⟩

/-- indicator of colour `true` at position `t mod 2k` -/
def dB (k : ℕ) (hk : 1 ≤ k) (c : Fin (2 * k) → Bool) (t : ℕ) : ℕ :=
  if c ⟨t % (2 * k), Nat.mod_lt _ (by omega)⟩ = true then 1 else 0

/-- number of `true` in the cyclic window of length `m` starting at `s` -/
def dW (k : ℕ) (hk : 1 ≤ k) (c : Fin (2 * k) → Bool) (m s : ℕ) : ℕ :=
  ∑ q ∈ range m, dB k hk c (s + q)

theorem dW_card (k : ℕ) (hk : 1 ≤ k) (c : Fin (2 * k) → Bool) (m s : ℕ) :
    dW k hk c m s = ((range m).filter
        (fun q : ℕ => c ⟨(s + q) % (2 * k), Nat.mod_lt _ (by omega)⟩ = true)).card := by
  unfold dW dB
  rw [Finset.card_filter]

theorem dW_step (k : ℕ) (hk : 1 ≤ k) (c : Fin (2 * k) → Bool) (m s : ℕ) :
    (dW k hk c m (s+1) : ℤ) - dW k hk c m s = (dB k hk c (s + m) : ℤ) - dB k hk c s := by
  unfold dW
  have h1 : ∑ q ∈ range (m+1), dB k hk c (s + q) =
      ∑ q ∈ range m, dB k hk c (s + q) + dB k hk c (s + m) := Finset.sum_range_succ _ _
  have h2 : ∑ q ∈ range (m+1), dB k hk c (s + q) =
      ∑ q ∈ range m, dB k hk c (s + (q+1)) + dB k hk c (s + 0) := Finset.sum_range_succ' _ _
  have h3 : ∀ q, s + 1 + q = s + (q + 1) := fun q => by omega
  simp only [h3]
  simp only [add_zero] at h2
  omega

theorem dB_sum (k : ℕ) (hk : 1 ≤ k) (c : Fin (2 * k) → Bool)
    (hc : (univ.filter (fun i => c i = true)).card = k) (q : ℕ) :
    ∑ s ∈ range (2 * k), dB k hk c (s + q) = k := by
  have : NeZero (2 * k) := ⟨by omega⟩
  rw [Finset.sum_range]
  have key : ∀ s : Fin (2 * k), dB k hk c (s.val + q) =
      (fun j : Fin (2 * k) => if c j = true then 1 else 0) (s + (Fin.ofNat (2 * k) q)) := by
    intro s
    unfold dB
    have : (s + (Fin.ofNat (2 * k) q)) = ⟨(s.val + q) % (2 * k), Nat.mod_lt _ (by omega)⟩ := by
      apply Fin.ext
      rw [Fin.val_add, Fin.val_ofNat]
      simp [Nat.add_mod]
    simp only [this]
  rw [Finset.sum_congr rfl (fun s _ => key s)]
  refine Eq.trans (Equiv.sum_comp (Equiv.addRight (Fin.ofNat (2 * k) q))
    (fun j : Fin (2 * k) => if c j = true then 1 else 0)) ?_
  exact (Finset.card_filter _ _).symm.trans hc

theorem dW_sum (k : ℕ) (hk : 1 ≤ k) (c : Fin (2 * k) → Bool)
    (hc : (univ.filter (fun i => c i = true)).card = k) (m : ℕ) :
    ∑ s ∈ range (2 * k), dW k hk c m s = m * k := by
  unfold dW
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun q _ => dB_sum k hk c hc q)]
  simp

theorem dB_le (k : ℕ) (hk : 1 ≤ k) (c : Fin (2 * k) → Bool) (t : ℕ) : dB k hk c t ≤ 1 := by
  unfold dB; split_ifs <;> omega

theorem dW_mod (k : ℕ) (hk : 1 ≤ k) (c : Fin (2 * k) → Bool) (m s : ℕ) :
    dW k hk c m (s % (2 * k)) = dW k hk c m s := by
  unfold dW dB
  refine Finset.sum_congr rfl (fun q _ => ?_)
  simp only [Nat.mod_add_mod]

theorem dmgi_core (k : ℕ) (hk : 1 ≤ k) (c : Fin (2 * k) → Bool)
    (hc : (univ.filter (fun i => c i = true)).card = k) (m l : ℕ)
    (hlo : m * k < 2 * k * (l + 1)) (hhi : 2 * k * l < m * k + 2 * k) :
    ∃ s : Fin (2 * k),
      ((range m).filter
        (fun q : ℕ => c ⟨(s.val + q) % (2 * k), Nat.mod_lt _ (by omega)⟩ = true)).card = l := by
  have hsum := dW_sum k hk c hc m
  have ha : ∃ a, dW k hk c m a ≤ l := by
    by_contra hcon
    push Not at hcon
    have : (range (2 * k)).card • (l + 1) ≤ ∑ s ∈ range (2 * k), dW k hk c m s :=
      Finset.card_nsmul_le_sum _ _ _ (fun s _ => hcon s)
    rw [hsum, card_range, smul_eq_mul] at this
    omega
  have hb : ∃ b, l ≤ dW k hk c m b := by
    by_contra hcon
    push Not at hcon
    have : ∑ s ∈ range (2 * k), (dW k hk c m s + 1) ≤ (range (2 * k)).card • l :=
      Finset.sum_le_card_nsmul _ _ _ (fun s _ => hcon s)
    rw [Finset.sum_add_distrib, hsum, card_range, smul_eq_mul] at this
    simp at this
    omega
  obtain ⟨a, ha⟩ := ha
  obtain ⟨b, hb⟩ := hb
  have hg : ∀ s, (fun s => (dW k hk c m s : ℤ)) (s+1) - (fun s => (dW k hk c m s : ℤ)) s ≤ 1 ∧
      (fun s => (dW k hk c m s : ℤ)) s - (fun s => (dW k hk c m s : ℤ)) (s+1) ≤ 1 := by
    intro s
    have h := dW_step k hk c m s
    have h1 := dB_le k hk c (s + m)
    have h2 := dB_le k hk c s
    simp only
    omega
  obtain ⟨s, hs⟩ := dmgi_ivt2 (fun s => (dW k hk c m s : ℤ)) hg (l : ℤ) a b (by exact_mod_cast ha) (by exact_mod_cast hb)
  have hs' : dW k hk c m s = l := by exact_mod_cast hs
  refine ⟨⟨s % (2 * k), Nat.mod_lt _ (by omega)⟩, ?_⟩
  rw [← dW_card]
  show dW k hk c m (s % (2 * k)) = l
  rw [dW_mod]; exact hs'

theorem solution (k : ℕ) (hk : 1 ≤ k)
    (c : Fin (2 * k) → Bool)
    (hc : (univ.filter (fun i => c i = true)).card = k)
    (l : ℕ) (hl : 1 ≤ l) (hlu : l ≤ k - 1) :
    ∃ s : Fin (2 * k),
      ((range (2 * l + 1)).filter
        (fun q : ℕ => c ⟨(s.val + q) % (2 * k), Nat.mod_lt _ (by omega)⟩ = true)).card = l := by
  apply dmgi_core k hk c hc
  · nlinarith
  · nlinarith
