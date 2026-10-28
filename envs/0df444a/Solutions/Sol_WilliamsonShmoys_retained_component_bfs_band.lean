-- Prove2me | solution 1 for WilliamsonShmoys.retained_component_bfs_band
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T21:32:14.131572+00:00
-- url     : https://prove2.me/submissions/ae470250-6064-4f1c-abcf-6cd9d98e6c43

import Definitions.Def_WilliamsonShmoys_BakerLevel
import Mathlib.Combinatorics.SimpleGraph.Metric
set_option autoImplicit false

namespace A3S55BB
open WilliamsonShmoys

lemma root_eq {n : Nat} (G : SimpleGraph (Fin n)) {a b : Fin n} (h : G.Reachable a b) :
    bakerRoot G a = bakerRoot G b := by
  have hh : ∀ u, G.Reachable u a ↔ G.Reachable u b :=
    fun u => ⟨fun h' => h'.trans h, fun h' => h'.trans h.symm⟩
  unfold bakerRoot
  congr 1
  ext u
  simp [hh]

lemma root_reach {n : Nat} (G : SimpleGraph (Fin n)) (v : Fin n) :
    G.Reachable (bakerRoot G v) v := by
  classical
  have := Finset.min'_mem (Finset.univ.filter (fun u => G.Reachable u v))
    ⟨v, Finset.mem_filter.2 ⟨Finset.mem_univ v, SimpleGraph.Reachable.refl v⟩⟩
  unfold bakerRoot
  convert (Finset.mem_filter.1 this).2

lemma dist_step {n : Nat} (G : SimpleGraph (Fin n)) {r a b : Fin n} (hr : G.Reachable r a)
    (hab : G.Adj a b) : G.dist r b ≤ G.dist r a + 1 := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  have := SimpleGraph.dist_le (p.concat hab)
  simp [SimpleGraph.Walk.length_concat] at this
  omega

lemma dvd_imp {k j m : Nat} (hj : j < k) (h : k ∣ m + k - j) : m % k = j := by
  obtain ⟨c, hc⟩ := h
  cases c with
  | zero => simp at hc; omega
  | succ c =>
    rw [mul_add, mul_one] at hc
    have : m = k * c + j := by omega
    rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]

lemma beta_step {k j m : Nat} (hj : j < k) (h1 : m % k ≠ j) (h2 : (m + 1) % k ≠ j) :
    (m + 1 + k - j) / k = (m + k - j) / k := by
  have e : m + 1 + k - j = (m + k - j) + 1 := by omega
  rw [e, Nat.succ_div]
  have : ¬ k ∣ (m + k - j) + 1 := by
    intro hd
    apply h2
    apply dvd_imp hj
    rwa [e]
  simp [this]

lemma beta_adj {k j a b : Nat} (hj : j < k) (ha : a % k ≠ j) (hb : b % k ≠ j)
    (h1 : b ≤ a + 1) (h2 : a ≤ b + 1) : (a + k - j) / k = (b + k - j) / k := by
  rcases (show b = a ∨ b = a + 1 ∨ a = b + 1 by omega) with h | h | h
  · rw [h]
  · subst h; exact (beta_step hj ha hb).symm
  · subst h; exact beta_step hj hb ha

lemma core {n : Nat} (G : SimpleGraph (Fin n)) (k j : Nat) (hj : j < k)
    (u v : {x : Fin n // bakerLevel G x % k ≠ j})
    (p : (G.induce {x : Fin n | bakerLevel G x % k ≠ j}).Walk u v) :
    G.Reachable u.1 v.1 ∧
      (bakerLevel G u.1 + k - j) / k = (bakerLevel G v.1 + k - j) / k := by
  induction p with
  | nil => exact ⟨SimpleGraph.Reachable.refl _, rfl⟩
  | @cons a b c h p ih =>
    have hab : G.Adj a.1 b.1 := h
    obtain ⟨hr, hb⟩ := ih
    have hrab : G.Reachable a.1 b.1 := hab.reachable
    refine ⟨hrab.trans hr, ?_⟩
    rw [← hb]
    have re := root_eq G hrab
    have ha2 : bakerLevel G a.1 % k ≠ j := a.2
    have hb2 : bakerLevel G b.1 % k ≠ j := b.2
    have s1 := dist_step G (root_reach G a.1) hab
    have s2 := dist_step G (re ▸ root_reach G b.1) hab.symm
    have e1 : bakerLevel G b.1 ≤ bakerLevel G a.1 + 1 := by
      unfold bakerLevel; rw [← re]; exact s1
    have e2 : bakerLevel G a.1 ≤ bakerLevel G b.1 + 1 := by
      unfold bakerLevel; rw [← re]; exact s2
    exact beta_adj hj ha2 hb2 e1 e2

lemma band {k j m L : Nat} (hj : j < k) (hm : m % k ≠ j)
    (hb : (m + k - j) / k = (L + k - j) / k) :
    k * ((L + k - j) / k) + j + 1 - k ≤ m ∧ m ≤ k * ((L + k - j) / k) + j - 1 := by
  have h1 := Nat.div_add_mod (m + k - j) k
  have h2 := Nat.mod_lt (m + k - j) (by omega : 0 < k)
  have h3 : (m + k - j) % k ≠ 0 := by
    intro h0
    exact hm (dvd_imp hj (Nat.dvd_of_mod_eq_zero h0))
  rw [hb] at h1
  generalize k * ((L + k - j) / k) = P at *
  generalize (m + k - j) % k = r at *
  omega

end A3S55BB

theorem solution {n : Nat} (G : SimpleGraph (Fin n)) (k j : Nat) (hk : 0 < k) (hj : j < k) (v : {x : Fin n // WilliamsonShmoys.bakerLevel G x % k ≠ j}) : ∃ lo hi : Nat, hi - lo < k ∧ ∀ u : {x : Fin n // WilliamsonShmoys.bakerLevel G x % k ≠ j}, (G.induce {x : Fin n | WilliamsonShmoys.bakerLevel G x % k ≠ j}).Reachable u v → G.Reachable (WilliamsonShmoys.bakerRoot G v.1) u.1 ∧ lo ≤ G.dist (WilliamsonShmoys.bakerRoot G v.1) u.1 ∧ G.dist (WilliamsonShmoys.bakerRoot G v.1) u.1 ≤ hi := by
  refine ⟨k * ((WilliamsonShmoys.bakerLevel G v.1 + k - j) / k) + j + 1 - k,
    k * ((WilliamsonShmoys.bakerLevel G v.1 + k - j) / k) + j - 1, by omega, ?_⟩
  rintro u ⟨p⟩
  obtain ⟨hr, hb⟩ := A3S55BB.core G k j hj u v p
  have re := A3S55BB.root_eq G hr
  have hl : WilliamsonShmoys.bakerLevel G u.1 = G.dist (WilliamsonShmoys.bakerRoot G v.1) u.1 := by
    unfold WilliamsonShmoys.bakerLevel; rw [re]
  rw [← hl, ← re]
  exact ⟨A3S55BB.root_reach G u.1, A3S55BB.band hj u.2 hb⟩

