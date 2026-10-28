-- Prove2me | solution 1 for SpectralSparsify.Pullback.lemma_10_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:08:11.244066+00:00
-- url     : https://prove2.me/submissions/da676e6c-5e86-47d6-a7f0-d86cd6bc8fad

import Mathlib
import Definitions.Def_SpectralSparsify_Pullback_WeightedGraph
import Definitions.Def_SpectralSparsify_Pullback_PathGraph

namespace Aux_SS103

lemma double_delta {V : Type*} [Fintype V] [DecidableEq V] (a b : V) (F : V → V → ℝ) :
    ∑ a', ∑ b', (if a' = a ∧ b' = b then F a' b' else 0) = F a b := by
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro b' _ hb'
      simp [hb']
    · simp
  · intro a' _ ha'
    apply Finset.sum_eq_zero
    intro b' _
    simp [ha']
  · simp

lemma edge_lap {V : Type*} [Fintype V] [DecidableEq V] (a b : V) (c : ℝ) (hab : a ≠ b)
    (x : V → ℝ) :
    (1 / 2) * ∑ a', ∑ b', (if (a' = a ∧ b' = b) ∨ (a' = b ∧ b' = a) then c else 0) *
      (x a' - x b') ^ 2 = c * (x a - x b) ^ 2 := by
  have split : ∀ a' b' : V, (if (a' = a ∧ b' = b) ∨ (a' = b ∧ b' = a) then c else 0) =
      (if a' = a ∧ b' = b then c else 0) + (if a' = b ∧ b' = a then c else 0) := by
    intro a' b'
    by_cases h1 : a' = a ∧ b' = b
    · have h2 : ¬ (a' = b ∧ b' = a) := by
        rintro ⟨h3, -⟩
        exact hab (h1.1.symm.trans h3)
      rw [if_pos (Or.inl h1), if_pos h1, if_neg h2, add_zero]
    · by_cases h2 : a' = b ∧ b' = a
      · rw [if_pos (Or.inr h2), if_neg h1, if_pos h2, zero_add]
      · rw [if_neg (not_or.mpr ⟨h1, h2⟩), if_neg h1, if_neg h2, add_zero]
  simp_rw [split, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
  simp only [double_delta]
  ring

end Aux_SS103

open SpectralSparsify.Pullback in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 1 ≤ k)
    (p : Fin (k + 1) → V) (hp : Function.Injective p) (wt : Fin k → ℝ) (hwt : ∀ i, 0 < wt i)
    (u v : V) (hu : p 0 = u) (hv : p (Fin.last k) = v) :
    GraphLE (unitEdge u v) ((∑ i, 1 / wt i) • pathGraph p wt) := by
  intro x
  set S := ∑ i, 1 / wt i with hS
  have huv : u ≠ v := by
    rw [← hu, ← hv]
    intro h
    have := hp h
    rw [Fin.ext_iff] at this
    simp at this
    omega
  have hL : SpectralSparsify.Sampling.lapForm (unitEdge u v) x = (x u - x v) ^ 2 := by
    unfold SpectralSparsify.Sampling.lapForm unitEdge
    rw [Aux_SS103.edge_lap u v 1 huv x, one_mul]
  set d : Fin k → ℝ := fun i => x (p i.castSucc) - x (p i.succ) with hd
  have hR : SpectralSparsify.Sampling.lapForm (S • pathGraph p wt) x =
      S * ∑ i, wt i * d i ^ 2 := by
    unfold SpectralSparsify.Sampling.lapForm pathGraph
    simp only [Pi.smul_apply, smul_eq_mul]
    have e1 : ∑ a, ∑ b, (S * ∑ i : Fin k, (if (a = p i.castSucc ∧ b = p i.succ) ∨
        (a = p i.succ ∧ b = p i.castSucc) then wt i else 0)) * (x a - x b) ^ 2 =
        ∑ i : Fin k, S * ∑ a, ∑ b, (if (a = p i.castSucc ∧ b = p i.succ) ∨
        (a = p i.succ ∧ b = p i.castSucc) then wt i else 0) * (x a - x b) ^ 2 := by
      calc _ = ∑ a, ∑ b, ∑ i : Fin k, S * ((if (a = p i.castSucc ∧ b = p i.succ) ∨
            (a = p i.succ ∧ b = p i.castSucc) then wt i else 0) * (x a - x b) ^ 2) := by
            refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
            rw [Finset.mul_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl (fun i _ => by ring)
        _ = ∑ a, ∑ i : Fin k, ∑ b, S * ((if (a = p i.castSucc ∧ b = p i.succ) ∨
            (a = p i.succ ∧ b = p i.castSucc) then wt i else 0) * (x a - x b) ^ 2) :=
            Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
        _ = ∑ i : Fin k, ∑ a, ∑ b, S * ((if (a = p i.castSucc ∧ b = p i.succ) ∨
            (a = p i.succ ∧ b = p i.castSucc) then wt i else 0) * (x a - x b) ^ 2) :=
            Finset.sum_comm
        _ = _ := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun a _ => ?_)
            rw [Finset.mul_sum]
    rw [e1, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hne : p i.castSucc ≠ p i.succ := by
      intro h
      have := hp h
      rw [Fin.ext_iff] at this
      simp at this
    have := Aux_SS103.edge_lap (p i.castSucc) (p i.succ) (wt i) hne x
    rw [← this]
    ring
  have htel : x u - x v = ∑ i, d i := by
    let g : ℕ → ℝ := fun j => x (p ⟨min j k, by omega⟩)
    have h1 : ∀ i : Fin k, d i = g i - g (i + 1) := by
      intro i
      simp only [hd, g]
      have e1 : (i.castSucc : Fin (k + 1)) = ⟨min (i : ℕ) k, by omega⟩ := by
        ext; simp <;> omega
      have e2 : (i.succ : Fin (k + 1)) = ⟨min ((i : ℕ) + 1) k, by omega⟩ := by
        ext; simp <;> omega
      rw [e1, e2]
    rw [Finset.sum_congr rfl (fun i _ => h1 i)]
    rw [Fin.sum_univ_eq_sum_range (fun j => g j - g (j + 1)), Finset.sum_range_sub']
    have e0 : ∀ h, (⟨min 0 k, h⟩ : Fin (k + 1)) = 0 := fun h => by ext; simp
    have ek : ∀ h, (⟨min k k, h⟩ : Fin (k + 1)) = Fin.last k := fun h => by ext; simp
    simp only [g, e0, ek]
    rw [hu, hv]
  rw [hL, hR, htel]
  have hSpos : 0 < S := by
    apply Finset.sum_pos (fun i _ => by have := hwt i; positivity)
    exact ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  have hsed := Finset.sq_sum_div_le_sum_sq_div Finset.univ d
    (g := fun i => 1 / wt i) (fun i _ => by have := hwt i; positivity)
  have hrw : ∑ i, d i ^ 2 / (1 / wt i) = ∑ i, wt i * d i ^ 2 := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [div_div_eq_mul_div, div_one]; ring
  rw [hrw, ← hS, div_le_iff₀ hSpos] at hsed
  linarith
