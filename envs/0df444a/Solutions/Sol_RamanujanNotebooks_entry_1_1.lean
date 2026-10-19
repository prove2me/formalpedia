-- Prove2me | solution 1 for RamanujanNotebooks.entry_1_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T14:27:40.857033+00:00
-- url     : https://prove2.me/submissions/9b5efca8-a8c8-4050-8cdf-4fe84e395df9

import Mathlib
import Definitions.Def_RamanujanNotebooks_ch01_ch1AntiDiagSum
import Definitions.Def_RamanujanNotebooks_ch01_ch1DiagSum
import Definitions.Def_RamanujanNotebooks_ch01_ch1IsMagic
import Definitions.Def_RamanujanNotebooks_ch01_ch1IsSemiMagic

namespace RNE1

lemma bij_sum {n : ℕ} (a : Fin n → ℕ) (f : Fin n → Fin n) (hf : Function.Bijective f) :
    ∑ i : Fin n, a (f i) = ∑ k : Fin n, a k :=
  (Equiv.ofBijective f hf).sum_comp a

end RNE1

open RamanujanNotebooks in
theorem solution (n : ℕ) (hn : 0 < n) (a p : Fin n → ℕ) (σ τ : Fin n → Fin n → Fin n)
    (hσrow : ∀ i : Fin n, Function.Bijective (fun j : Fin n => σ i j))
    (hσcol : ∀ j : Fin n, Function.Bijective (fun i : Fin n => σ i j))
    (hσdiag : Function.Bijective (fun i : Fin n => σ i i))
    (hσanti : Function.Bijective (fun i : Fin n => σ i (Fin.rev i)))
    (hτrow : ∀ i : Fin n, Function.Bijective (fun j : Fin n => τ i j))
    (hτcol : ∀ j : Fin n, Function.Bijective (fun i : Fin n => τ i j))
    (hτdiag : Function.Bijective (fun i : Fin n => τ i i))
    (hτanti : Function.Bijective (fun i : Fin n => τ i (Fin.rev i)))
    (hpair : Function.Bijective (fun x : Fin n × Fin n => (σ x.1 x.2, τ x.1 x.2))) :
    ch1IsMagic (fun i j : Fin n => a (σ i j) + p (τ i j))
      ((∑ k : Fin n, a k) + (∑ k : Fin n, p k)) := by
  refine ⟨⟨fun i => ?_, fun j => ?_⟩, ?_, ?_⟩
  · simp only [Finset.sum_add_distrib]
    rw [RNE1.bij_sum a _ (hσrow i), RNE1.bij_sum p _ (hτrow i)]
  · simp only [Finset.sum_add_distrib]
    rw [RNE1.bij_sum a _ (hσcol j), RNE1.bij_sum p _ (hτcol j)]
  · simp only [ch1DiagSum, Finset.sum_add_distrib]
    rw [RNE1.bij_sum a _ hσdiag, RNE1.bij_sum p _ hτdiag]
  · simp only [ch1AntiDiagSum, Finset.sum_add_distrib]
    rw [RNE1.bij_sum a _ hσanti, RNE1.bij_sum p _ hτanti]
