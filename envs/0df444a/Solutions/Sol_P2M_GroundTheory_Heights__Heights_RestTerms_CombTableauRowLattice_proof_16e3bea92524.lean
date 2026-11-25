-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_CombTableauRowLattice_proof_16e3bea92524
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:33:46.331041+00:00
-- url     : https://prove2.me/submissions/0f87b6cf-fc0b-4126-bb72-dbb48d5f9e5a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombTableauRowLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open Finset Comb
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace CombTableauRowLattice
theorem _root_.solution : CombTableauRowLattice.Statement := by
  classical
  intro m lam hlam T hT t i j hij
  have hmem : ∀ p : youngCells lam, p.1.1 = j → (i, p.1.2) ∈ youngCells lam := by
    intro p hp
    have hp' := p.2
    simp only [youngCells, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
      Finset.mem_range] at hp' ⊢
    have h1 : p.1.2 < lam i := by
      rw [hp] at hp'
      exact lt_of_lt_of_le hp'.2 (hlam hij)
    refine ⟨lt_of_lt_of_le h1 ?_, h1⟩
    exact Finset.single_le_sum (fun k _ => Nat.zero_le (lam k)) (Finset.mem_univ i)
  let f : youngCells lam → youngCells lam := fun p =>
    if h : p.1.1 = j then ⟨(i, p.1.2), hmem p h⟩ else p
  have hf : ∀ p : youngCells lam, ∀ h : p.1.1 = j, f p = ⟨(i, p.1.2), hmem p h⟩ := by
    intro p h
    simp only [f, dif_pos h]
  apply Finset.card_le_card_of_injOn f
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp ⊢
    rw [hf p hp.1]
    refine ⟨rfl, lt_of_le_of_lt ?_ hp.2⟩
    have := hT ⟨(i, p.1.2), hmem p hp.1⟩ p (by simpa [hp.1] using hij) le_rfl
    exact_mod_cast this
  · intro p hp q hq hpq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp hq
    rw [hf p hp.1, hf q hq.1] at hpq
    have h2 : p.1.2 = q.1.2 := by
      have := congrArg (fun x : youngCells lam => x.1.2) hpq
      simpa using this
    apply Subtype.ext
    exact Prod.ext (hp.1.trans hq.1.symm) h2
end CombTableauRowLattice
end GroundTheory.Heights₂.Heights.RestTerms
