-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GridProductLowerBound_exists_grid_prod_ne_zero_e9513834daea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:32:09.68488+00:00
-- url     : https://prove2.me/submissions/b985e712-df5f-4da7-8a32-da4d8500ab65

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGridProductLowerBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGridProductLowerBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology MvPolynomial
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace GridProductLowerBound
theorem _root_.solution {σ : Type} [Fintype σ] {N k : ℕ} (hk : k ≤ N)
    (v : Fin k → σ → ℂ) (hv : ∀ m, v m ≠ 0) :
    ∃ u : σ → Fin (N + 1), ∏ m, ∑ i, ((u i : ℕ) : ℂ) * v m i ≠ 0 := by
  classical
  set P : MvPolynomial σ ℂ := ∏ m, ∑ i, X i * C (v m i) with hP
  have hlin : ∀ m, ∑ i, X i * C (v m i) ≠ (0 : MvPolynomial σ ℂ) := by
    intro m h
    obtain ⟨i, hi⟩ := Function.ne_iff.1 (hv m)
    have := congrArg (eval (Pi.single i 1)) h
    simp [Pi.single_apply] at this
    exact hi this
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun m _ => hlin m
  let S : σ → Finset ℂ := fun _ => Finset.univ.image fun j : Fin (N + 1) => ((j : ℕ) : ℂ)
  have hS : ∀ i, (S i).card = N + 1 := fun i => by
    simp only [S]
    rw [Finset.card_image_of_injective _ fun a b h => Fin.ext (by exact_mod_cast h)]
    simp
  have htot : P.totalDegree ≤ k := by
    refine (totalDegree_finsetProd _ _).trans ?_
    calc ∑ m, (∑ i, X i * C (v m i) : MvPolynomial σ ℂ).totalDegree ≤ ∑ _m : Fin k, 1 :=
          Finset.sum_le_sum fun m _ => totalDegree_finsetSum_le fun j _ =>
            (totalDegree_mul _ _).trans (by simp [totalDegree_X, totalDegree_C])
      _ = k := by simp
  have hdeg : ∀ i, P.degreeOf i < (S i).card := fun i => by
    rw [hS i]
    exact Nat.lt_succ_of_le (((degreeOf_le_totalDegree _ _).trans htot).trans hk)
  by_contra hne
  push Not at hne
  refine hP0 (eq_zero_of_eval_zero_at_prod_finset P S hdeg fun x hx => ?_)
  choose u _ hu using fun i => Finset.mem_image.1 (hx i)
  have := hne u
  simp only [hu] at this
  simpa [hP, map_prod] using this
end GridProductLowerBound
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
