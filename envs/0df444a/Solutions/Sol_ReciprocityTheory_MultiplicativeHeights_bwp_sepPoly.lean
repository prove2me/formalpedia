-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.bwp_sepPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:08:48.432839+00:00
-- url     : https://prove2.me/submissions/d14a62cf-0ed3-4e7f-a821-cd7b5738a36b

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_BWPolyA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_bwp_sepPoly_fin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Polynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {σ : Type*} [Fintype σ] [DecidableEq σ] (k : ℕ) (G : (σ → ℂ) → ℂ)
    (hG : ∀ y m, ∃ Q : ℂ[X], Q.natDegree ≤ k ∧ ∀ t, G (Function.update y m t) = Q.eval t) :
    ∃ F : MvPolynomial σ ℂ, ∀ y, G y = MvPolynomial.eval y F := by
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  obtain ⟨F, hF⟩ := bwp_sepPoly_fin k (Fintype.card σ) (fun z => G (z ∘ e)) (fun z m => by
    obtain ⟨Q, hQd, hQ⟩ := hG (z ∘ e) (e.symm m)
    refine ⟨Q, hQd, fun t => ?_⟩
    show G ((Function.update z m t) ∘ e) = _
    rw [Function.update_comp_equiv, hQ])
  refine ⟨MvPolynomial.rename e.symm F, fun y => ?_⟩
  rw [MvPolynomial.eval_rename, ← hF]
  congr 1
  ext s
  simp
end ReciprocityTheory.MultiplicativeHeights
