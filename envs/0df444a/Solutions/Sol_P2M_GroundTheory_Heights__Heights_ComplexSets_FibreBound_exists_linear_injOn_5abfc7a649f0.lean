-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_exists_linear_injOn_5abfc7a649f0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:52:06.132628+00:00
-- url     : https://prove2.me/submissions/09a352d4-29a8-4f11-8cc0-90ec53c9a493

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
noncomputable section
variable {n d : ℕ}
open GroundTheory.Heights₂.Heights.ComplexSets.FibreBound
namespace GroundTheory.Heights₂.Heights.ComplexSets.FibreBound
theorem _root_.solution (T : Finset (Fin n → ℂ)) :
    ∃ c : Fin n → ℂ, Set.InjOn (fun x : Fin n → ℂ => ∑ j, c j * x j) T := by
  classical
  let p : (Fin n → ℂ) → (Fin n → ℂ) → Polynomial ℂ := fun x x' =>
    ∑ j : Fin n, Polynomial.monomial (j : ℕ) (x j - x' j)
  have hp : ∀ x x', x ≠ x' → p x x' ≠ 0 := by
    intro x x' hne h
    apply hne
    funext j
    have hc := congrArg (fun q => Polynomial.coeff q (j : ℕ)) h
    simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at hc
    rw [Finset.sum_eq_single j] at hc
    · simpa [sub_eq_zero] using hc
    · intro b _ hb; rw [if_neg]; exact fun h => hb (Fin.ext h)
    · simp
  have hev : ∀ x x' (t : ℂ), (p x x').eval t = ∑ j : Fin n, (x j - x' j) * t ^ (j : ℕ) := by
    intro x x' t
    simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset
    (((T ×ˢ T).filter (fun z => z.1 ≠ z.2)).biUnion (fun z => (p z.1 z.2).roots.toFinset))
  refine ⟨fun j => t ^ (j : ℕ), ?_⟩
  intro x hx x' hx' hxx'
  by_contra hne
  apply ht
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_product]
  refine ⟨(x, x'), ⟨⟨Finset.mem_coe.mp hx, Finset.mem_coe.mp hx'⟩, hne⟩, ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (hp x x' hne), Polynomial.IsRoot, hev]
  have hs : ∑ j : Fin n, (x j - x' j) * t ^ (j : ℕ) =
      (∑ j : Fin n, t ^ (j : ℕ) * x j) - ∑ j : Fin n, t ^ (j : ℕ) * x' j := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [hs]; exact sub_eq_zero.mpr hxx'
end GroundTheory.Heights₂.Heights.ComplexSets.FibreBound
