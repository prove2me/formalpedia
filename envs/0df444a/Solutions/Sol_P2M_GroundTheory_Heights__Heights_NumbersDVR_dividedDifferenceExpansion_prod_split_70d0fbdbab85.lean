-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_prod_split_70d0fbdbab85
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:42:00.30834+00:00
-- url     : https://prove2.me/submissions/7482b843-4b83-4def-9abd-9f8aba53e180

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinDivDiffExpansion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR.dividedDifferenceExpansion
namespace GroundTheory.Heights₂.Heights.NumbersDVR.dividedDifferenceExpansion
theorem _root_.solution {M : Type*} [CommMonoid M] {r : ℕ} (l : Fin r) (f : Fin r → M) :
    ∏ j, f j = (∏ j ∈ Finset.univ.filter (fun j => j < l), f j) * f l *
      ∏ j ∈ Finset.univ.filter (fun j => l < j), f j := by
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun j => j < l),
    ← Finset.prod_filter_mul_prod_filter_not (Finset.univ.filter fun j => ¬ j < l) (fun j => j = l),
    Finset.filter_filter, Finset.filter_filter, mul_assoc]
  congr 2
  · rw [Finset.prod_eq_single l]
    · intro b hb hbl
      simp only [Finset.mem_filter] at hb
      exact absurd hb.2.2 hbl
    · intro h
      exact absurd (by simp) h
  · congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      exact lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)
    · intro h
      exact ⟨not_lt.mpr h.le, ne_of_gt h⟩
end GroundTheory.Heights₂.Heights.NumbersDVR.dividedDifferenceExpansion
