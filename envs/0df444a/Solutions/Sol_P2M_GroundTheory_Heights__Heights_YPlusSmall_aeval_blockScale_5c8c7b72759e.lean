-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_YPlusSmall_aeval_blockScale_5c8c7b72759e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:50.668825+00:00
-- url     : https://prove2.me/submissions/f8bf6aad-29e7-4acc-9dcb-f16a754cc132

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PYPlusSmall

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.YPlusSmall
namespace GroundTheory.Heights₂.Heights.YPlusSmall
theorem _root_.solution {κ : Type} [Fintype κ] {n' : κ → ℕ} {A : Type*} [CommRing A]
    {f : MvPolynomial (Coord n') ℤ} {e : κ → ℕ} (hf : Geo.IsMultiHomog (ι := blockIdx n') f e)
    (c : κ → A) (v : Coord n' → A) :
    aeval (fun p ↦ c p.1 * v p) f = (∏ k, c k ^ e k) * aeval v f := by
  simp only [aeval_def, eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have h1 : ∏ p, (c p.1 * v p) ^ m p = (∏ p, c p.1 ^ m p) * ∏ p, v p ^ m p := by
    rw [← Finset.prod_mul_distrib]
    simp_rw [mul_pow]
  have h2 : ∏ p : Coord n', c p.1 ^ m p = ∏ k, c k ^ e k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    show ∏ i, c k ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hf m hm k]
  rw [h1, h2]
  ring
end GroundTheory.Heights₂.Heights.YPlusSmall
