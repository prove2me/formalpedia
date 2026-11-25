-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VerticalPointMultiplicityChart_aeval_C_mul_X_e703e1c7feb0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:39:55.032387+00:00
-- url     : https://prove2.me/submissions/99f57232-68cd-4d3a-b717-1802407e7b02

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsVertPointNagata
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PVertPointResidue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PVertPointMultChart

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.VerticalPointMultiplicityChart
namespace GroundTheory.Heights₂.Heights.VerticalPointMultiplicityChart
theorem _root_.solution {T : Type} [Fintype T] {S : Type*} [CommRing S] (r : (Σ _ : Unit, T) → S)
    (f : MRing (fun _ : Unit => T)) (d : ℕ) (hf : IsMultiHomog f (fun _ => d)) :
    eval₂ (Int.castRingHom (Polynomial S)) (fun p => Polynomial.C (r p) * Polynomial.X) f =
      Polynomial.C (eval₂ (Int.castRingHom S) r f) * Polynomial.X ^ d := by
  classical
  rw [eval₂_eq, eval₂_eq, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmd : ∑ i, m ⟨(), i⟩ = d := hf m hm ()
  rw [Finset.prod_subset (Finset.subset_univ m.support) (fun p _ hp => by
      rw [Finsupp.notMem_support_iff.mp hp, pow_zero]),
    Finset.prod_subset (Finset.subset_univ m.support) (fun p _ hp => by
      rw [Finsupp.notMem_support_iff.mp hp, pow_zero])]
  simp_rw [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [Fintype.sum_sigma, Fintype.sum_unique, hmd, map_mul, map_prod]
  simp only [map_pow, eq_intCast, map_intCast]
  ring
end GroundTheory.Heights₂.Heights.VerticalPointMultiplicityChart
