-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RootPointConjugation_aeval_mul_monomial_c5929ecdffff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:14:17.952184+00:00
-- url     : https://prove2.me/submissions/ae195d1b-01cf-41d1-8d26-41b2e713f238

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeightNE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootPointConj

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.RootPointConjugation
namespace GroundTheory.Heights₂.Heights.RootPointConjugation
theorem _root_.solution {σ A : Type*} [CommRing A] (s : A) (x : σ → A) (μ : σ →₀ ℕ) (c : ℤ) :
    aeval (fun i => s * x i) (monomial μ c) = s ^ (μ.sum fun _ e => e) * aeval x (monomial μ c) := by
  simp only [aeval_monomial, Finsupp.prod, Finsupp.sum, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  ring
end GroundTheory.Heights₂.Heights.RootPointConjugation
