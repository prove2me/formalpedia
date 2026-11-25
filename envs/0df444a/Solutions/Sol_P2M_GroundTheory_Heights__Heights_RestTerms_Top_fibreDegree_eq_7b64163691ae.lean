-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_fibreDegree_eq_7b64163691ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:54:19.945608+00:00
-- url     : https://prove2.me/submissions/d573e976-85bd-46b1-b26a-1ce42915a308

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_BlockValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSameFactorFormula
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_isHomogeneous_mu_pow_fib_0c2c6eb9bcfd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_multinomial_const_2190c1ab2280
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockCoeff_rect_eq_7d9159b82c6d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_dividedDifference_eq_of_hasDD_5f38fe8d41e9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_gmfOut_zero_9add85c2d281
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_gmf_13295714a17c


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
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Top
theorem _root_.solution (hF : FrobeniusCharacterFormula.Statement) (hCI : CharacterAtIdentity.Statement)
    (hV : VandermondeOfHomogeneous.Statement) (f r a : ℕ) (c : SmallBlock) (hr : 1 ≤ r)
    (ha : 1 ≤ a) (κ : ℚ)
    (hκ : ∀ lam : Fin r → ℕ, Antitone lam →
        HasDD 1 (r + a) (yEval r a c (schur (Fin r) lam) * fib1 r a c) (pushOut r a c κ lam))
    (c0 : ℚ)
    (hInt : ∀ H : RootRing f (r + a), H.IsHomogeneous (topDegree f (r + a)) →
      algebraMap ℚ (FractionRing (RootRing f (r + a))) (flagIntegral f (r + a) H) =
        algebraMap ℚ (FractionRing (RootRing f (r + a))) c0 * dividedDifference f (r + a) H) :
    fibreDegree f r a c =
      c0 * κ ^ f * (f * (r * a)).factorial / ((r * a).factorial : ℚ) ^ f *
        (numStandardTable (rectangle r a) : ℚ) ^ f := by
  have hra : r * a ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have hH : gmf f r a c 0 (f * (r * a)) =
      smallBlockMu f r a c ^ (f * (r * a)) * fibreClass f r a c := by
    simp [gmf, extraFactor]
  have hdd := dividedDifference_eq_of_hasDD (hasDD_gmf hF f r a c κ hκ 0 (f * (r * a)))
  rw [hH, gmfOut_zero] at hdd
  have h := hInt _ (isHomogeneous_mu_pow_fib hV f r a c)
  rw [hdd, ← MvPolynomial.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply ℚ (RootRing f (r + a)) (FractionRing (RootRing f (r + a))),
    ← map_mul] at h
  have h2 := (algebraMap ℚ (FractionRing (RootRing f (r + a)))).injective h
  rw [fibreDegree, h2, multinomial_const, blockCoeff_rect_eq hCI r a hra]
  have hx : ((r * a).factorial : ℚ) ^ f ≠ 0 := pow_ne_zero _ (by exact_mod_cast Nat.factorial_ne_zero _)
  field_simp
  ring
end GroundTheory.Heights₂.Heights.RestTerms.Top
