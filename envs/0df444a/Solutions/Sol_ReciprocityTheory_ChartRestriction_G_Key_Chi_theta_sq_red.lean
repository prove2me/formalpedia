-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.theta_sq_red
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:01:38.116269+00:00
-- url     : https://prove2.me/submissions/19e4caf3-ed5b-4d15-80e2-c4cae6e3c2b7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_eC_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_ofRealVec_halfVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_ofIntVec_dot
import Theorems.Thm_ReciprocityTheory_PTheta_eC_int
import Theorems.Thm_ReciprocityTheory_PTheta_thetaIntChar_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
namespace ReciprocityTheory.ChartRestriction.G.Key.Chi
theorem _root_.solution {g : ℕ} (k k' : Fin g → ℤ) (z : Fin g → ℂ) (τ : Matrix (Fin g) (Fin g) ℂ) :
    theta (halfVec k) (halfVec k') z τ ^ 2 =
      theta (halfVec fun i => k i % 2) (halfVec fun i => k' i % 2) z τ ^ 2 := by
  have hsplit : ∀ m : Fin g → ℤ,
      halfVec m = halfVec (fun i => m i % 2) + fun i => ((m i / 2 : ℤ) : ℝ) := by
    intro m
    funext i
    have h0 : m i % 2 + 2 * (m i / 2) = m i := by omega
    have h : ((m i % 2 + 2 * (m i / 2) : ℤ) : ℝ) = (m i : ℝ) := by
      rw [h0]
    push_cast at h
    simp only [halfVec, Pi.add_apply]
    linarith
  have hE : ∀ a b : Fin g → ℤ, eC (ofRealVec (halfVec a) ⬝ᵥ ofIntVec b) ^ 2 = 1 := by
    intro a b
    rw [eC_pow, ofRealVec_halfVec, smul_dotProduct, ofIntVec_dot, smul_eq_mul]
    convert eC_int (a ⬝ᵥ b) using 2
    push_cast
    ring
  rw [hsplit k, hsplit k',
    thetaIntChar_holds (Fin g) _ _ (fun i => k i / 2) (fun i => k' i / 2), mul_pow, hE, one_mul]
end ReciprocityTheory.ChartRestriction.G.Key.Chi
