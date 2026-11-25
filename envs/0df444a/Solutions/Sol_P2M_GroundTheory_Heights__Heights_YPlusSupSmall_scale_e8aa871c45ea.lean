-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_YPlusSupSmall_scale_e8aa871c45ea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:25:21.175588+00:00
-- url     : https://prove2.me/submissions/4749f00a-9398-4163-b4c3-8fa1ceab9cc8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PYPlusSupSmall
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_YPlusSupSmall_exps_7871b70a62a4

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
open GroundTheory.Heights₂.Heights.YPlusSupSmall
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n} (D : AddBlockData P)
namespace GroundTheory.Heights₂.Heights.YPlusSupSmall
theorem _root_.solution {R : Type*} [CommRing R] {τ : ℕ} {f : MvPolynomial (Coord D.extSizes) ℤ}
    (hf : Geo.IsMultiHomog (ι := blockIdx D.extSizes) f (Pi.single none τ)) (u w : Coord D.extSizes → R)
    (α β : R) (huw : ∀ j : Fin (D.size + 1), α * u ⟨none, j⟩ = β * w ⟨none, j⟩) :
    α ^ τ * aeval u f = β ^ τ * aeval w f := by
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  obtain ⟨h0, hτ⟩ := exps D hf hm
  have key : ∀ (v : Coord D.extSizes → R) (γ : R),
      γ ^ τ * ∏ p, v p ^ m p = ∏ j, (γ * v ⟨none, j⟩) ^ m ⟨none, j⟩ := by
    intro v γ
    rw [Fintype.prod_sigma, Fintype.prod_option]
    simp only [h0, pow_zero, Finset.prod_const_one, mul_one]
    rw [← hτ, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    simp only [mul_pow]
  rw [mul_left_comm (α ^ τ), mul_left_comm (β ^ τ), key u α, key w β]
  exact congrArg _ (Finset.prod_congr rfl fun j _ ↦ congrArg (· ^ m ⟨none, j⟩) (huw j))
end GroundTheory.Heights₂.Heights.YPlusSupSmall
