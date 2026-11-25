-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_isFlagPair_comp_bfd63f823db0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:45:59.970807+00:00
-- url     : https://prove2.me/submissions/ec7bc9c3-0236-4894-93d4-2c94bca76f78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialQuotDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealCorresp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDimStrictDrop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVerticalDivisorsCommute
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairCocycle
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isVerticalDivisor_mul_6491c5235776
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_repr_chain_b243eed5817a

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
  [Field Ω] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω]
  {N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {ϖ : O} {y : (Σ k, ι k) → Ω} [(pointIdeal O y).IsPrime]
    {B B' B'' : ChartBundle O (segreVec y) N E} {w w' w'' : Module.Basis (Fin N) Ω E}
    {x x' x'' : Fin N → K → ℤ} {f g f' g' : Fin N → MRing ι O}
    (hp₁ : IsFlagPair ϖ y B B' w w' x x' f g) (hp₂ : IsFlagPair ϖ y B' B'' w' w'' x' x'' f' g') :
    IsFlagPair ϖ y B B'' w w'' x x'' (fun i => f i * f' i) (fun i => g i * g' i) where
  flag := hp₁.flag
  flag' := hp₂.flag'
  sameFlag := by
    intro i j hij
    rw [repr_chain w w' (w'' i) j]
    refine Finset.sum_eq_zero fun m _ => ?_
    rcases lt_or_ge i m with h | h
    · rw [hp₂.sameFlag i m h, zero_mul]
    · rw [hp₁.sameFlag m j (lt_of_le_of_lt h hij), mul_zero]
  vertical := fun i => by
    have h := isVerticalDivisor_mul (hp₁.vertical i) (hp₂.vertical i)
    rwa [sub_add_sub_cancel] at h
  generic := fun i => by
    simp only [map_mul]
    rw [hp₁.generic i, hp₂.generic i, repr_chain w w' (w'' i) i, Finset.sum_eq_single i]
    · ring
    · intro m _ hmi
      rcases lt_or_gt_of_ne hmi with h | h
      · rw [hp₁.sameFlag m i h, mul_zero]
      · rw [hp₂.sameFlag i m h, zero_mul]
    · simp
end GroundTheory.Heights₂.Heights.NumbersDVR
