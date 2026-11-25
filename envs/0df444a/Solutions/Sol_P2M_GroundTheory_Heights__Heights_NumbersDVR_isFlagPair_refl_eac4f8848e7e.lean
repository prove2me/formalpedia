-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_isFlagPair_refl_eac4f8848e7e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:42:29.91787+00:00
-- url     : https://prove2.me/submissions/803b5baf-a64d-4ae0-81e0-dd04bce689e5

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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isVerticalDivisor_one_177da7b5f629


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
omit [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {ϖ : O} {y : (Σ k, ι k) → Ω} [(pointIdeal O y).IsPrime]
    {B : ChartBundle O (segreVec y) N E} {w : Module.Basis (Fin N) Ω E} {x : Fin N → K → ℤ}
    (hf : IsFlagFrame y B w x) :
    IsFlagPair ϖ y B B w w x x (fun _ => 1) (fun _ => 1) where
  flag := hf
  flag' := hf
  sameFlag := by
    intro i j hij
    simp [Module.Basis.repr_self, hij.ne]
  vertical := fun i => by
    rw [sub_self]
    exact isVerticalDivisor_one ϖ _
  generic := fun i => by simp [Module.Basis.repr_self]
end GroundTheory.Heights₂.Heights.NumbersDVR
