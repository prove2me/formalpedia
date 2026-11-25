-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitConjSum_restrict_eq_iff_7898508957a0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:45:52.461751+00:00
-- url     : https://prove2.me/submissions/0afc1bcd-4768-40e6-b778-bc81723fddbf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitConjSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitConjSumLemmas

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
open GroundTheory.Heights₂.Heights.OrbitConjSum
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.OrbitConjSum
theorem _root_.solution (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (σ σ' : coordField x →+* ℂ) :
    σ.comp (algebraMap (ratioField x c) (coordField x)) =
        σ'.comp (algebraMap (ratioField x c) (coordField x)) ↔
      ∀ p, σ (ratio x c p) = σ' (ratio x c p) := by
  constructor
  · intro h p
    exact DFunLike.congr_fun h ⟨ratio x c p, IntermediateField.subset_adjoin ℚ _ ⟨p, rfl⟩⟩
  · intro h
    have e : (σ.comp (algebraMap (ratioField x c) (coordField x))).toRatAlgHom =
        (σ'.comp (algebraMap (ratioField x c) (coordField x))).toRatAlgHom :=
      IntermediateField.adjoin_algHom_ext ℚ fun y ⟨p, hp⟩ ↦ by
        subst hp
        exact h p
    ext a
    exact DFunLike.congr_fun e a
end GroundTheory.Heights₂.Heights.OrbitConjSum
