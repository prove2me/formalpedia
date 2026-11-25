-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_algebraMap_mem_chartRing_line_3298f58654f8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:20:25.959417+00:00
-- url     : https://prove2.me/submissions/a5782036-8a2e-4dc5-9d99-1688bdae87cf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u v w
variable (k : Type u) [Field k]
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (p : Polynomial k) :
    algebraMap (Polynomial k) (RatFunc k) p ∈ chartRing k (lineX k) (lineChart0 k) := by
  have hX : (RatFunc.X : RatFunc k) ∈ chartRing k (lineX k) (lineChart0 k) := by
    have := (ratio (S := k) (lineX_ne_zero k 0) 1).2
    unfold lineChart0
    simpa [ratio, lineX] using this
  let φ := IsScalarTower.toAlgHom k (Polynomial k) (RatFunc k)
  have hp : p ∈ Algebra.adjoin k {(Polynomial.X : Polynomial k)} := by
    rw [Polynomial.adjoin_X]; trivial
  have hφ : φ p ∈ (Algebra.adjoin k {(Polynomial.X : Polynomial k)}).map φ := ⟨p, hp, rfl⟩
  rw [AlgHom.map_adjoin, Set.image_singleton] at hφ
  refine Algebra.adjoin_le ?_ hφ
  rw [Set.singleton_subset_iff]
  change algebraMap (Polynomial k) (RatFunc k) Polynomial.X ∈ _
  rw [RatFunc.algebraMap_X]
  exact hX
end GroundTheory.Heights₂.Heights.Kleiman
