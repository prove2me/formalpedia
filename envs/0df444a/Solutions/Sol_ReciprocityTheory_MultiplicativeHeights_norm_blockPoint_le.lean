-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.norm_blockPoint_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:29:25.715793+00:00
-- url     : https://prove2.me/submissions/a6006c53-3b02-47f5-bba6-841bc357a4ab

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereTorusC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric
open scoped Pointwise
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {B n : ℕ} (z : BlockSphere B n) (p : Fin B × Fin n) :
    ‖blockPoint z p‖ ≤ 1 := by
  have h1 : ‖((z p.1 : UnitSphereC n) : EuclideanSpace ℂ (Fin n))‖ = 1 := norm_eq_of_mem_sphere _
  have h2 := EuclideanSpace.norm_eq ((z p.1 : UnitSphereC n) : EuclideanSpace ℂ (Fin n))
  rw [h1] at h2
  have h3 : ‖WithLp.ofLp ((z p.1 : UnitSphereC n) : EuclideanSpace ℂ (Fin n)) p.2‖ ^ 2 ≤
      ∑ i, ‖WithLp.ofLp ((z p.1 : UnitSphereC n) : EuclideanSpace ℂ (Fin n)) i‖ ^ 2 :=
    Finset.single_le_sum (f := fun i => ‖WithLp.ofLp ((z p.1 : UnitSphereC n) :
      EuclideanSpace ℂ (Fin n)) i‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ _)
  have h4 := Real.sqrt_le_sqrt h3
  rw [← h2, Real.sqrt_sq (norm_nonneg _)] at h4
  exact h4
end ReciprocityTheory.MultiplicativeHeights
