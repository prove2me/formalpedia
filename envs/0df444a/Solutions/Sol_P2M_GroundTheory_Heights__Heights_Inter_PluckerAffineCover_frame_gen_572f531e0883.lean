-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_frame_gen_572f531e0883
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:42.815651+00:00
-- url     : https://prove2.me/submissions/be000e50-4a5b-4c8e-9c7d-84cdaa29f5cc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
variable {Ω : Type} [Field Ω] {ι : Type} (x : ι → Ω) (i : ι)
variable {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ}
namespace GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
theorem _root_.solution (B : ChartBundle ℤ x r E) {f : Ω} (bb : Fin r → E)
    (hloc : ∀ e, (∃ n : ℕ, f ^ n • e ∈ B.lat i) ↔
      ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f ^ n * a q ∈ chartRing ℤ x i) ∧ e = ∑ q, a q • bb q) (q : Fin r) :
    ∃ n : ℕ, f ^ n • bb q ∈ B.lat i := by
  classical
  refine (hloc _).2 ⟨Pi.single q 1, fun q' => ⟨0, ?_⟩, ?_⟩
  · rcases eq_or_ne q' q with rfl | h
    · simp
    · simp [h]
  · simp [Pi.single_apply]
end GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
