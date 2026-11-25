-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_aeval_of_mem_ker_c4e20c757a43
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:30:36.089544+00:00
-- url     : https://prove2.me/submissions/df2892a6-3cba-46ee-8e2d-a1a9f137c68f

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
variable {D : ℕ} (S : ProjectiveLineBundle D)
namespace GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
theorem _root_.solution {K : Type} {ι : K → Type} {Φ : Type} [Field Φ] (c : (Σ k, ι k) → Φ) {p : MRing ι}
    (hp : p ∈ RingHom.ker (T.multiConeMap c)) : aeval c p = 0 := by
  have h : (MvPolynomial.eval (fun _ => (1 : Φ))).comp (T.multiConeMap c) = (aeval c).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro n; simp [T.multiConeMap]
    · intro q; simp [T.multiConeMap]
  have := RingHom.congr_fun h p
  rw [RingHom.comp_apply, RingHom.mem_ker.1 hp, map_zero] at this
  exact this.symm
end GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
