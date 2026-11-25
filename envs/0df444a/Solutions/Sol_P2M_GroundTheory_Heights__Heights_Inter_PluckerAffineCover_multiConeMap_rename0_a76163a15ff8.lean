-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_multiConeMap_rename0_a76163a15ff8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:08:10.6303+00:00
-- url     : https://prove2.me/submissions/a02625eb-4ed7-42b3-a79f-00c2505b1200

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
theorem _root_.solution {Φ : Type} [Field Φ] (c : (Σ k, S.WIdx k) → Φ) (s : MRing S.YIdx) :
    T.multiConeMap c (rename (T.yyEmb 0) s) = rename blk0 (T.multiConeMap (c ∘ T.yyEmb 0) s) := by
  have h : (T.multiConeMap c).comp (rename (T.yyEmb 0) : MRing S.YIdx →ₐ[ℤ] MRing S.WIdx).toRingHom =
      (rename blk0 : MvPolynomial T.YBlk Φ →ₐ[Φ] MvPolynomial T.WBlk Φ).toRingHom.comp
        (T.multiConeMap (c ∘ T.yyEmb 0)) := by
    apply MvPolynomial.ringHom_ext
    · intro n; simp [T.multiConeMap]
    · rintro ⟨b, j⟩
      cases b <;> simp [T.multiConeMap, T.yyEmb, blk0]
  exact RingHom.congr_fun h s
end GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
