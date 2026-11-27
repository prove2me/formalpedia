-- Prove2me | solution 1 for P2M_GlobalTheory_existsUnique_factor_completedStalk__0c9a727c5acc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:53:08.781196+00:00
-- url     : https://prove2.me/submissions/67059d60-17cd-40d4-ba54-2ca5a5aa07b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Theorems.Thm_GlobalTheory_existsUnique_factor_completedStalk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry IsLocalRing
universe u
open GlobalTheory
variable {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
omit [IsLocalRing R]
namespace GlobalTheory
theorem _root_.solution (I : Ideal R) [IsAdicComplete I R]
    {f : Spec (.of R) ⟶ X} {x : X}
    {φ : X.presheaf.stalk x ⟶ .of R} (hφ : Spec.map φ ≫ X.fromSpecStalk x = f)
    (hfg : (maximalIdeal (X.presheaf.stalk x)).FG)
    (hk : ∃ k : ℕ, (maximalIdeal (X.presheaf.stalk x)).map φ.hom ^ k ≤ I) :
    ∃! g, g ≫ fromSpecCompletedStalk X x = f := by
  obtain ⟨ψ, hψ, hu⟩ := existsUnique_factor_completedStalk I hφ hfg hk
  refine ⟨_, hψ, fun g hg => ?_⟩
  obtain ⟨χ, rfl⟩ := Spec.map_surjective g
  rw [← hu χ.hom hg]
  rfl
end GlobalTheory
