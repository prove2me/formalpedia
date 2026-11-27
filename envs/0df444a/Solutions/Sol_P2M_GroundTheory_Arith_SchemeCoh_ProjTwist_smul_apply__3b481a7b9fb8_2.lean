-- Prove2me | solution 2 for P2M_GroundTheory_Arith_SchemeCoh_ProjTwist_smul_apply__3b481a7b9fb8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:53:46.245116+00:00
-- url     : https://prove2.me/submissions/c7637f13-4b97-4f49-a531-623578f8872f

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwist

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
universe u
variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
open GroundTheory.Arith.SchemeCoh.ProjTwist
variable {𝒜}
open ProjectiveSpectrum
namespace GroundTheory.Arith.SchemeCoh.ProjTwist
theorem _root_.solution {U : Opens (ProjectiveSpectrum.top 𝒜)} (t : (Proj.structureSheaf 𝒜).obj.obj (op U))
    (f : ∀ x : U, Loc 𝒜 x.1) (x : U) : (t • f) x = (t.1 x).val * f x := rfl
end GroundTheory.Arith.SchemeCoh.ProjTwist
