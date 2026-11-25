-- Prove2me | solution 1 for P2M_GroundTheory_Arith_SchemeCoh_ProjSpace_away__toSpecBase_03f8e91fffce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:12:06.108329+00:00
-- url     : https://prove2.me/submissions/86a96a43-1b71-4e1f-90c7-13949f3ae2a5

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveSpaceChart
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_TwistingSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ProjBaseChange

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
open AlgebraicGeometry CategoryTheory Limits MvPolynomial HomogeneousLocalization
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section
open GroundTheory.Arith.SchemeCoh.ProjSpace
variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (n : ℕ)
variable {A B n}
variable (A)
namespace GroundTheory.Arith.SchemeCoh.ProjSpace
theorem _root_.solution {s : MvPolynomial (Fin (n + 1)) A} {d : ℕ} (hs : s ∈ grading A n d)
    (hd : 0 < d) :
    Proj.awayι (grading A n) s hs hd ≫ toSpecBase A n =
      Spec.map (CommRingCat.ofHom (chartAlgebraMap A s)) := by
  rw [toSpecBase, ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl
end GroundTheory.Arith.SchemeCoh.ProjSpace
