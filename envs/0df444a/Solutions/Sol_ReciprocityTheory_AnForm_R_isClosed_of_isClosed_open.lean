-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.isClosed_of_isClosed_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:46:26.136624+00:00
-- url     : https://prove2.me/submissions/019afbcf-75d1-44db-8282-017c9ad65699

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SecHomSurjective
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BijOnClosedPointsOfIsIso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory MvPolynomial
noncomputable section
variable {W X : Scheme.{0}} {sW : W ⟶ Spec (.of ℂ)} {sX : X ⟶ Spec (.of ℂ)}
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution [LocallyOfFiniteType sW] (V : W.Opens) (x : V)
    (hx : IsClosed ({x} : Set V)) : IsClosed ({x.1} : Set W) := by
  have : JacobsonSpace W := LocallyOfFiniteType.jacobsonSpace sW
  apply isClosed_singleton_of_isLocallyClosed_singleton
  obtain ⟨t, ht, hteq⟩ := isClosed_induced_iff.mp hx
  refine ⟨(V : Set W), t, V.isOpen, ht, ?_⟩
  ext z
  constructor
  · rintro rfl
    exact ⟨x.2, (Set.ext_iff.mp hteq x).mpr rfl⟩
  · rintro ⟨hzV, hzt⟩
    have e : (⟨z, hzV⟩ : V) = x := (Set.ext_iff.mp hteq ⟨z, hzV⟩).mp hzt
    show z = x.1
    exact congrArg Subtype.val e
end ReciprocityTheory.AnForm.R
