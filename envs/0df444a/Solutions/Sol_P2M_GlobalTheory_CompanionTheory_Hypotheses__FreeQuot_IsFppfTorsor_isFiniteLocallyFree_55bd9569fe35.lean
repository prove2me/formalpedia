-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Hypotheses__FreeQuot_IsFppfTorsor_isFiniteLocallyFree_55bd9569fe35
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:38:14.161224+00:00
-- url     : https://prove2.me/submissions/a8489845-8098-4364-a8a6-3dda33671f05

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RingHomFlatCodescendsAlongFaithfullyFlat
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__FreeQuot_IsFppfTorsor_of_descendsAlong_b40a1a97fbb5
import Theorems.Thm_GlobalTheory_flat_descendsAlong_fpqc
import Theorems.Thm_GlobalTheory_isAffineHom_descendsAlong_fpqc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hypotheses₂
open FreeQuot
open GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
universe u
variable {S : Scheme.{u}} {G X Y : Over S} [GrpObj G] [ModObj G X] {q : X ⟶ Y}
set_option backward.isDefEq.respectTransparency.types false
namespace GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
namespace IsFppfTorsor
theorem _root_.solution {S : Scheme.{0}} {G X Y : Over S} [GrpObj G] [ModObj G X] {q : X ⟶ Y}
    (h : IsFppfTorsor G q) (hG : IsFiniteLocallyFree G.hom) : IsFiniteLocallyFree q.left := by
  obtain ⟨h1, h2, h3⟩ := hG
  have := isAffineHom_descendsAlong_fpqc.{0}
  have := flat_descendsAlong_fpqc
  have a2 : IsAffineHom q.left := h.of_descendsAlong @IsAffineHom (inferInstanceAs (IsAffineHom G.hom))
  have a3 : UniversallyClosed q.left :=
    h.of_descendsAlong @UniversallyClosed (inferInstanceAs (UniversallyClosed G.hom))
  have a4 : LocallyOfFinitePresentation q.left := h.of_descendsAlong @LocallyOfFinitePresentation h3
  exact ⟨(IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr
    ⟨IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨a3, a2⟩, inferInstance⟩,
    h.of_descendsAlong @Flat h2, a4⟩
end IsFppfTorsor
end GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
