-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Hypotheses__FreeQuot_IsFppfTorsor_isFppfQuotient_3e882fd20688
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:29:53.173376+00:00
-- url     : https://prove2.me/submissions/8a0e284a-d4cf-4bd1-819b-ff07f8849885

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RingHomFlatCodescendsAlongFaithfullyFlat
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__FreeQuot_IsFppfTorsor_existsUnique_smul_0af5c6c57843

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
namespace GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
namespace IsFppfTorsor
theorem _root_.solution (h : IsFppfTorsor G q) : IsFppfQuotient G q := by
  refine ⟨h.1.w, ?_, ?_⟩
  · refine Presheaf.isLocallyInjective_of_injective _ _ ?_
    rintro T ⟨x⟩ ⟨y⟩ e
    obtain ⟨g, hg, -⟩ := h.existsUnique_smul y x e
    exact Quotient.sound ⟨g, hg⟩
  · obtain ⟨hp, J, U, f, hf, hs, hl⟩ := h
    refine ⟨fun {T} y => ?_⟩
    have hc : Presieve.ofArrows U f ∈ Scheme.fppfPrecoverage Y.left :=
      (Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨hs, hf⟩
    have := Scheme.fppfTopology.pullback_stable y.left (Precoverage.generate_mem_toGrothendieck hc)
    rw [GrothendieckTopology.mem_over_iff]
    refine Scheme.fppfTopology.superset_covering ?_ this
    rintro V a ⟨W, b, c, ⟨i⟩, e⟩
    obtain ⟨s, hs⟩ := hl i
    rw [Sieve.overEquiv_iff]
    have e' : (b ≫ s) ≫ q.left = a ≫ y.left := by rw [Category.assoc, hs, e]
    refine ⟨Quotient.mk _ (Over.homMk (b ≫ s) ?_), ?_⟩
    · rw [← Over.w q, ← Category.assoc, e', Category.assoc, Over.w y]; rfl
    · exact Over.OverMorphism.ext e'
end IsFppfTorsor
end GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
