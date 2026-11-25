-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Hypotheses__FreeQuot_IsFppfTorsor_existsUnique_smul_0af5c6c57843
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:05:12.078894+00:00
-- url     : https://prove2.me/submissions/90778dd0-5aeb-425a-9ef6-c14a4b299c6c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RingHomFlatCodescendsAlongFaithfullyFlat
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5

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
theorem _root_.solution (h : IsFppfTorsor G q) {T : Over S} (x y : T ⟶ X) (e : y ≫ q = x ≫ q) :
    ∃! g : T ⟶ G, g • x = y := by
  have h2 : h.1.lift y x e ≫ snd G X = x := h.1.lift_snd _ _ _
  refine ⟨h.1.lift y x e ≫ fst G X, ?_, fun g hg => ?_⟩
  · have : lift (h.1.lift y x e ≫ fst G X) x = h.1.lift y x e := by
      ext
      · simp
      · simp [h2]
    beta_reduce
    rw [Hom.smul_def, this, h.1.lift_fst]
  · have : lift g x = h.1.lift y x e := by
      apply h.1.hom_ext
      · rw [h.1.lift_fst]; exact hg
      · rw [h.1.lift_snd, lift_snd]
    rw [← this, lift_fst]
end IsFppfTorsor
end GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
