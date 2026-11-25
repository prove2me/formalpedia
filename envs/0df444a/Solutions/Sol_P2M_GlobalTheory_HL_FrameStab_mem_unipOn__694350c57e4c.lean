-- Prove2me | solution 1 for P2M_GlobalTheory_HL_FrameStab_mem_unipOn__694350c57e4c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:24:11.312048+00:00
-- url     : https://prove2.me/submissions/1a56c0e6-a0e6-4134-92e8-6dbca7e8c3a0

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameStab
open GlobalTheory.HL.Eichler GlobalTheory.HL.FrameOnto
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.FrameStab
theorem _root_.solution [IsArtinianRing E] {n : ℕ} {A B : Submodule E (Fin n → E)} (hBA : B ≤ A)
    (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (h1 : ∀ v ∈ A, g v - v ∈ B) : g ∈ unipOn A B := by
  have h2 : ∀ v ∈ A, g v ∈ A := fun v hv => by simpa using A.add_mem (hBA (h1 _ hv)) hv
  refine ⟨fun v => ⟨fun hv => ?_, h2 v⟩, h1⟩
  have hs := IsArtinian.surjective_of_injective_endomorphism (g.toLinearMap.restrict h2)
    (fun a b hab => Subtype.ext (g.injective (congrArg Subtype.val hab)))
  obtain ⟨a, ha⟩ := hs ⟨g v, hv⟩
  have : (a : Fin n → E) = v := g.injective (congrArg Subtype.val ha)
  exact this ▸ a.2
end GlobalTheory.HL.FrameStab
