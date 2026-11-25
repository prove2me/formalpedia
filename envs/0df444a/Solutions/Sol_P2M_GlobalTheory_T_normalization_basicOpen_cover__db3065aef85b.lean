-- Prove2me | solution 1 for P2M_GlobalTheory_T_normalization_basicOpen_cover__db3065aef85b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:32:35.192005+00:00
-- url     : https://prove2.me/submissions/213d0265-1fc9-4443-b1ac-652925eda368

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormalizationBasicOpenCover
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormalizationBasicOpenCoverStatement
import Theorems.Thm_GlobalTheory_normalization_basicOpen_cover


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (U X : Scheme.{0}) (f : U ⟶ X), ∀ [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [LocallyQuasiFinite f] (V : X.AffineZariskiSite), ∃ G : Finset (f.normalizationDiagram.obj (Opposite.op V.1)), (∀ b ∈ G, letI := (f.normalizationDiagramMap.app (Opposite.op V.1)).hom.toAlgebra; Algebra.FiniteType Γ(X, V.1) (Localization.Away b)) ∧ ∀ x : U, f x ∈ V.1 → ∃ b ∈ G, f.toNormalization x ∈ f.normalizationOpenCover.f V '' (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum (f.normalizationDiagram.obj (Opposite.op V.1)))) := by
  first | exact @GlobalTheory.normalization_basicOpen_cover | exact GlobalTheory.normalization_basicOpen_cover | (intros; apply GlobalTheory.normalization_basicOpen_cover <;> assumption)
end _root_.GlobalTheory.T
