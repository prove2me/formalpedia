-- Prove2me | solution 1 for QEC.Distillation.Ngu24MultiplicativeCSS.f256SourceInput_complement_separates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:40:33.806345+00:00
-- url     : https://prove2.me/submissions/cf5869a6-1f7d-466b-9ce9-1b937b1e28bc

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureInterpolation
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureInput
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CosetDetectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteAlphabetLocality
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureDistance
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_f256SourceInput_cosetLabel_mem_punctured
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_PlaceNormalizedExtension_trans
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256PuncturedMultiplicationCode_distance_lower
import Theorems.Thm_QEC_Coding_HypergraphProduct_finitePredicateMinimum_le_of


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24MultiplicativeCSS
open Coding Coding.AlgebraicGeometry Coding.AlgebraicGeometry.F256GarciaStichtenoth
open Semantics
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Distillation.Ngu24MultiplicativeCSS
theorem _root_.solution (i : ℕ)
    (S : Finset (f256SourceInput i).PivotComplement)
    (hS : S.card < (f256GarciaStichtenothLength i + 4) / 5 -
      f256MultiplicationLogicalCount i)
    (u v : Fin (f256MultiplicationLogicalCount i) → F256)
    (h k : (f256SourceInput i).H0)
    (hsame : ∀ j, j ∉ S → (f256SourceInput i).shortenedCosetLabel u h j =
      (f256SourceInput i).shortenedCosetLabel v k j) :
    u = v ∧ h = k := by
  classical
  let x : Word F256 (F256MultiplicationRetained i) :=
    (f256SourceInput i).shortenedCosetLabel u h -
    (f256SourceInput i).shortenedCosetLabel v k
  have hx : x ∈ (f256PuncturedMultiplicationCode i).carrier :=
    (f256PuncturedMultiplicationCode i).carrier.sub_mem
      (f256SourceInput_cosetLabel_mem_punctured i u h)
      (f256SourceInput_cosetLabel_mem_punctured i v k)
  have hw : HammingWeight x ≤ S.card := by
    apply Finset.card_le_card
    intro j hj
    have hjx : x j ≠ 0 := (Finset.mem_filter.mp hj).2
    by_contra hjS
    exact hjx (sub_eq_zero.mpr (hsame j hjS))
  have hxzero : x = 0 := by
    by_contra hxzero
    have hd := (f256PuncturedMultiplicationCode_distance_lower i).trans
      (HypergraphProduct.finitePredicateMinimum_le_of (weight := HammingWeight)
        ⟨hx, hxzero⟩)
    have hd' : (f256GarciaStichtenothLength i + 3) / 4 -
        f256MultiplicationLogicalCount i ≤ HammingWeight x := WithTop.coe_le_coe.mp hd
    omega
  have hlabel := sub_eq_zero.mp hxzero
  have huv := (f256SourceInput i).shortenedCosetLabel_eq_implies_logical_eq u v h k hlabel
  refine ⟨huv, ?_⟩
  subst v
  exact (f256SourceInput i).shortenedCosetLabel_injective u hlabel
end QEC.Distillation.Ngu24MultiplicativeCSS
