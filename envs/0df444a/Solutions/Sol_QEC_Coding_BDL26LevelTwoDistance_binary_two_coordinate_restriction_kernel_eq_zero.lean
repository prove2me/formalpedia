-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoDistance.binary_two_coordinate_restriction_kernel_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:27:59.972202+00:00
-- url     : https://prove2.me/submissions/b982e683-2584-4455-8824-1d0c44b0c4b2

import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXSeedSmallSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AlternatingCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDistance
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_binary_two_coordinate_kernel_eq_zero
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

section
namespace QEC.Coding.BDL26LevelTwoDistance
open scoped BigOperators
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps BDL26LevelTwoCode
open BDL26DecodingGraph
private theorem coordinatePreimageOr_of_eq {Q I : Type} (embed : I → Q)
    (hinj : Function.Injective embed) (fallback i : I) (q : Q) (h : embed i = q) :
    i = coordinatePreimageOr embed fallback q := by
  classical
  have hex : ∃ j, embed j = q := ⟨i, h⟩
  rw [coordinatePreimageOr, dif_pos hex]
  exact hinj (h.trans (Classical.choose_spec hex).symm)
end QEC.Coding.BDL26LevelTwoDistance
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoDistance
open scoped BigOperators
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps BDL26LevelTwoCode
attribute [local instance] QEC.Coding.BDL26LevelTwoDistance.rzQDecidableEq
open BDL26DecodingGraph
namespace QEC.Coding.BDL26LevelTwoDistance
theorem _root_.solution
    {Q I Z : Type} [Fintype Q] [DecidableEq Q] [Fintype I] [DecidableEq I]
    [Fintype Z] [DecidableEq Z]
    (embed : I → Q) (hinj : Function.Injective embed)
    (syndrome : Word Field I →ₗ[Field] Word Field Z)
    (hnonzero : ∀ i, syndrome (canonicalBasisWord i) ≠ 0)
    (hdistinct : Function.Injective (fun i => syndrome (canonicalBasisWord i)))
    (word : Word Field Q)
    (hzero : syndrome (fun i => word (embed i)) = 0) (a b : Q)
    (hsupport : ∀ q, word q ≠ 0 → q = a ∨ q = b) :
    (fun i => word (embed i)) = 0 := by
  classical
  by_contra hlocal
  have hex : ∃ i, word (embed i) ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hlocal (funext hn)
  obtain ⟨fallback, _⟩ := hex
  apply hlocal
  apply binary_two_coordinate_kernel_eq_zero syndrome hnonzero hdistinct _ hzero
    (coordinatePreimageOr embed fallback a) (coordinatePreimageOr embed fallback b)
  intro i hi
  rcases hsupport (embed i) hi with ha | hb
  · exact Or.inl (coordinatePreimageOr_of_eq embed hinj fallback i a ha)
  · exact Or.inr (coordinatePreimageOr_of_eq embed hinj fallback i b hb)
end QEC.Coding.BDL26LevelTwoDistance
