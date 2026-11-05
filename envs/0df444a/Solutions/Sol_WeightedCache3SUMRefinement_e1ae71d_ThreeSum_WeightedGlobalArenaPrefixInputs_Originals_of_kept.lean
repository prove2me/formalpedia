-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixInputs.Originals.of_kept
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:55:28.118556+00:00
-- url     : https://prove2.me/submissions/54e164a3-f15d-403a-ab73-3913dd364093

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSeedData
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaOriginalInputs
import Theorems.Thm_ThreeSum_LightBalancedOffset_offset_lt
import Theorems.Thm_ThreeSum_TernarySignedLayout_offset_lt
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaLayout_offset_lt


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixInputs
open Light WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSeedData TernaryExtensionEncoding
variable {p : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixInputs
namespace Originals
theorem _root_.solution {I : Input} {A : Inputs} {seedCount featureBound tagBound positionCap : ℕ}
    {ℓ : E→ₗ[ZMod p] ZMod p} {seeds : ℕ→E×E} {L R O : ℕ→ℕ→ℤ} {μ ν : ℕ→ℤ}
    (H : Originals I A seedCount featureBound tagBound positionCap ℓ seeds L R O μ)
    (hk : Kept μ ν I.free) : Originals I A seedCount featureBound tagBound positionCap ℓ seeds L R O ν := by
  have cell_lt {base count i k : ℕ} (hend : base+count*(A.J+2)≤I.free)
      (hi : i<count) (hki : k<A.J+2) : base+i*(A.J+2)+k<I.free := by nlinarith
  exact { H with
    BRead:=fun i hi k hki => (hk _ (cell_lt H.BEnd hi hki)).trans (H.BRead i hi k hki)
    CRead:=fun i hi k hki => (hk _ (cell_lt H.CEnd hi hki)).trans (H.CRead i hi k hki)
    ORead:=fun i hi k hki => (hk _ (cell_lt H.OEnd hi hki)).trans (H.ORead i hi k hki)
    menuRead:=fun ordinal ho k hki => (hk _ (cell_lt H.menuEnd ho hki)).trans (H.menuRead ordinal ho k hki)
    positionRead:=fun i hi => (hk _ (by have hh:=H.positionEnd;omega)).trans (H.positionRead i hi)
    leftRead:=fun i hi t ht => (hk _ (cell_lt H.leftEnd hi (TernarySignedLayout.offset_lt ht))).trans (H.leftRead i hi t ht)
    rightRead:=fun i hi t ht => (hk _ (cell_lt H.rightEnd hi (TernarySignedLayout.offset_lt ht))).trans (H.rightRead i hi t ht) }
end Originals
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixInputs
