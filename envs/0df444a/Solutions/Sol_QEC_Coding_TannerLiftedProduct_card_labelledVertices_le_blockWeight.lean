-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.card_labelledVertices_le_blockWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:18:29.321049+00:00
-- url     : https://prove2.me/submissions/0097ec09-154e-4a25-9cb8-5056285e0fb1

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGlobalExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_d_mul_card_nonactiveLabelledVertices_le_four_mul_faceSupport

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcCycle : LiftedProduct.boundary1 (data label h g') c = 0)
    (d m : Nat)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hFour : 4 ≤ d) :
    (labelledVertices label c m).card ≤ blockWeight c := by
  have hDouble :=
    d_mul_card_nonactiveLabelledVertices_le_four_mul_faceSupport
      label h g' c hcCycle d m hDistance
  have hFourNonactive :
      4 * (nonactiveLabelledVertices label c m).card ≤
        d * (nonactiveLabelledVertices label c m).card :=
    Nat.mul_le_mul_right (nonactiveLabelledVertices label c m).card hFour
  have hNonactive :
      (nonactiveLabelledVertices label c m).card ≤ (faceSupport c).card := by
    omega
  have hCover : labelledVertices label c m ⊆
      nonactiveLabelledVertices label c m ∪ vertexBlockSupport c := by
    intro v hv
    by_cases hvActive : v ∈ vertexBlockSupport c
    · exact Finset.mem_union_right _ hvActive
    · exact Finset.mem_union_left _
        (Finset.mem_sdiff.mpr ⟨hv, hvActive⟩)
  unfold blockWeight
  calc
    (labelledVertices label c m).card ≤
        (nonactiveLabelledVertices label c m ∪
          vertexBlockSupport c).card := Finset.card_le_card hCover
    _ ≤ (nonactiveLabelledVertices label c m).card +
        (vertexBlockSupport c).card := Finset.card_union_le _ _
    _ ≤ (faceSupport c).card + (vertexBlockSupport c).card :=
      Nat.add_le_add_right hNonactive _
end QEC.Coding.TannerLiftedProduct
