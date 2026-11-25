-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.mem_multidegree_piece_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:58:26.988667+00:00
-- url     : https://prove2.me/submissions/5a634818-d62a-4768-b06a-95abdc13b112

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqSumMultihomogeneousComponents
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CardPieceIrrelevantIdeal
import Theorems.Thm_P2M_RH_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_mem_mHom_iff_eb27d564b98b5c3f


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {W : Ideal (MRing ι)} {a : K → ℕ} {y : MRing ι ⧸ W} :
    y ∈ mPiece W a ↔ ∃ h, IsMultiHomog h a ∧ Ideal.Quotient.mk W h = y := by
  unfold mPiece
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, (mem_mHom_iff _ _).1 hh, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, (mem_mHom_iff _ _).2 hh, rfl⟩
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
