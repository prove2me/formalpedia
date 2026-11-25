-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_exists_minor_ne_zero_143e4e8206ad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:59:14.132683+00:00
-- url     : https://prove2.me/submissions/f62eabfd-e99e-4f8a-8f35-703201014bcc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagBundleSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagConeTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsIntDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagArith

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution {F : Type} [Field F] {r N : ℕ} (M : Matrix (Fin r) (Fin N) F)
    (hM : LinearIndependent F M.row) :
    ∃ (S : Finset (Fin N)) (hS : S.card = r), (M.submatrix id (S.orderEmbOfFin hS)).det ≠ 0 := by
  classical
  obtain ⟨b, -, -, hsp, hb⟩ := exists_linearIndepOn_extension (K := F) (v := M.col)
    (linearIndepOn_empty F M.col) (Set.empty_subset Set.univ)
  have h1 : Submodule.span F (M.col '' b) = Submodule.span F (Set.range M.col) := by
    refine le_antisymm (Submodule.span_mono (Set.image_subset_range _ _)) (Submodule.span_le.2 ?_)
    rintro _ ⟨i, rfl⟩
    exact hsp ⟨i, Set.mem_univ _, rfl⟩
  have h2 : Module.finrank F (Submodule.span F (M.col '' b)) = Fintype.card b := by
    rw [Set.image_eq_range]
    exact finrank_span_eq_card hb
  rw [h1, ← Matrix.rank_eq_finrank_span_cols, hM.rank_matrix, Fintype.card_fin] at h2
  have hS : b.toFinset.card = r := by rw [Set.toFinset_card]; exact h2.symm
  refine ⟨b.toFinset, hS, ?_⟩
  have hmem : ∀ c, b.toFinset.orderEmbOfFin hS c ∈ b := fun c =>
    Set.mem_toFinset.1 (b.toFinset.orderEmbOfFin_mem hS c)
  have hli : LinearIndependent F (M.submatrix id (b.toFinset.orderEmbOfFin hS)).col :=
    hb.comp (fun c => ⟨_, hmem c⟩) fun c c' h => by
      have h' := congrArg Subtype.val h
      exact (b.toFinset.orderEmbOfFin hS).injective h'
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_cols_iff_isUnit.1 hli)).ne_zero
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
