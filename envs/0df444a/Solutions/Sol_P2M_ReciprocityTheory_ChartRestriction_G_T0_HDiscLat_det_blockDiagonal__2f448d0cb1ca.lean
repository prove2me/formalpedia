-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_T0_HDiscLat_det_blockDiagonal__2f448d0cb1ca
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:21:04.926037+00:00
-- url     : https://prove2.me/submissions/313f66d1-1ab0-4315-9f3f-03e9f9df8615

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.HDiscLat
open Module
namespace ReciprocityTheory.ChartRestriction.G.T0.HDiscLat
theorem _root_.solution {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    {κ : ι → Type*} [∀ c, Fintype (κ c)] [∀ c, DecidableEq (κ c)]
    (M : ∀ c, Matrix (κ c) (κ c) R) :
    (Matrix.blockDiagonal' M).det = ∏ c, (M c).det := by
  classical

  have hblk : ∀ c, (Matrix.toSquareBlock (Matrix.blockDiagonal' M) Sigma.fst c).det =
      (M c).det := by
    intro c
    let e : κ c ≃ {s : (Σ c, κ c) // s.1 = c} :=
      { toFun := fun k => ⟨⟨c, k⟩, rfl⟩
        invFun := fun s => cast (congrArg κ s.2) s.1.2
        left_inv := fun k => rfl
        right_inv := by
          rintro ⟨⟨a, k⟩, rfl⟩
          rfl }
    rw [← Matrix.det_submatrix_equiv_self e]
    congr 1
    ext k k'
    show Matrix.blockDiagonal' M ⟨c, k⟩ ⟨c, k'⟩ = M c k k'
    first
      | exact Matrix.blockDiagonal'_apply_eq M c k k'
      | simp [Matrix.blockDiagonal'_apply]
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  first
    | rw [(Matrix.blockTriangular_blockDiagonal' M).det]
    | rw [Matrix.BlockTriangular.det (Matrix.blockTriangular_blockDiagonal' M)]
  rw [Finset.prod_congr rfl (fun c _ => hblk c)]
  refine Finset.prod_subset (Finset.subset_univ _) ?_
  intro c _ hc
  haveI : IsEmpty (κ c) :=
    ⟨fun k => hc (Finset.mem_image.2 ⟨⟨c, k⟩, Finset.mem_univ _, rfl⟩)⟩
  exact Matrix.det_isEmpty
end ReciprocityTheory.ChartRestriction.G.T0.HDiscLat
