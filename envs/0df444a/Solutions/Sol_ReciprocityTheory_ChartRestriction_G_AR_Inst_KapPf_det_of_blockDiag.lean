-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf.det_of_blockDiag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:09:23.997662+00:00
-- url     : https://prove2.me/submissions/addd76c6-9fd8-4bfe-ac2b-05a60493955e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_PnormInvStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DetOfBlockDiag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix
open scoped Classical
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
theorem _root_.solution {m α : Type} [Fintype m] [DecidableEq m] [LinearOrder α] (M : Matrix m m ℂ)
    (bk : m → α) (hM : M.BlockTriangular bk) (dg : m → ℂ)
    (hd : ∀ i j, bk i = bk j → M i j = if i = j then dg i else 0) : M.det = ∏ i, dg i := by
  classical
  rw [hM.det]
  have hb : ∀ k, M.toSquareBlock bk k = Matrix.diagonal (fun i : {i // bk i = k} => dg i) := by
    intro k
    ext i j
    simp only [Matrix.toSquareBlock_def, Matrix.of_apply]
    rw [hd i j (i.2.trans j.2.symm), Matrix.diagonal_apply]
    simp [Subtype.ext_iff]
  simp only [hb, Matrix.det_diagonal]
  rw [← Finset.prod_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image bk) (g := bk)
    (fun x _ => Finset.mem_image_of_mem bk (Finset.mem_univ x)) dg]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← Finset.prod_subtype (Finset.univ.filter fun i => bk i = k) (p := fun i => bk i = k)
    (fun i => by simp)]
end ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
