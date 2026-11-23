-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.tr_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:37:14.451545+00:00
-- url     : https://prove2.me/submissions/bd47fc09-232f-4ed0-94de-b3a1b06521e1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tr_def
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_res_pullU_eq


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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped Classical
variable {X Y : Scheme.{0}} (L : LB X)
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (hL : L.IsLB) {V : Y.Opens} {ψ : Y ⟶ X} {a b c : L.ι}
    (h : V ≤ ψ ⁻¹ᵁ (L.U a ⊓ L.U b ⊓ L.U c)) :
    tr L V ψ a b * tr L V ψ b c = tr L V ψ a c := by
  have hab : V ≤ ψ ⁻¹ᵁ (L.U a ⊓ L.U b) := fun y hy => (h hy).1
  have hbc : V ≤ ψ ⁻¹ᵁ (L.U b ⊓ L.U c) := fun y hy => ⟨(h hy).1.2, (h hy).2⟩
  have hac : V ≤ ψ ⁻¹ᵁ (L.U a ⊓ L.U c) := fun y hy => ⟨(h hy).1.1, (h hy).2⟩
  rw [tr_def L hab, tr_def L hbc, tr_def L hac]
  have c1 := hL.cocycle a b c
  rw [res_pullU_eq ψ (inf_le_left : L.U a ⊓ L.U b ⊓ L.U c ≤ L.U a ⊓ L.U b) hab h,
    res_pullU_eq ψ (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      L.U a ⊓ L.U b ⊓ L.U c ≤ L.U b ⊓ L.U c) hbc h,
    res_pullU_eq ψ (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      L.U a ⊓ L.U b ⊓ L.U c ≤ L.U a ⊓ L.U c) hac h, ← map_mul, ← map_mul, c1]
end ReciprocityTheory.ChartRestriction.G.DVR
