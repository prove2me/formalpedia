-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.sec_compat_rs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:26.801145+00:00
-- url     : https://prove2.me/submissions/dfcbe8a3-10d7-4552-9ab2-9ae609d11c74

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_linComb_g_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_rs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_units
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_mul

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
variable {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (s : LB.Sec (LB.LinComb L φ ε)) (j j₂ : K → L.ι) {V : Y.Opens}
    (h : V ≤ LB.wchart L φ j ⊓ LB.wchart L φ j₂) :
    rs (h.trans inf_le_left) (s.f j) =
      ((∏ k, tr L V (φ k) (j k) (j₂ k) ^ ε k : Γ(Y, V)ˣ) : Γ(Y, V)) * rs (h.trans inf_le_right) (s.f j₂) := by
  have h' : V ≤ (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j₂ := h
  have e : rs h' (rs (inf_le_left : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j₂ ≤ _) (s.f j)) =
      rs h' ((((LB.LinComb L φ ε).g j j₂ : Γ(Y, (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j₂)ˣ) :
        Γ(Y, (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j₂)) *
        rs (inf_le_right : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j₂ ≤ _) (s.f j₂)) :=
    congrArg (rs h') (s.compat j j₂)
  rw [rs_rs, rs_mul, rs_rs, rs_units] at e
  erw [linComb_g_res L φ ε j j₂ h] at e
  exact e
end ReciprocityTheory.ChartRestriction.G.DVR
