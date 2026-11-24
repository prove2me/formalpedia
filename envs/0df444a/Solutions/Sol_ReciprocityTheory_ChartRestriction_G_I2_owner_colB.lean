-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.owner_colB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:02.675933+00:00
-- url     : https://prove2.me/submissions/ce2e140d-543f-4598-ac3b-6e6a7201cc8b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivDeterminantPolyTensor
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_OwnerNoneIff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_colB_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
noncomputable section
variable {E : Type} [Field E] [NumberField E] {n nb : ℕ}
variable {dim : (E →+* ℂ) → ℕ} (bs : Fin nb → Block E n dim)
variable {bs}
variable (bs)
variable {bs}
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (hD : Disj bs) (p : Σ j : Fin nb, Fin (bs j).i) : owner bs (colB bs p) = some p := by
  have h' : ∃ q, colB bs q = colB bs p := ⟨p, rfl⟩
  rw [owner, dif_pos h']
  exact congrArg some (colB_inj hD h'.choose_spec)
end ReciprocityTheory.ChartRestriction.G.I2
