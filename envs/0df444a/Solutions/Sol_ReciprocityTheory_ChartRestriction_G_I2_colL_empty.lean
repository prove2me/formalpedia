-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.colL_empty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:30:09.7648+00:00
-- url     : https://prove2.me/submissions/16e73f25-32e0-48b9-b8eb-0a71095e4b29

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivDeterminantPolyTensor
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_OwnerNoneIff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_owner_none_iff

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
variable (X : PT E) {bs : Fin nb → Block E n X.dim}
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (hD : Disj bs) (T : Choice bs) {k : Fin n} (hk : owner bs k = none) :
    colL (lst X bs T) k = [] := by
  rw [owner_none_iff hD] at hk
  unfold colL
  rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro x hx
  unfold lst at hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  obtain ⟨t, -, rfl⟩ := Multiset.mem_map.1 (Multiset.mem_toList.1 hl)
  intro h
  exact hk ⟨t.1, t.2.2⟩ (of_decide_eq_true h)
end ReciprocityTheory.ChartRestriction.G.I2
