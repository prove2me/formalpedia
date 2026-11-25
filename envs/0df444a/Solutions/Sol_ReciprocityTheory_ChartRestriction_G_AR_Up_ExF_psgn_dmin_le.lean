-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.psgn_dmin_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:30:38.605082+00:00
-- url     : https://prove2.me/submissions/b3bf0b3b-b2f3-49de-9367-1924198e97c2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_pos_re_of_posDef
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_psgn_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
theorem _root_.solution {x : Frame X.Ψ r} (τ : X.Ψ) (hA : (X.gramPos x τ).PosDef) (i : Fin (r + 1))
    (hip : (i : ℕ) ≤ X.p0) : 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := by
  rw [psgn_eq_one hip, one_mul]
  have hsub : ((X.gramPos x τ).submatrix (Fin.castLE hip) (Fin.castLE hip)).PosDef :=
    hA.submatrix (Fin.castLE_injective hip)
  have heq : dmin X.Gm x τ i =
      ((X.gramPos x τ).submatrix (Fin.castLE hip) (Fin.castLE hip)).det := by
    unfold dmin lminor Data.gramPos
    rw [Matrix.submatrix_submatrix]
    rfl
  rw [heq]
  exact OrthonormalChartBounds.pos_re_of_posDef hsub
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
