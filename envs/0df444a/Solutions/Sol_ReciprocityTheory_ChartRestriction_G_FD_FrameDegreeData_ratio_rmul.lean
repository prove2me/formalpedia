-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ratio_rmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:51:10.330272+00:00
-- url     : https://prove2.me/submissions/d3d8ff5b-0ed9-4dcf-96ca-7b8b1aaf40d2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_bdiag_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_dmin_rmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
noncomputable section
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
theorem _root_.solution (x : Frame X.Ψ r) (hx : x ∈ X.dom) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (τ : X.Ψ) (k : Fin r) :
    ‖dmin X.Gm (rmul x b) τ k.succ / dmin X.Gm (rmul x b) τ k.castSucc‖ =
      ‖b τ k k‖ ^ 2 * ‖dmin X.Gm x τ k.succ / dmin X.Gm x τ k.castSucc‖ := by
  have hsucc : (∏ j : Fin (k.succ : ℕ), mat b τ (Fin.castLE (Nat.le_of_lt_succ k.succ.isLt) j)
      (Fin.castLE (Nat.le_of_lt_succ k.succ.isLt) j)) =
      (∏ j : Fin (k.castSucc : ℕ), mat b τ (Fin.castLE (Nat.le_of_lt_succ k.castSucc.isLt) j)
        (Fin.castLE (Nat.le_of_lt_succ k.castSucc.isLt) j)) * b τ k k := by
    change (∏ j : Fin ((k : ℕ) + 1), mat b τ (Fin.castLE (Nat.le_of_lt_succ k.succ.isLt) j)
      (Fin.castLE (Nat.le_of_lt_succ k.succ.isLt) j)) = _
    rw [Fin.prod_univ_castSucc]
    rfl
  have hPk : (∏ j : Fin (k.castSucc : ℕ), mat b τ (Fin.castLE (Nat.le_of_lt_succ k.castSucc.isLt) j)
      (Fin.castLE (Nat.le_of_lt_succ k.castSucc.isLt) j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => bdiag_ne X hb τ _
  rw [dmin_rmul X x hb τ k.succ, dmin_rmul X x hb τ k.castSucc, hsucc]
  set Pk := (∏ j : Fin (k.castSucc : ℕ), mat b τ (Fin.castLE (Nat.le_of_lt_succ k.castSucc.isLt) j)
      (Fin.castLE (Nat.le_of_lt_succ k.castSucc.isLt) j))
  have hPn : ‖Pk‖ ≠ 0 := norm_ne_zero_iff.2 hPk
  simp only [norm_div, norm_mul, map_mul, Complex.norm_conj]
  by_cases hd : ‖dmin X.Gm x τ k.castSucc‖ = 0
  · simp [hd]
  · field_simp
end ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
