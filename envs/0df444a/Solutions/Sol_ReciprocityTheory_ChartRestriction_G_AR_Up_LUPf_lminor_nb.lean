-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.lminor_nb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:45.782801+00:00
-- url     : https://prove2.me/submissions/d6f03dc1-4a9e-4478-8da8-20e5bcd8331e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DetSubUpper
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
open Matrix ReciprocityTheory.ChartRestriction.G.FD
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
theorem _root_.solution (N B : Matrix (Fin n) (Fin n) ℂ) (hup : ∀ i k : Fin n, i < k → N i k = 0)
    (hd : ∀ i, N i i = 1) (hB : B.BlockTriangular id) (k : Fin (n + 1)) :
    lminor (N * B) k = ∏ j : Fin k, B (Fin.castLE (Nat.le_of_lt_succ k.isLt) j)
      (Fin.castLE (Nat.le_of_lt_succ k.isLt) j) := by
  set e : Fin k → Fin n := Fin.castLE (Nat.le_of_lt_succ k.isLt) with he
  have hmono : ∀ a b : Fin k, a < b → e a < e b := fun a b h => h
  have hsub : (N * B).submatrix e e = N.submatrix e e * B.submatrix e e := by
    ext a b
    simp only [submatrix_apply, mul_apply]
    symm
    refine Fintype.sum_of_injective e (Fin.castLE_injective _) _ _ (fun c hc => ?_) (fun _ => rfl)
    have hc' : (k : ℕ) ≤ c := by
      by_contra hlt
      exact hc ⟨⟨c, by omega⟩, Fin.ext rfl⟩
    have hac : e a < c := by
      rw [Fin.lt_iff_val_lt_val]
      show (a : ℕ) < c
      omega
    rw [hup _ _ hac, zero_mul]
  have hNt : (N.submatrix e e).BlockTriangular OrderDual.toDual :=
    fun a b h => hup _ _ (hmono _ _ (OrderDual.toDual_lt_toDual.mp h))
  have hBt : (B.submatrix e e).BlockTriangular id := fun a b h => hB (hmono _ _ h)
  rw [lminor, ← he, hsub, det_mul, Matrix.det_of_lowerTriangular _ hNt,
    Matrix.det_of_upperTriangular hBt]
  simp [hd]
end ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
