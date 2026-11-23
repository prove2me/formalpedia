-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.kUnit_eig_real
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:31:20.809937+00:00
-- url     : https://prove2.me/submissions/28bb8c6e-a2de-484a-afc5-45e700f959da

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_Lemmata_SimultaneousEigenvectors_BlSimeig
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hU : IsKUnitary ε A) {c : Fin n} {w : X} (hw0 : w ≠ 0) {z : ℂ}
    (hw : A c c w = z • w) : z = ((z.re : ℝ) : ℂ) := by
  have h := hU c c rfl w w
  rw [hw, inner_smul_left, inner_smul_right] at h
  have hne : inner ℂ w w ≠ (0 : ℂ) := inner_self_ne_zero.mpr hw0
  have h2 : (starRingEnd ℂ) z = z := mul_right_cancel₀ hne h
  exact (Complex.conj_eq_iff_re.mp h2).symm
end ReciprocityTheory.ChartRestriction.DS
