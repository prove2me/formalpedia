-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.sumBdIsUpq_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:44:47.747383+00:00
-- url     : https://prove2.me/submissions/31725a80-be3c-4f1f-89de-a20b1d93fc0a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBdJf_mul_Jf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open Matrix Topology Filter
open scoped Matrix ComplexOrder ENNReal
noncomputable section
variable {p q : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
theorem _root_.solution {M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq M) :
    M * Jf p q * Mᴴ = Jf p q := by
  have h1 : (Jf p q * Mᴴ * Jf p q) * M = 1 := by
    have := h; simp only [IsUpq, Matrix.mul_assoc] at this ⊢; rw [this, sumBdJf_mul_Jf]
  have h2 : M * (Jf p q * Mᴴ * Jf p q) = 1 := mul_eq_one_comm.mp h1
  calc M * Jf p q * Mᴴ = M * (Jf p q * Mᴴ * Jf p q) * Jf p q := by
        simp only [Matrix.mul_assoc, sumBdJf_mul_Jf, Matrix.mul_one]
    _ = Jf p q := by rw [h2, Matrix.one_mul]
end ReciprocityTheory.ChartRestriction.G.AR.Up
