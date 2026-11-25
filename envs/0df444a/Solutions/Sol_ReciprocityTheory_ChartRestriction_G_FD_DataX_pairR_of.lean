-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.DataX.pairR_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:01:27.174326+00:00
-- url     : https://prove2.me/submissions/07462440-6c2c-4f83-9310-6d6f4789a5b7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MmatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscrMulHermitianIntegral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_DataX_tau_c0E

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Module Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.DataX
variable {r : ℕ} (X : DataX E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.DataX
theorem _root_.solution (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) (w : Fin 2 → Fin 2 → E) :
    X.pairR χ (X.embH (Matrix.of fun i k => X.c0E * w i k)) =
      (((X.g * dEnat E : ℕ) : ℝ) / 2) *
        (∑ τ : X.Ψ, ∑ i, ∑ k, χ τ i k * τ.1 (w i k)).re := by
  unfold Data.pairR Data.embH
  simp only [Matrix.of_apply, map_mul, tau_c0E]
  rw [← Complex.re_ofReal_mul]
  congr 1
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring
end ReciprocityTheory.ChartRestriction.G.FD.DataX
