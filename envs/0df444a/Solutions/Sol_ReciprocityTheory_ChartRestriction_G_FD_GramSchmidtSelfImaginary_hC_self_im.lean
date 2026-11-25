-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary.hC_self_im
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:59:57.688344+00:00
-- url     : https://prove2.me/submissions/0b3bf66e-5e19-4846-a12d-008b776baab3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsUnitaryBasisSameFlag
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UMatUpper
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpSpanRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
  (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
variable (hG : ∀ a b, cc (G a b) = G b a)
include hG
namespace ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary
theorem _root_.solution (v : Fin r → ℂ) : (hermC τ G v v).im = 0 := by
  have hτ : ∀ a b, conj (τ (G a b)) = τ (G b a) := by
    intro a b
    rw [← hG a b]
    first
    | exact (NumberField.IsCMField.complexEmbedding_complexConj τ (G a b)).symm
    | exact (IsCMField.complexEmbedding_complexConj τ (G a b)).symm
    | (simp only [cc]; exact (NumberField.IsCMField.complexEmbedding_complexConj τ (G a b)).symm)
    | (simp [cc])
  have hc : conj (hermC τ G v v) = hermC τ G v v := by
    simp only [hermC, map_sum, map_mul, Complex.conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [hτ]
    ring
  exact Complex.conj_eq_iff_im.mp hc
end ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary
