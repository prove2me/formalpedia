-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_FD_herm_smul_left__eda3d1954a4c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:56:11.361572+00:00
-- url     : https://prove2.me/submissions/314db347-3aeb-4c6b-821b-83953c5d5853

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MmatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscrMulHermitianIntegral

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
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    herm G (c • x) y = c * herm G x y := by
  unfold herm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
end ReciprocityTheory.ChartRestriction.G.FD
