-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.lam_prodQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:38:43.873817+00:00
-- url     : https://prove2.me/submissions/9567f219-fd50-4c15-9eda-40c2d58d6b10

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnOperator
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TruncatedExpSecondEqFull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_lamL_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_lam_monomial
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_colM_glue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open SecondColumnDegree DegreeTruncationOperator
variable {k : Type} [CommRing k] {ι : Type} [Fintype ι] {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution (V : Fin n → (ι →₀ ℕ) → k) (Q : Fin n → MvPolynomial ι k) :
    lam (fun mo => ∏ b, V b (colM mo b)) (prodQ Q) = ∏ b, lam (V b) (Q b) := by
  classical
  have hP : prodQ Q = ∑ g ∈ Fintype.piFinset (fun b => (Q b).support),
      (monomial (glue g) (∏ b, (Q b).coeff (g b)) : MvPolynomial (ι × Fin n) k) := by
    have h1 : ∀ b, colE b (Q b) = ∑ e ∈ (Q b).support,
        (monomial (Finsupp.mapDomain (fun l => (l, b)) e) ((Q b).coeff e) : MvPolynomial (ι × Fin n) k) := by
      intro b
      conv_lhs => rw [(Q b).as_sum]
      rw [map_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      exact MvPolynomial.rename_monomial _ _ _
    unfold prodQ
    simp_rw [h1]
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [glue, MvPolynomial.monomial_sum_index, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [MvPolynomial.C_mul_monomial, mul_one]
  rw [hP, ← lamL_apply, map_sum]
  simp only [lamL_apply, lam_monomial, colM_glue]
  simp only [lam]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.prod_mul_distrib]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
