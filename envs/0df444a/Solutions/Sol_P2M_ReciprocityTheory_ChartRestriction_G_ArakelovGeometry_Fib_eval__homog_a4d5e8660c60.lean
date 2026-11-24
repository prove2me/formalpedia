-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_eval__homog_a4d5e8660c60
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:40.272642+00:00
-- url     : https://prove2.me/submissions/7505a991-1705-4753-8d9d-862d5e525999

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsSmoothPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
theorem _root_.solution {ι S : Type*} [Fintype ι] [DecidableEq ι] [Field S] (v : ι → S) (i₀ : ι)
    (hv : v i₀ ≠ 0) {N : ℕ} (G : MvPolynomial ι ℤ) (hN : G.totalDegree ≤ N) :
    eval₂ (Int.castRingHom S) v (homog i₀ N G) = v i₀ ^ N * deh v i₀ G := by
  rw [homog, eval₂_sum, deh, coe_eval₂Hom, eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmN : m.degree ≤ N := le_trans (le_totalDegree hm) hN
  rw [eval₂_monomial, Finsupp.prod_add_index' (by simp) (by intros; rw [pow_add]),
    Finsupp.prod_single_index (by simp)]
  have h1 : (m.prod fun i k => v i ^ k) = ∏ i, v i ^ m i :=
    Finsupp.prod_fintype _ _ (by simp)
  have h2 : ∏ i, (v i / v i₀) ^ m i = (∏ i, v i ^ m i) / v i₀ ^ m.degree := by
    rw [Finset.prod_congr rfl fun i _ => div_pow (v i) (v i₀) (m i), Finset.prod_div_distrib,
      Finset.prod_pow_eq_pow_sum, Finsupp.degree_eq_sum]
  rw [h1, h2]
  have h3 : v i₀ ^ N = v i₀ ^ (N - m.degree) * v i₀ ^ m.degree := by
    rw [← pow_add]; congr 1; omega
  rw [h3]
  field_simp
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
