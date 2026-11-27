-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.sum_smul_bG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:48:01.559336+00:00
-- url     : https://prove2.me/submissions/5b0c5c58-40c5-42e7-8c45-46b3d2493065

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussAbsMulSupportFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsIntMultiple
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K]
namespace ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
theorem _root_.solution {κ : Type} (G : MvPolynomial κ K) (S : Finset (κ →₀ ℕ)) {T : Finset (κ →₀ ℕ)}
    {r : ℕ} (e : T ≃ Fin r) (p : Fin S.card → K) :
    ∑ j, p j • bG G S e j = coordVec e (G * polyOf S p) := by
  funext i
  simp only [bG, coordVec, polyOf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show MvPolynomial.monomial (mS S j) (p j) =
      MvPolynomial.C (p j) * MvPolynomial.monomial (mS S j) 1 by
    rw [MvPolynomial.C_mul_monomial, mul_one]]
  rw [mul_left_comm G, MvPolynomial.coeff_C_mul]
end ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
