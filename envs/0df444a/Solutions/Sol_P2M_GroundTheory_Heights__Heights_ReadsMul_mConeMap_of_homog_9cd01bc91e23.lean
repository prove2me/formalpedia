-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ReadsMul_mConeMap_of_homog_9cd01bc91e23
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:48:23.691684+00:00
-- url     : https://prove2.me/submissions/0c2cefa5-dafc-4898-a5da-3e864e594eed

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PReadsMul
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexAt_algebraMap_apply_de37bb391a59


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.ReadsMul
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.ReadsMul
theorem _root_.solution {Ω : Type} [Field Ω] (y : Coord n → Ω) {g : MvPolynomial (Coord n) ℤ}
    {d : ι → ℕ} (hg : IsWeightedHomogeneous (coordDeg n) g d) :
    Geo.mConeMap (ι := blockIdx n) y g = C (aeval y g) * ∏ k, (X k : MvPolynomial ι Ω) ^ d k := by
  have hg' := (geoMultiHomog_iff g d).mpr hg
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hX : ∏ p : Coord n, (X p.1 : MvPolynomial ι Ω) ^ m p = ∏ k, (X k : MvPolynomial ι Ω) ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (X k : MvPolynomial ι Ω) ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hg' m hm k]
  simp only [Geo.mConeMap, aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun i => by simp), Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, hX, map_mul, map_prod, map_pow,
    MvPolynomial.algebraMap_apply]
  ring
end GroundTheory.Heights₂.Heights.ReadsMul
