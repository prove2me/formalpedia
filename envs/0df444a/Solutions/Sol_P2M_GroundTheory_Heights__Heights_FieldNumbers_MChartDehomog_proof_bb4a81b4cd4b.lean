-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartDehomog_proof_bb4a81b4cd4b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:29:42.547918+00:00
-- url     : https://prove2.me/submissions/5ea0b690-990d-4d6d-81a6-c4ee60cdef66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMChartDehomog
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_prod_pow_blockWeight_69a38f0cbb39

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace MChartDehomog
theorem _root_.solution : MChartDehomog.Statement := by
  intro F _ K _ _ ι P _ u hu f b hf
  set L := FractionRing (MRing ι F ⧸ P)
  let φ : MRing ι F →+* L := (algebraMap (MRing ι F ⧸ P) L).comp (Ideal.Quotient.mk P)
  let w : K → L := fun k => φ (X ⟨k, u k⟩)
  have hw : ∀ k, w k ≠ 0 := fun k => by
    simp only [w, φ, RingHom.comp_apply, ne_eq, IsFractionRing.to_map_eq_zero_iff,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hu k
  have hD : φ (chartMonomial u b) = ∏ k, w k ^ b k := by
    simp [chartMonomial, w, map_prod, map_pow]
  have hC : ∀ c : F, φ (C c) = algebraMap F L c := fun c => by
    simp only [φ, RingHom.comp_apply]
    rw [← MvPolynomial.algebraMap_eq, ← Ideal.Quotient.mkₐ_eq_mk F, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply]
  have hmono : ∀ e ∈ f.support, chartMap P u (monomial e (coeff e f)) * ∏ k, w k ^ b k =
      φ (monomial e (coeff e f)) := by
    intro e he
    have hwe : Finsupp.weight (blockWeight ι) e = b := hf (mem_support_iff.mp he)
    rw [← hwe, prod_pow_blockWeight, chartMap, aeval_monomial, mul_assoc, ← Finsupp.prod_mul,
      monomial_eq, map_mul, hC, Finsupp.prod, Finsupp.prod, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun v _ => ?_
    change (φ (X v) / w v.1) ^ e v * w v.1 ^ e v = φ (X v ^ e v)
    rw [← mul_pow, div_mul_cancel₀ _ (hw v.1), map_pow]
  change chartMap P u f = φ f / φ (chartMonomial u b)
  rw [hD, eq_div_iff (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hw k))]
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl hmono
end MChartDehomog
end GroundTheory.Heights₂.Heights.FieldNumbers
