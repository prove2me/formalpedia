-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitConjSum_aeval_chartHomog_4ac03b3e97ec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:45:31.387644+00:00
-- url     : https://prove2.me/submissions/05800340-810f-4f9d-b183-c7d8d7a60110

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitConjSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitConjSumLemmas
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitConjSum_blockDeg_le_9e02025f8eb2

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
open GroundTheory.Heights₂.Heights.OrbitConjSum
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.OrbitConjSum
theorem _root_.solution {F : Type*} [Field F] (c : (k : ι) → Fin (n k + 1))
    (P : MvPolynomial (Coord n) ℤ) (w : Coord n → F) (hw : ∀ k, w ⟨k, c k⟩ ≠ 0) :
    aeval w (chartHomog c P) =
      (∏ k, w ⟨k, c k⟩ ^ P.totalDegree) * aeval (fun p ↦ w p / w ⟨p.1, c p.1⟩) P := by
  have hP : aeval (fun p ↦ w p / w ⟨p.1, c p.1⟩) P =
      ∑ m ∈ P.support, aeval (fun p ↦ w p / w ⟨p.1, c p.1⟩) (monomial m (P.coeff m)) := by
    conv_lhs => rw [P.as_sum]
    exact map_sum _ _ _
  rw [hP, chartHomog, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hden : ∏ p : Coord n, w ⟨p.1, c p.1⟩ ^ m p = ∏ k, w ⟨k, c k⟩ ^ ∑ i, m ⟨k, i⟩ := by
    rw [Fintype.prod_sigma]
    exact Finset.prod_congr rfl fun k _ ↦ by
      show ∏ i, w ⟨k, c k⟩ ^ m ⟨k, i⟩ = _
      exact Finset.prod_pow_eq_pow_sum _ _ _
  have hE : ∏ k, w ⟨k, c k⟩ ^ P.totalDegree = (∏ k, w ⟨k, c k⟩ ^ ∑ i, m ⟨k, i⟩) *
      ∏ k, w ⟨k, c k⟩ ^ (P.totalDegree - ∑ i, m ⟨k, i⟩) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ ↦ by
      rw [← pow_add, Nat.add_sub_cancel' (blockDeg_le P hm k)]
  have h0 : ∏ k, w ⟨k, c k⟩ ^ ∑ i, m ⟨k, i⟩ ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hw k)
  simp only [map_mul, aeval_monomial, chartMonomial, map_prod, map_pow, aeval_X]
  rw [Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
  simp only [div_pow, Finset.prod_div_distrib, hden]
  field_simp
  rw [hE]
  ring
end GroundTheory.Heights₂.Heights.OrbitConjSum
