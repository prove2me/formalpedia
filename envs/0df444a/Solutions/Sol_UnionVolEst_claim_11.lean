-- Prove2me | solution 1 for UnionVolEst.claim_11
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:47:50.355087+00:00
-- url     : https://prove2.me/submissions/6acd1ecc-a744-44ff-aa96-b2d9d7d004ae

import Mathlib
import Definitions.Def_UnionVolEst_IsAlmostLinftyClose
import Definitions.Def_UnionVolEst_IsVolumeApprox
import Definitions.Def_UnionVolEst_OracleModel

open MeasureTheory ProbabilityTheory
open scoped NNReal

open UnionVolEst in
theorem solution {n M : ℕ} (hM : 1 ≤ M) (K : Fin M → Set (EuclideanSpace ℝ (Fin n)))
    (hK : ∀ i, MeasurableSet (K i)) (hK0 : ∀ i, volume (K i) ≠ 0)
    (hKfin : ∀ i, volume (K i) ≠ ⊤)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : OracleModel P K (ε / 32) (δ / (4 * M)) (ε / 32) (ε / (32 * M))) :
    P {ω | ∃ i, ¬ IsVolumeApprox (ε / 32) (K i) (m.Vt i ω)} ≤ ENNReal.ofReal (δ / 4) := by
  rw [Set.setOf_exists]
  refine le_trans (measure_iUnion_fintype_le P _) ?_
  refine le_trans (Finset.sum_le_sum (fun i _ => m.vol_guarantee i)) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have e : δ / 4 = (M : ℝ) * (δ / (4 * M)) := by
    field_simp
  rw [e, ENNReal.ofReal_mul (Nat.cast_nonneg M), ENNReal.ofReal_natCast]
