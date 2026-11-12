-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P24.compatibility_implies_positive_difference
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T00:11:30.43621+00:00
-- url     : https://prove2.me/submissions/658dc49c-9630-4781-a0ef-ec8127a50920

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P24

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder Matrix.Norms.L2Operator

open MeasureTheory

open QAlgorithms.Papers.Independent.Dependency50.P49 (traceDual)

open QAlgorithms.Papers.Independent.Information100.P30 (IsPositiveMap)

open QAlgorithms.Papers.Independent.Intake100.P24 in
theorem solution
    (Phi : PolarizationMatrix →ₗ[ℂ] PolarizationMatrix) (V : PolarizationMatrix)
    (hPhi : IsDoublyContracting Phi) (hV : (1 - V * Vᴴ).PosSemidef)
    (hcompatible : ∀ (S : PolarizationMatrix) (alpha : JonesVector),
      S.PosSemidef → (S - jonesOuter alpha).PosSemidef →
        (Phi S - V * jonesOuter alpha * Vᴴ).PosSemidef) :
    IsPositiveMap (Phi - jonesConjugation V) := by
  intro X hX
  obtain ⟨m, v, hXv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.1 hX
  have hJ : ∀ i, jonesOuter (v i) = Matrix.vecMulVec (v i) (star (v i)) := fun i => rfl
  have hpos : ∀ i, (Phi (jonesOuter (v i)) - V * jonesOuter (v i) * Vᴴ).PosSemidef := by
    intro i
    refine hcompatible _ (v i) ?_ ?_
    · rw [hJ]
      exact Matrix.posSemidef_vecMulVec_self_star _
    · rw [sub_self]
      exact Matrix.PosSemidef.zero
  have heq : (Phi - jonesConjugation V) X =
      ∑ i, (Phi (jonesOuter (v i)) - V * jonesOuter (v i) * Vᴴ) := by
    rw [LinearMap.sub_apply, hXv, map_sum, map_sum, ← Finset.sum_sub_distrib]
    rfl
  rw [heq]
  exact Matrix.posSemidef_sum _ (fun i _ => hpos i)

end
