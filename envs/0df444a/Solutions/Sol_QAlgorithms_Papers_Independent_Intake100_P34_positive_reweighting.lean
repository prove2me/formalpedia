-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P34.positive_reweighting
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T02:15:43.347096+00:00
-- url     : https://prove2.me/submissions/ade2b852-c8ca-4376-a566-c0e9782ff244

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P34

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator ComplexOrder

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms (IsDensityMatrix)

open QAlgorithms.Papers.Independent.Information100.P26 (Mat commutant scalars)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap IsPositiveMap)

local notation "GeneratorMap" => fun d : ℕ => MatrixMap (Fin d) (Fin d)

open QAlgorithms.Papers.Independent.Intake100.P34 in
theorem solution {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (Phi : Fin n → GeneratorMap d) (weights : Fin n → ℝ)
    (hPositive : ∀ j, IsPositiveMap (Phi j)) (hWeights : ∀ j, 0 < weights j)
    (hIrreducible : DaviesIrreducible (∑ j, Phi j)) :
    DaviesIrreducible (∑ j, (weights j : ℂ) • Phi j) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨j0, hj0⟩ := Finite.exists_min weights
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = weights j0 := ⟨_, rfl⟩
  have hμpos : 0 < μ := by rw [hμ]; exact hWeights j0
  have hμle : ∀ j, μ ≤ weights j := fun j => by rw [hμ]; exact hj0 j
  constructor
  · intro X hX
    rw [LinearMap.sum_apply]
    apply Matrix.posSemidef_sum
    intro j _
    rw [LinearMap.smul_apply]
    exact (hPositive j X hX).smul (Complex.zero_le_real.mpr (hWeights j).le)
  · intro P hPP hPH c hc hpsd
    have hPpsd : P.PosSemidef := by
      have h := Matrix.posSemidef_conjTranspose_mul_self P
      rwa [hPH, hPP] at h
    apply hIrreducible.2 P hPP hPH (c / μ) (div_pos hc hμpos)
    rw [LinearMap.sum_apply]
    rw [LinearMap.sum_apply] at hpsd
    simp only [LinearMap.smul_apply] at hpsd
    have hU : (∑ j, ((weights j : ℂ) - (μ : ℂ)) • Phi j P).PosSemidef := by
      apply Matrix.posSemidef_sum
      intro j _
      apply (hPositive j P hPpsd).smul
      rw [← Complex.ofReal_sub]
      exact Complex.zero_le_real.mpr (sub_nonneg.mpr (hμle j))
    have hsum := hpsd.add hU
    have hterm : ∀ j, (weights j : ℂ) • Phi j P - ((weights j : ℂ) - (μ : ℂ)) • Phi j P =
        (μ : ℂ) • Phi j P := by
      intro j
      rw [sub_smul, sub_sub_cancel]
    have heq : (c : ℂ) • P - ∑ j, (weights j : ℂ) • Phi j P +
          ∑ j, ((weights j : ℂ) - (μ : ℂ)) • Phi j P
        = (μ : ℂ) • (((c / μ : ℝ) : ℂ) • P - ∑ j, Phi j P) := by
      rw [sub_add, ← Finset.sum_sub_distrib]
      simp only [hterm]
      rw [smul_sub, smul_smul, ← Finset.smul_sum, Complex.ofReal_div,
        mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hμpos.ne')]
    rw [heq] at hsum
    have h2 := hsum.smul (Complex.zero_le_real.mpr (inv_nonneg.mpr hμpos.le))
    rwa [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hμpos.ne', Complex.ofReal_one,
      one_smul] at h2

end
