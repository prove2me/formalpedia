-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P06.quantum_complete_tni
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:48:31.885149+00:00
-- url     : https://prove2.me/submissions/0557061b-f74d-4c21-a225-e5ce2838ec98

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P06

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P06

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

section QuantumResults

variable {A0 A1 B0 B1 : Type}

variable [Fintype A0] [Fintype A1] [Fintype B0] [Fintype B1]

variable [hA0 : Nonempty A0] [hA1 : Nonempty A1] [hB0 : Nonempty B0] [hB1 : Nonempty B1]

/-- PDF pp.5–6,24, (6.1): ordinary CPTNI maps remain CPTNI when tensored
with an identity channel, rather than an identity supermap. -/
theorem solution [Nonempty A0] [Nonempty A1] (E : QMap A0 A1) (hE : IsCPTNI E) :
    ∀ r : ℕ, 0 < r → ∀ rho : Op (Fin r × A0), IsDensityMatrix rho →
      (idTensorSuperop E rho).PosSemidef ∧ (idTensorSuperop E rho).trace.re ≤ 1 := by
  intro r _ rho hrho
  refine ⟨hE.1 r rho hrho.1, ?_⟩
  let B : Fin r → Op A0 := fun s => Matrix.of fun i i' => rho (s, i) (s, i')
  have hblk : ∀ s, (B s).PosSemidef := fun s => hrho.1.submatrix (fun i => (s, i))
  have htr : (idTensorSuperop E rho).trace = ∑ s, (E (B s)).trace := by
    simp [Matrix.trace, idTensorSuperop, Fintype.sum_prod_type, B]
  have hsum : ∑ s, (B s).trace = 1 := by
    rw [← hrho.2]; simp [Matrix.trace, Fintype.sum_prod_type, B]
  have key : ∀ s, (E (B s)).trace.re ≤ (B s).trace.re := by
    intro s
    have h0 : 0 ≤ (B s).trace := (hblk s).trace_nonneg
    rw [Complex.nonneg_iff] at h0
    rcases h0.1.lt_or_eq with hpos | hzero
    · set t := (B s).trace.re with ht
      have htc : (B s).trace = (t : ℂ) := Complex.ext (by simp [t]) (by simp [h0.2])
      have hd : IsDensityMatrix (((t⁻¹ : ℝ) : ℂ) • B s) := by
        refine ⟨(hblk s).smul ?_, ?_⟩
        · exact_mod_cast (inv_nonneg.mpr hpos.le)
        · rw [Matrix.trace_smul, htc, smul_eq_mul, ← Complex.ofReal_mul,
            inv_mul_cancel₀ hpos.ne', Complex.ofReal_one]
      have := hE.2 _ hd
      rw [map_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul] at this
      have h2 := mul_le_mul_of_nonneg_left this hpos.le
      rwa [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul, mul_one] at h2
    · have hz : (B s).trace = 0 := Complex.ext (by simp [← hzero]) (by simp [h0.2])
      rw [(hblk s).trace_eq_zero_iff.mp hz, map_zero]
      simp
  rw [htr, Complex.re_sum]
  calc ∑ s, (E (B s)).trace.re ≤ ∑ s, (B s).trace.re := Finset.sum_le_sum fun s _ => key s
    _ = 1 := by rw [← Complex.re_sum, hsum, Complex.one_re]

end QuantumResults


end

