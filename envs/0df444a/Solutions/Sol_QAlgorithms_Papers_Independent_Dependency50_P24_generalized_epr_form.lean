-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P24.generalized_epr_form
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T02:36:01.996456+00:00
-- url     : https://prove2.me/submissions/9a592664-b390-454b-84c8-2adc97d57e89

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P24

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Finset

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Accepted declarations are imported rather than redeclared locally.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P04 (bellProjector)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits relativeEntanglement)


open scoped MatrixOrder in
lemma g53c_sqrt_mul_sqrt {H : Type*} [Fintype H] [DecidableEq H] (tau : Matrix H H ℂ)
    (h : tau.PosSemidef) : cfc Real.sqrt tau * cfc Real.sqrt tau = tau := by
  have hsa : IsSelfAdjoint tau := h.1
  have hnn : (0 : Matrix H H ℂ) ≤ tau := by
    rw [Matrix.nonneg_iff_posSemidef]; exact h
  rw [← cfc_mul Real.sqrt Real.sqrt tau]
  conv_rhs => rw [← cfc_id' ℝ tau]
  apply cfc_congr
  intro x hx
  have : 0 ≤ x := spectrum_nonneg_of_nonneg hnn hx
  simp [Real.mul_self_sqrt this]

lemma g53c_sqrt_herm {H : Type*} [Fintype H] [DecidableEq H] (tau : Matrix H H ℂ) :
    (cfc Real.sqrt tau)ᴴ = cfc Real.sqrt tau := by
  have : IsSelfAdjoint (cfc Real.sqrt tau) := cfc_predicate Real.sqrt tau
  exact this.star_eq

lemma g53c_amp {d : ℕ} {H : Type*} [Fintype H] [DecidableEq H] (tau : Op H)
    (U : Fin d → Matrix.unitaryGroup H ℂ) (htau : tau.PosSemidef) :
    operatorAmplitude tau U * (operatorAmplitude tau U)ᴴ = privateMatrix tau U := by
  ext a b
  have key : ((U a.1.1 : Op H) * tau * (U b.1.1 : Op H)ᴴ) =
      ((U a.1.1 : Op H) * cfc Real.sqrt tau) * ((U b.1.1 : Op H) * cfc Real.sqrt tau)ᴴ := by
    rw [Matrix.conjTranspose_mul, g53c_sqrt_herm]
    conv_lhs => rw [← g53c_sqrt_mul_sqrt tau htau]
    simp only [Matrix.mul_assoc]
  have hc : ((Real.sqrt d)⁻¹ : ℂ) * star ((Real.sqrt d)⁻¹ : ℂ) = (d : ℂ)⁻¹ := by
    have h1 : star ((Real.sqrt d)⁻¹ : ℂ) = ((Real.sqrt d)⁻¹ : ℂ) := by
      rw [star_inv₀]; congr 1; exact Complex.conj_ofReal _
    rw [h1, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]
    simp
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, operatorAmplitude, privateMatrix]
  by_cases ha : a.1.1 = a.1.2
  · by_cases hb : b.1.1 = b.1.2
    · rw [if_pos ⟨ha, hb⟩, key, Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [if_pos ha, if_pos hb, Matrix.conjTranspose_apply, star_mul', ← hc]
      ring
    · rw [if_neg (fun h => hb h.2)]
      simp [hb]
  · rw [if_neg (fun h => ha h.1)]
    simp [ha]

lemma g53c_trace {d : ℕ} [NeZero d] {H : Type*} [Fintype H] [DecidableEq H] (tau : Op H)
    (U : Fin d → Matrix.unitaryGroup H ℂ) (htau : tau.trace = 1) :
    (privateMatrix tau U).trace = 1 := by
  have hU : ∀ i, ((U i : Op H) * tau * (U i : Op H)ᴴ).trace = 1 := by
    intro i
    rw [Matrix.trace_mul_cycle, ← Matrix.star_eq_conjTranspose, Matrix.UnitaryGroup.star_mul_self, Matrix.one_mul, htau]
  rw [Matrix.trace, Fintype.sum_prod_type]
  have h2 : ∀ x : Key d, ∑ y : H, Matrix.diag (privateMatrix tau U) (x, y) =
      if x.1 = x.2 then (d : ℂ)⁻¹ else 0 := by
    intro x
    simp only [Matrix.diag_apply, privateMatrix, and_self]
    split_ifs with hx
    · rw [← Finset.mul_sum]
      have := hU x.1
      rw [Matrix.trace] at this
      simp only [Matrix.diag_apply] at this
      rw [this, mul_one]
    · simp
  rw [Finset.sum_congr rfl (fun x _ => h2 x), Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  field_simp

/-- PDF p.9, Eqs.(39)–(42): generalized EPR form with a common normalized polar modulus.
The actual private-bit corner is one half of Y0 Y1†. -/
theorem solution {d : ℕ} [NeZero d] {S T : Type*}
    [Fintype S] [Fintype T] [Nonempty S] [Nonempty T] (gamma : Op (Key d × (S × T))) :
    IsPrivate gamma ↔ ∃ tau : Op (S × T), IsDensityMatrix tau ∧
      ∃ U : Fin d → Matrix.unitaryGroup (S × T) ℂ,
        gamma = operatorAmplitude tau U * (operatorAmplitude tau U)ᴴ := by
  constructor
  · rintro ⟨_, tau, htau, U, rfl⟩
    exact ⟨tau, htau, U, (g53c_amp tau U htau.1).symm⟩
  · rintro ⟨tau, htau, U, rfl⟩
    refine ⟨⟨Matrix.posSemidef_self_mul_conjTranspose _, ?_⟩, tau, htau, U, g53c_amp tau U htau.1⟩
    rw [g53c_amp tau U htau.1]; exact g53c_trace tau U htau.2


end

