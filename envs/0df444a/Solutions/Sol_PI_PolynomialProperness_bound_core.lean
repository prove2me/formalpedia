-- Prove2me | solution 1 for PI.PolynomialProperness.bound_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:26:48.307856+00:00
-- url     : https://prove2.me/submissions/0237778b-5274-413e-9be0-47b510608b72

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_AddLeMulPowOfSqLeOfLeMul
import Theorems.Thm_PI_PolynomialProperness_fmul_one
import Theorems.Thm_PI_PolynomialProperness_frame_mulVec_fmul
import Theorems.Thm_PI_PolynomialProperness_ut_mul_inv
import Theorems.Thm_PI_PolynomialProperness_mx_nonneg
import Theorems.Thm_PI_PolynomialProperness_real_sq_bound
import Theorems.Thm_PI_PolynomialProperness_add_le_mul_pow_of_sq_le_of_le_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
open scoped ComplexConjugate
noncomputable section
open PI PI.PolynomialProperness
namespace PI.PolynomialProperness
theorem _root_.solution (hG : GVGroup) (hN : NormInv) (hNF : GNFacts)
    {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
    {Cf Cf' CA Cc : ℝ}
    (hCf : ∀ c b, nsq (fmul k r z c b) ≤ Cf * mx c ^ 2)
    (hCf' : ∀ c b, nsq (fmul k r z' c b) ≤ Cf' * mx c ^ 2)
    (hCc : ∀ s ∈ B.GV k r, ∀ K : ℝ, 0 ≤ K → (∀ i, nsq (s *ᵥ gramVec k r z z' γ i) ≤ K) →
      B.gN s ^ 2 ≤ Cc * (1 + K) ^ 2)
    (σ s' : B.Mat k r) (v u' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hσ : σ ∈ B.GV k r) (hs' : s' ∈ B.GV k r) (hv : v ∈ UTset (r + 1)) (hu : u' ∈ UTset (r + 1))
    (hσf : ∀ b, σ *ᵥ fvec k r z b = fmul k r z v b)
    (hsf : ∀ b, s' *ᵥ fvec k r z' b = fmul k r z' u' b)
    (hbv : mx v⁻¹ ≤ CA * B.gN (σ⁻¹ * γ * s') ^ (r * (r + 1)))
    (hbu : mx u'⁻¹ ≤ CA * B.gN (σ⁻¹ * γ * s') ^ (r * (r + 1))) :
    B.gN σ + B.gN s' ≤ (1 + B.gN γ⁻¹) * (|Cc| * (1 + (|Cf| + |Cf'|) * CA ^ 2) ^ 2) *
      B.gN (σ⁻¹ * γ * s') ^ (5 * (r + 1) ^ 2) := by
  obtain ⟨hmul, hinv⟩ := hG k r
  obtain ⟨hnn, hsub, hvec, -⟩ := hNF k r
  have hσi := hinv σ hσ
  have hγi := hinv γ hγ
  have hg : σ⁻¹ * γ * s' ∈ B.GV k r := hmul _ (hmul _ hσi.2.1 _ hγ) _ hs'
  have hx1 : 1 ≤ B.gN (σ⁻¹ * γ * s') := (hN k r _ hg).2

  have hσinv_f : ∀ b, σ⁻¹ *ᵥ fvec k r z b = fmul k r z v⁻¹ b := by
    intro b
    have h1 : σ *ᵥ fmul k r z v⁻¹ b = fvec k r z b := by
      rw [frame_mulVec_fmul hσf, ut_mul_inv hv, fmul_one]
    rw [← h1, Matrix.mulVec_mulVec, hσi.2.2.2, Matrix.one_mulVec]

  have hσinv_f' : ∀ b, σ⁻¹ *ᵥ (γ *ᵥ fvec k r z' b) =
      (σ⁻¹ * γ * s') *ᵥ fmul k r z' u'⁻¹ b := by
    intro b
    have h1 : s' *ᵥ fmul k r z' u'⁻¹ b = fvec k r z' b := by
      rw [frame_mulVec_fmul hsf, ut_mul_inv hu, fmul_one]
    rw [← h1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hgv : ∀ i, nsq (σ⁻¹ *ᵥ gramVec k r z z' γ i) ≤
      (|Cf| + |Cf'|) * CA ^ 2 * B.gN (σ⁻¹ * γ * s') ^ (2 * (r * (r + 1)) + 2) := by
    intro i
    generalize hxg : B.gN (σ⁻¹ * γ * s') = x at hx1 hbv hbu
    have hx0 : 0 ≤ x := by linarith
    have hxp : x ^ (2 * (r * (r + 1))) ≤ x ^ (2 * (r * (r + 1)) + 2) :=
      pow_le_pow_right₀ hx1 (by omega)
    have hc0 : 0 ≤ CA ^ 2 := sq_nonneg _
    cases i with
    | inl a =>
      show nsq (σ⁻¹ *ᵥ fvec k r z a) ≤ _
      rw [hσinv_f]
      have h1 := real_sq_bound (mx_nonneg _) hbv hx1 (hCf v⁻¹ a)
      have h2 : |Cf| * CA ^ 2 * x ^ (2 * (r * (r + 1))) ≤ |Cf| * CA ^ 2 * x ^ (2 * (r * (r + 1)) + 2) :=
        mul_le_mul_of_nonneg_left hxp (by positivity)
      have h3 : 0 ≤ |Cf'| * CA ^ 2 * x ^ (2 * (r * (r + 1)) + 2) := by positivity
      linarith
    | inr b =>
      show nsq (σ⁻¹ *ᵥ (γ *ᵥ fvec k r z' b)) ≤ _
      rw [hσinv_f']
      have h0 := hvec (σ⁻¹ * γ * s') (fmul k r z' u'⁻¹ b)
      rw [hxg] at h0
      have h1 := real_sq_bound (mx_nonneg _) hbu hx1 (hCf' u'⁻¹ b)
      have h2 : x ^ 2 * nsq (fmul k r z' u'⁻¹ b) ≤ x ^ 2 * (|Cf'| * CA ^ 2 * x ^ (2 * (r * (r + 1)))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h3 : x ^ 2 * (|Cf'| * CA ^ 2 * x ^ (2 * (r * (r + 1)))) =
          |Cf'| * CA ^ 2 * x ^ (2 * (r * (r + 1)) + 2) := by ring
      have h4 : 0 ≤ |Cf| * CA ^ 2 * x ^ (2 * (r * (r + 1)) + 2) := by positivity
      linarith
  have hD : 0 ≤ (|Cf| + |Cf'|) * CA ^ 2 := by positivity
  have hcore := hCc σ⁻¹ hσi.2.1 _ (by positivity) hgv
  have hNσ := hN k r σ hσ
  rw [hNσ.1] at hcore
  have hs'eq : s' = γ⁻¹ * σ * (σ⁻¹ * γ * s') := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc γ⁻¹ σ σ⁻¹, hσi.2.2.1,
      Matrix.mul_one, hγi.2.2.2, Matrix.one_mul]
  have hs'b : B.gN s' ≤ B.gN γ⁻¹ * B.gN σ * B.gN (σ⁻¹ * γ * s') := by
    conv_lhs => rw [hs'eq]
    calc B.gN (γ⁻¹ * σ * (σ⁻¹ * γ * s')) ≤ B.gN (γ⁻¹ * σ) * B.gN (σ⁻¹ * γ * s') := hsub _ _
      _ ≤ B.gN γ⁻¹ * B.gN σ * B.gN (σ⁻¹ * γ * s') :=
        mul_le_mul_of_nonneg_right (hsub _ _) (hnn _)
  have hN5 : 4 * (r * (r + 1)) + 5 ≤ 5 * (r + 1) ^ 2 := by nlinarith
  exact add_le_mul_pow_of_sq_le_of_le_mul hD (hnn γ⁻¹) hNσ.2 hx1 hcore hs'b hN5
end PI.PolynomialProperness
