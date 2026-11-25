-- Prove2me | solution 1 for P2M_PI_MirrorSection__split_unique_901b42c7598e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:32:19.642122+00:00
-- url     : https://prove2.me/submissions/cc46d248-891a-4c11-a888-4a3c80a8c760

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_IsMonomialConjTranspose
import Theorems.Thm_P2M_PI_MirrorSection__ut_mul_7638fd5817a9
import Theorems.Thm_P2M_PI_MirrorSection__lt_mul_a8f5782a03d1
import Theorems.Thm_P2M_PI_MirrorSection__ut_inv_c3f594f8935a
import Theorems.Thm_P2M_PI_MirrorSection__lt_inv_ad263186a75e
import Theorems.Thm_P2M_PI_MirrorSection__ut_lt_eq_one_ee1d850c9437

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.MirrorSection₂
open Formalism.FourierDecayAlt.C2
variable {m : ℕ}
namespace PI.MirrorSection₂
theorem _root_.solution {P : Matrix (Fin m) (Fin m) ℂ} (hP : IsUnit P.det)
    {a₁ a₂ v₁ v₂ : Matrix (Fin m) (Fin m) ℂ}
    (ha₁ : P * a₁ * P⁻¹ ∈ LTset m) (ha₂ : P * a₂ * P⁻¹ ∈ LTset m)
    (hv₁ : P * v₁ * P⁻¹ ∈ UTset m) (hv₂ : P * v₂ * P⁻¹ ∈ UTset m)
    (h : a₁ * v₁ = a₂ * v₂) : a₁ = a₂ := by
  set A₁ := P * a₁ * P⁻¹
  set A₂ := P * a₂ * P⁻¹
  set V₁ := P * v₁ * P⁻¹
  set V₂ := P * v₂ * P⁻¹
  have hPP : P⁻¹ * P = 1 := nonsing_inv_mul P hP
  have hPP' : P * P⁻¹ = 1 := mul_nonsing_inv P hP
  have hAV : A₁ * V₁ = A₂ * V₂ := by
    have e1 : A₁ * V₁ = P * (a₁ * v₁) * P⁻¹ := by
      simp only [A₁, V₁, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P⁻¹ P, hPP, Matrix.one_mul]
    have e2 : A₂ * V₂ = P * (a₂ * v₂) * P⁻¹ := by
      simp only [A₂, V₂, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P⁻¹ P, hPP, Matrix.one_mul]
    rw [e1, e2, h]
  have iA := lt_inv ha₂
  have iV := ut_inv hv₁
  have hx : A₂⁻¹ * A₁ = V₂ * V₁⁻¹ := by
    calc A₂⁻¹ * A₁ = A₂⁻¹ * (A₁ * V₁) * V₁⁻¹ := by
          rw [Matrix.mul_assoc A₂⁻¹, Matrix.mul_assoc A₁, iV.1, Matrix.mul_one]
      _ = A₂⁻¹ * (A₂ * V₂) * V₁⁻¹ := by rw [hAV]
      _ = V₂ * V₁⁻¹ := by rw [← Matrix.mul_assoc A₂⁻¹, iA.2.1, Matrix.one_mul]
  have h1 : A₂⁻¹ * A₁ = 1 := ut_lt_eq_one (hx ▸ ut_mul hv₂ iV.2.2) (lt_mul iA.2.2 ha₁)
  have hA : A₁ = A₂ := by
    calc A₁ = A₂ * (A₂⁻¹ * A₁) := by rw [← Matrix.mul_assoc, iA.1, Matrix.one_mul]
      _ = A₂ := by rw [h1, Matrix.mul_one]
  have back : ∀ x : Matrix (Fin m) (Fin m) ℂ, x = P⁻¹ * (P * x * P⁻¹) * P := by
    intro x
    simp only [Matrix.mul_assoc]
    rw [hPP, Matrix.mul_one, ← Matrix.mul_assoc, hPP, Matrix.one_mul]
  rw [back a₁, back a₂]
  exact congrArg (fun y => P⁻¹ * y * P) hA
end PI.MirrorSection₂
