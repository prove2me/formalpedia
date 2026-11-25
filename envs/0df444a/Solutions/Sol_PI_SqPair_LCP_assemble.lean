-- Prove2me | solution 1 for PI.SqPair.LCP.assemble
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:33:29.86682+00:00
-- url     : https://prove2.me/submissions/ab499edc-ce8d-4203-ae5f-a9065d1691a0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PiNonunit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_FiniteAdeleIdempotentOfFMulSelf
import Theorems.Thm_PI_SqPair_LCP_finiteAdeleIdempotentOfF_mul_self
import Theorems.Thm_PI_SqPair_LCP_elementary_hyperbolic
import Theorems.Thm_PI_SqPair_LCP_elementary_commutes_diagonal
import Theorems.Thm_PI_SqPair_LCP_cancel_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SqPair PI.SqPair.LCP
variable {R : Type} [CommRing R] [StarRing R]
namespace PI.SqPair.LCP
theorem _root_.solution {κ : Type} [Fintype κ] [DecidableEq κ]
    (A h u u' : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R) (A₁ h₂ : Matrix κ κ R) (d : Fin 2 → R)
    (hu : IsUnit u.det) (hu' : IsUnit u'.det)
    (hA : uᴴ * A * u = fromBlocks hyp 0 0 A₁)
    (hh : h * u' = u * fromBlocks (diagonal d) 0 0 h₂)
    (e₂ f₂ : Matrix κ κ R) (he : e₂ * e₂ = e₂) (heA : e₂ᴴ * A₁ = A₁ * (1 - e₂))
    (hef : e₂ * h₂ = h₂ * f₂) : PConcl A h := by
  set E : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R := fromBlocks e0 0 0 e₂ with hEdef
  set F : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R := fromBlocks e0 0 0 f₂ with hFdef
  set D : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R := fromBlocks (diagonal d) 0 0 h₂ with hDdef
  set B : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R := fromBlocks hyp 0 0 A₁ with hBdef
  have hi : u⁻¹ * u = 1 := nonsing_inv_mul u hu
  have hi' : u'⁻¹ * u' = 1 := nonsing_inv_mul u' hu'
  have hE : E * E = E := by simp [hEdef, fromBlocks_multiply, finiteAdeleIdempotentOfF_mul_self, he]
  have hED : E * D = D * F := by simp [hEdef, hDdef, hFdef, fromBlocks_multiply, elementary_commutes_diagonal, hef]
  have heA' : e₂ᴴ * A₁ = A₁ - A₁ * e₂ := by rw [heA, Matrix.mul_sub, Matrix.mul_one]
  have hEB : Eᴴ * B = B - B * E := by
    rw [hEdef, hBdef, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    ext (i | i) (j | j) <;>
      simp [elementary_hyperbolic, heA', Matrix.sub_apply]
  refine ⟨u * E * u⁻¹, u' * F * u'⁻¹, ?_, ?_, ?_⟩
  · calc u * E * u⁻¹ * (u * E * u⁻¹) = u * (E * (u⁻¹ * u) * E) * u⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = u * E * u⁻¹ := by rw [hi, Matrix.mul_one, hE]
  · apply cancel_conj hu
    have hct : uᴴ * (u⁻¹)ᴴ = 1 := by rw [← conjTranspose_mul, hi, conjTranspose_one]
    calc uᴴ * ((u * E * u⁻¹)ᴴ * A) * u = (uᴴ * (u⁻¹)ᴴ) * Eᴴ * (uᴴ * A * u) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Eᴴ * B := by rw [hct, Matrix.one_mul, hA]
      _ = B - B * E * (u⁻¹ * u) := by rw [hi, Matrix.mul_one, hEB]
      _ = uᴴ * (A * (1 - u * E * u⁻¹)) * u := by
          rw [← hA]; simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
  · have hh' : h = u * D * u'⁻¹ := by
      rw [← hh, Matrix.mul_assoc, mul_nonsing_inv u' hu', Matrix.mul_one]
    rw [hh']
    calc u * E * u⁻¹ * (u * D * u'⁻¹) = u * (E * (u⁻¹ * u) * D) * u'⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = u * (D * (u'⁻¹ * u') * F) * u'⁻¹ := by rw [hi, hi', Matrix.mul_one, Matrix.mul_one, hED]
      _ = u * D * u'⁻¹ * (u' * F * u'⁻¹) := by simp only [Matrix.mul_assoc]
end PI.SqPair.LCP
