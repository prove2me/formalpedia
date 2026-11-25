-- Prove2me | solution 1 for PIW.AdelicOrbitU.stLam_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:48:57.508388+00:00
-- url     : https://prove2.me/submissions/6bbf178a-7b30-49fe-96a4-acacfcb5aa90

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_UnitChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_QuadFiniteDimensional
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_StLamOf
import Theorems.Thm_PIW_AdelicOrbitU_core
import Theorems.Thm_PIW_AdelicOrbitU_sigR_algebraMap
import Theorems.Thm_PIW_AdelicOrbitU_sigR_tmul
import Theorems.Thm_PIW_AdelicOrbitU_decomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelicOrbitU
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
namespace PIW.AdelicOrbitU
theorem _root_.solution (hQ : QuadGen) : StLam := by
  intro F E _ _ _ _ σ hfin hfix R _ _ hU t β hβ
  obtain ⟨θ, d, hθ, hσθ, hd, hspan⟩ := hQ F E σ hfin hfix
  obtain ⟨a, b, rfl⟩ := decomp R θ hspan t
  obtain ⟨T, hT0, hTd⟩ : ∃ T : F, T ≠ 0 ∧ T ^ 2 - d ≠ 0 := by
    by_cases h1 : d = 1
    · refine ⟨2, two_ne_zero, ?_⟩
      rw [h1]
      norm_num
    · refine ⟨1, one_ne_zero, ?_⟩
      rw [one_pow]
      exact sub_ne_zero.mpr (Ne.symm h1)
  obtain ⟨P, Q, hPQ, hQ0⟩ : ∃ P Q : F, P ^ 2 - d * Q ^ 2 = 1 ∧ Q ≠ 0 := by
    refine ⟨(T ^ 2 + d) / (T ^ 2 - d), 2 * T / (T ^ 2 - d), ?_, ?_⟩
    · field_simp
      ring
    · exact div_ne_zero (mul_ne_zero two_ne_zero hT0) hTd
  have hidR : ∀ x : R, algebraMap R R x = x := fun _ => rfl
  have hβS : algebraMap F (R ⊗[F] E) β = algebraMap R (R ⊗[F] E) (algebraMap F R β) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply,
      hidR]
  rw [hβS]
  refine core (algebraMap R (R ⊗[F] E)) (sigR R σ) (1 ⊗ₜ θ) (algebraMap F R d)
    (algebraMap F R β) (algebraMap F R P) (algebraMap F R Q) a b ?_ ?_ ?_ ?_
    (algebraMap F R β⁻¹) (algebraMap F R (Q * d)⁻¹) (algebraMap F R (1 / 4)) ?_ ?_ ?_ hU
  · rw [Algebra.TensorProduct.tmul_pow, one_pow, hθ, Algebra.TensorProduct.algebraMap_apply,
      hidR, Algebra.algebraMap_eq_smul_one d, Algebra.algebraMap_eq_smul_one d,
      TensorProduct.smul_tmul]
  · rw [sigR_tmul, hσθ, TensorProduct.tmul_neg]
  · exact fun r => sigR_algebraMap σ R r
  · rw [← map_pow, ← map_pow, ← map_mul, ← map_sub, hPQ, map_one]
  · rw [← map_mul, mul_inv_cancel₀ hβ, map_one]
  · rw [← map_mul, ← map_mul, mul_inv_cancel₀ (mul_ne_zero hQ0 hd), map_one]
  · have h4 : (4 : R) = algebraMap F R 4 := (map_ofNat (algebraMap F R) 4).symm
    rw [h4, ← map_mul]
    norm_num
end PIW.AdelicOrbitU
