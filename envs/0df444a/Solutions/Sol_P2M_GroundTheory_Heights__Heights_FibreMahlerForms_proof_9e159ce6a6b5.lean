-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FibreMahlerForms_proof_9e159ce6a6b5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:13:43.538813+00:00
-- url     : https://prove2.me/submissions/11e23764-10f1-474d-a67c-6a1f1045814f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsFibreMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PDiagonalChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PFibreMahlerForms
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FibreMahlerForms_apply_repr_symm_bee5a38d5919
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FibreMahlerForms_mahler_linear_924a42cd360c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FibreMahlerForms_mahler_C_mul_prod_3290182d23cd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FibreMahlerForms_finrank_fibreSpace_df6a8049e968
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FibreMahlerForms_fibreGen_surjective_dc495228befe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FibreMahlerForms_archLin_fibreGen_25cb1cf05c25
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FibreMahlerForms_archDualNorm_eq_5570a2d01de9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FibreMahlerForms_exists_archLin_ne_zero_ed53fe7598d6

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
open MvPolynomial NumberField TensorProduct ComplexAt
noncomputable section
open FibreMahlerForms
namespace GroundTheory.Heights₂.Heights
namespace FibreMahlerForms
theorem _root_.solution : FibreMahlerForms.Statement := by
  intro F _ _ W _ _ _ _ h n w hw K _ _ _ τ m yv hyv a ha
  set σ := τ.comp (algebraMap F K) with hσ
  let b := stdOrthonormalBasis ℂ (FibreSpace h σ)
  have hsurj := fibreGen_surjective h σ w hw
  have hG : fibreMahler h σ w (C a * ∏ q, ∑ k, C (τ (yv q (w k))) * X k) =
      mahler (HermNorm.std (Module.finrank ℂ (FibreSpace h σ))) 1
        (C a * ∏ q, ∑ j, C (archLin h τ (yv q) (b j)) * X ((0 : Fin 1), j)) := by
    unfold fibreMahler fibreSphereMean mahler
    congr 1
    funext u
    set ξ := b.repr.symm (WithLp.toLp 2 fun j ↦ u (0, j))
    have hx : fibreGen h σ w (Function.invFun (fibreGen h σ w) ξ) = ξ :=
      Function.invFun_eq (hsurj ξ)
    simp only [fibrePoly, map_mul, eval_C, map_prod, map_sum, eval_X]
    refine congrArg (fun z ↦ Real.log ‖a * z‖) (Finset.prod_congr rfl fun q _ ↦ ?_)
    have h1 := archLin_fibreGen h τ (yv q) w (Function.invFun (fibreGen h σ w) ξ)
    rw [hx] at h1
    rw [← h1, apply_repr_symm]
  rw [hG, mahler_C_mul_prod]
  · congr 1
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    have hd : (harmonic (Module.finrank ℂ (FibreSpace h σ) - 1) : ℝ) =
        harmonic (Module.finrank (𝓞 F) W - 1) := by rw [finrank_fibreSpace]
    rw [mahler_linear _ (exists_archLin_ne_zero h τ (yv q) (hyv q) b), archDualNorm_eq h τ (yv q) b, hd]
  · intro q hq
    obtain ⟨j, hj⟩ := exists_archLin_ne_zero h τ (yv q) (hyv q) b
    have h1 := congrArg (eval fun ij : Fin 1 × Fin (Module.finrank ℂ (FibreSpace h σ)) ↦
      star (archLin h τ (yv q) (b ij.2))) hq
    simp only [map_sum, map_mul, eval_C, eval_X, map_zero, Complex.star_def, Complex.mul_conj'] at h1
    have h2 : ((∑ j, ‖archLin h τ (yv q) (b j)‖ ^ 2 : ℝ) : ℂ) = 0 := by push_cast; exact h1
    have h3 : ∑ j, ‖archLin h τ (yv q) (b j)‖ ^ 2 = 0 := by exact_mod_cast h2
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ by positivity)] at h3
    exact hj (by simpa using h3 j (Finset.mem_univ _))
  · exact ha
end FibreMahlerForms
end GroundTheory.Heights₂.Heights
