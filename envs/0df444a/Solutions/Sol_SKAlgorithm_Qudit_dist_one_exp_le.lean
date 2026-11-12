-- Prove2me | solution 1 for SKAlgorithm.Qudit.dist_one_exp_le
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T00:01:51.729476+00:00
-- url     : https://prove2.me/submissions/ca426310-9ac9-4140-befd-c580e5b12309

import Mathlib
import Definitions.Def_SKAlgorithm_Qudit_Model

open scoped Matrix
open QAlgorithms
open scoped Matrix.Norms.L2Operator




theorem solution {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian) :
    specNorm (1 - NormedSpace.exp (Complex.I • H)) ≤ specNorm H := by
  classical
  change ‖(1 : Matrix (Fin d) (Fin d) ℂ) - NormedSpace.exp (Complex.I • H)‖ ≤ ‖H‖
  by_cases hd : d = 0
  · subst d
    have hzero : H = 0 := Subsingleton.elim _ _
    rw [hzero]
    simp
  haveI : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero hd⟩⟩
  have hsa : IsSelfAdjoint H := hH.isSelfAdjoint
  haveI : IsStarNormal H := hsa.isStarNormal
  have he : cfc (fun z : ℂ => 1 - Complex.exp (Complex.I * z)) H =
      (1 : Matrix (Fin d) (Fin d) ℂ) - NormedSpace.exp (Complex.I • H) := by
    rw [cfc_sub (fun _ : ℂ => 1) (fun z : ℂ => Complex.exp (Complex.I * z)) H,
      cfc_const_one ℂ H, cfc_comp_const_mul Complex.I Complex.exp H,
      CFC.complex_exp_eq_normedSpace_exp]
  rw [← he]
  apply norm_cfc_le (norm_nonneg H)
  intro z hz
  have hzreal : z = (z.re : ℂ) := hsa.mem_spectrum_eq_re hz
  have hnorm : ‖z.re‖ = ‖z‖ := by
    conv_rhs => rw [hzreal]
    exact (Complex.norm_real z.re).symm
  calc
    ‖1 - Complex.exp (Complex.I * z)‖ =
        ‖Complex.exp (Complex.I * (z.re : ℂ)) - 1‖ := by
      rw [norm_sub_rev]
      exact congrArg (fun w : ℂ => ‖Complex.exp (Complex.I * w) - 1‖) hzreal
    _ ≤ ‖z.re‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = ‖z‖ := hnorm
    _ ≤ ‖H‖ := spectrum.norm_le_norm_of_mem hz
