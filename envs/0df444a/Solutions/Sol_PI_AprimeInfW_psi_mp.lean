-- Prove2me | solution 1 for PI.AprimeInfW.psi_mp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:14:28.528421+00:00
-- url     : https://prove2.me/submissions/51e88ee4-b429-4c45-892c-60edc5c2a7a2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_DetMulRCReal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_MpOfIsomProd
import Theorems.Thm_PI_AprimeInfW_mp_of_isom_prod
import Theorems.Thm_PI_AprimeInfW_norm_reim_sq
import Theorems.Thm_PI_AprimeInfW_reim_surj
import Theorems.Thm_PI_AprimeInfW_herm_pyth
import Theorems.Thm_PI_AprimeInfW_psiLp_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfW
open MeasureTheory Matrix ComplexConjugate
namespace PI.AprimeInfW
theorem _root_.solution {m : ℕ} {η : Type} [Fintype η] (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ)
    (hH : ∀ t, (H t)ᴴ = H t) (hn : ∀ t, ∑ i, ∑ j, ‖H t i j‖ ^ 2 = ‖t‖ ^ 2)
    (hs : ∀ M : Matrix (Fin m) (Fin m) ℂ, Mᴴ = M → ∃ t, H t = M) :
    MeasurePreserving (psiLp H) volume volume := by
  apply mp_of_isom_prod
  · intro a b
    rw [psiLp_apply, norm_reim_sq, herm_pyth _ _ (hH a) (hH b), hn a, hn b]
  · intro y
    obtain ⟨Y, rfl⟩ := reim_surj y
    set A : Matrix (Fin m) (Fin m) ℂ := (-(Complex.I / 2)) • (Y - Yᴴ) with hAdef
    set B : Matrix (Fin m) (Fin m) ℂ := (1 / 2 : ℂ) • (Y + Yᴴ) with hBdef
    have hA : Aᴴ = A := by
      rw [hAdef, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
        Matrix.conjTranspose_conjTranspose]
      ext i j
      simp [Complex.ext_iff]
      constructor <;> ring
    have hB : Bᴴ = B := by
      rw [hBdef, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
        Matrix.conjTranspose_conjTranspose]
      ext i j
      simp [Complex.ext_iff]
      constructor <;> ring
    obtain ⟨s, hsA⟩ := hs A hA
    obtain ⟨t, htB⟩ := hs B hB
    refine ⟨(s, t), ?_⟩
    rw [psiLp_apply]
    congr 1
    simp only [hsA, htB]
    ext i j
    simp [hAdef, hBdef, Complex.ext_iff]
    constructor <;> ring
end PI.AprimeInfW
