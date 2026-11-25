-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KSplit.kill_dY
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:40:44.022846+00:00
-- url     : https://prove2.me/submissions/3fb17f73-847f-48aa-a60b-f36b8ef1edff

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ThetaSplitting_ActUDiagMonomial
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_dY_add
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_dY_smul
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_kill_herm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KSplit
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.SiegelWeilFormula.KSplit
theorem _root_.solution (Λ : PX m n →ₗ[ℂ] ℂ) (hΛ : ∀ u ∈ unitaryGroup (Fin m) ℂ, ∀ P, Λ (actU u P) = Λ P)
    (Y : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) : Λ (dY Y P) = 0 := by
  obtain ⟨H₁, h1, H₂, h2, eY⟩ : ∃ H₁ : Matrix (Fin m) (Fin m) ℂ, H₁.IsHermitian ∧ ∃ H₂ : Matrix (Fin m) (Fin m) ℂ,
      H₂.IsHermitian ∧ Y = H₁ + Complex.I • H₂ := by
    refine ⟨(1 / 2 : ℂ) • (Y + Yᴴ), ?_, (1 / (2 * Complex.I) : ℂ) • (Y - Yᴴ), ?_, ?_⟩
    · ext i j
      simp only [IsHermitian, conjTranspose_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, star_mul',
        star_add, star_star]
      rw [show star (1 / 2 : ℂ) = 1 / 2 by simp [Complex.ext_iff]]
      ring
    · ext i j
      simp only [IsHermitian, conjTranspose_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, star_mul',
        star_sub, star_star]
      rw [show star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) by
        simp [Complex.ext_iff, Complex.div_re, Complex.div_im]]
      ring
    · ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
      field_simp
      ring
  rw [eY, dY_add, dY_smul, Derivation.add_apply, Derivation.smul_apply, map_add, map_smul, kill_herm Λ hΛ _ h1,
    kill_herm Λ hΛ _ h2, smul_zero, add_zero]
end PositivityTheory.SiegelWeilFormula.KSplit
