-- Prove2me | solution 1 for PI.ET.HornW.compress_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:38:03.653574+00:00
-- url     : https://prove2.me/submissions/adab258d-c094-4a53-be4f-530ceca179b9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExpTri
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_SortedSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_NormDetConjExp
import Theorems.Thm_PI_ET_HornW_unit_star_mul
import Theorems.Thm_PI_ET_HornW_emb_compress

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped MatrixOrder ComplexOrder
noncomputable section
open PI PI.ET
open PI.ET.HornW
variable {n : ℕ}
namespace PI.ET.HornW
theorem _root_.solution {W : Matrix (Fin n) (Fin n) ℂ} (hW : W ∈ unitaryGroup (Fin n) ℂ) {k : ℕ}
    (hk : k ≤ n) (f : Fin n → ℂ) :
    (W * emb hk)ᴴ * (W * diagonal f * Wᴴ) * (W * emb hk) =
      diagonal (fun i => f (Fin.castLE hk i)) := by
  rw [conjTranspose_mul]
  calc (emb hk)ᴴ * Wᴴ * (W * diagonal f * Wᴴ) * (W * emb hk)
      = (emb hk)ᴴ * ((Wᴴ * W) * diagonal f * (Wᴴ * W)) * emb hk := by simp only [Matrix.mul_assoc]
    _ = diagonal (fun i => f (Fin.castLE hk i)) := by
      rw [unit_star_mul hW, Matrix.one_mul, Matrix.mul_one, emb_compress]
end PI.ET.HornW
