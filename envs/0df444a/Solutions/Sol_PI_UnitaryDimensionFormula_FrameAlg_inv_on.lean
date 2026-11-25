-- Prove2me | solution 1 for PI.UnitaryDimensionFormula.FrameAlg.inv_on
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:35:11.078945+00:00
-- url     : https://prove2.me/submissions/3213b78b-8f26-414b-ba38-12cc99fb4f02

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RankTwoDimensionFormula_IdxDcvAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open PI PI.UnitaryDimensionFormula PI.UnitaryDimensionFormula.FrameAlg
variable {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A) (J : Matrix n n A)
variable {r : ℕ}
namespace PI.UnitaryDimensionFormula.FrameAlg
theorem _root_.solution {k : ℕ} (G : Matrix (Fin k) (Fin k) A) (ε y : A) (hy : ε * G.det * y = ε) :
    ((ε * y) • G.adjugate) * G = ε • (1 : Matrix (Fin k) (Fin k) A) := by
  rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul]
  congr 1
  linear_combination hy
end PI.UnitaryDimensionFormula.FrameAlg
