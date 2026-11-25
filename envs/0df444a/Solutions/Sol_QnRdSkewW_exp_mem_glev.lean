-- Prove2me | solution 1 for QnRdSkewW.exp_mem_glev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:03:54.643798+00:00
-- url     : https://prove2.me/submissions/d5697048-8633-4401-9c00-1c44830c9dd0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkewAnalyticGroup_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkewAnalyticGroup_SkewReductionGroup
import Theorems.Thm_QnRdSkewW_exp_mulVec_fix
import Theorems.Thm_QnRdSkewW_exp_mem_UH
import Theorems.Thm_Formalism_QuantumDeterminants_hpkFacts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open QnRdSkewW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
namespace QnRdSkewW
theorem _root_.solution {k r : ℕ} {i : Fin (r + 1)} {X : Mx k r} (hX : inLieLev k r i X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i := by
  obtain ⟨hL, hF⟩ := hX
  have hH : Hpk k r * Hpk k r = 1 := (hpkFacts k r).2.1
  refine ⟨exp_mem_UH _ _ hH ?_, fun a ha => ?_⟩
  · rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.mul_smul, ← smul_add, hL, smul_zero]
  · obtain ⟨h1, h2⟩ := hF a ha
    exact ⟨exp_mulVec_fix X _ h1 t, exp_mulVec_fix X _ h2 t⟩
end QnRdSkewW
