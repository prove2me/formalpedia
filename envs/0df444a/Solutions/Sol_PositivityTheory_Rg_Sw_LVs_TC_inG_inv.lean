-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.TC.inG_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:12:51.50721+00:00
-- url     : https://prove2.me/submissions/90f4df3c-b541-42ac-ba4e-9f4073cea46f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCMatA
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BlkB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCMatB
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_inG_mul_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.TC
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.TC
theorem _root_.solution {g : M2 n} (hg : InG g) : InG g⁻¹ := by
  have h1 := inG_mul_inv hg
  unfold InG at *
  calc (g⁻¹)ᴴ * JJ n * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * JJ n * g) * g⁻¹ := by rw [hg]
    _ = (g * g⁻¹)ᴴ * JJ n * (g * g⁻¹) := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = JJ n := by rw [h1]; simp
end PositivityTheory.Rg.Sw.LVs.TC
