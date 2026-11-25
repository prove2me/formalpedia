-- Prove2me | solution 1 for PI.DvRows.mem_span_of_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:39:41.610439+00:00
-- url     : https://prove2.me/submissions/1a78f498-fd6b-4fa6-989b-a4a826c5572e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_AsmDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Adapted

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv Formalism.LFunctionChainParameters.LLcv
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace PI.DvRows
theorem _root_.solution {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V) {x : V} (s : 𝓞 K) (hs : s ≠ 0)
    (hsx : s • x ∈ M) : x ∈ Submodule.span K (M : Set V) := by
  have hs0 : algebraMap (𝓞 K) K s ≠ 0 := by
    intro h0; exact hs (IsFractionRing.injective (𝓞 K) K (by rw [h0, map_zero]))
  have : x = (algebraMap (𝓞 K) K s)⁻¹ • (s • x) := by
    rw [← algebraMap_smul K s x, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hsx)
end PI.DvRows
