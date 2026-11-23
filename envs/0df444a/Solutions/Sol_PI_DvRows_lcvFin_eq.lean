-- Prove2me | solution 1 for PI.DvRows.lcvFin_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:04.610515+00:00
-- url     : https://prove2.me/submissions/4e4b8d4d-e7ca-4dce-8d0e-75824fe3b982

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_AsmBound

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
variable {K : Type} [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
namespace PI.DvRows
theorem _root_.solution (A : HLat K) {j : ℕ} (y : Fin j → A.V) (M : Submodule (𝓞 K) A.V) :
    lcvFin y M = 2 * ∑ᶠ w : HeightOneSpectrum (𝓞 K),
      lw K w * (Formalism.HermitianLatticesTheory.lidx w.asIdeal (Submodule.span (𝓞 K) (Set.range y)) M : ℝ) := by
  unfold lcvFin
  congr 1
  rw [← finsum_comp_equiv (hosEquiv (K := K))]
  rfl
end PI.DvRows
