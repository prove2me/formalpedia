-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.compact_region_estimate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:03:26.356899+00:00
-- url     : https://prove2.me/submissions/e5303860-9e6e-47c5-8621-b1a03be21896

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompRB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompactRegionEstimate
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CRH_cs_LR
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CRH_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
open PI PI.UnitaryCorollaryDerivatives
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace PI.UnitaryCorollaryDerivatives
theorem _root_.solution : CompR := by
  intro k r ψ h cost n C₀ hψ hh hb H
  obtain ⟨K, _, hK⟩ := CRH.main ψ h cost n C₀ hψ hh hb (by
      rintro w ⟨u, v, hu, hv, hl, rfl⟩ hne g hg
      have hne' : u ++ v ≠ [] := by
        rintro h0
        rw [List.append_eq_nil_iff] at h0
        obtain ⟨rfl, rfl⟩ := h0
        exact hne (by simp [P.BetaSesquilinearity.wL, P.BetaSesquilinearity.wR])
      have key := H u v hu hv hl hne' g hg
      rwa [P.BetaSesquilinearity.dLR_eq, Real.rpow_natCast, CRH.cs_LR] at key) n 0
  refine ⟨K, fun u v hu hv hl g hg => ?_⟩
  have key := hK (P.BetaSesquilinearity.wL u ++ P.BetaSesquilinearity.wR v) ⟨u, v, hu, hv, hl, rfl⟩
    (by simpa [P.BetaSesquilinearity.wL, P.BetaSesquilinearity.wR] using hl) g hg
  rw [P.BetaSesquilinearity.dLR_eq, zero_add, Real.rpow_natCast, CRH.cs_LR]
  simpa [iteratedDeriv_zero] using key
end PI.UnitaryCorollaryDerivatives
