-- Prove2me | solution 1 for PI.BeDiagZp.SubstW.mem_SerS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:34:34.743364+00:00
-- url     : https://prove2.me/submissions/6ce19104-a374-401b-a968-2c167d25d899

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_PowerSeriesDiagonalLinear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.BeDiagZp PI.BeDiagZp.SubstW
namespace PI.BeDiagZp.SubstW
theorem _root_.solution {K : Type*} [CommRing K] (S : Subring K) {σ : Type*} (f : MvPowerSeries σ K) :
    f ∈ SerS S σ ↔ ∀ e, MvPowerSeries.coeff e f ∈ S := by
  constructor
  · rintro ⟨g, rfl⟩ e
    rw [MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff e g).2
  · intro h
    obtain ⟨g, hg⟩ : ∃ g : MvPowerSeries σ S, ∀ e, MvPowerSeries.coeff e g = ⟨MvPowerSeries.coeff e f, h e⟩ :=
      ⟨fun e => ⟨MvPowerSeries.coeff e f, h e⟩, fun e => rfl⟩
    refine ⟨g, ?_⟩
    ext e
    rw [MvPowerSeries.coeff_map, hg]
    rfl
end PI.BeDiagZp.SubstW
