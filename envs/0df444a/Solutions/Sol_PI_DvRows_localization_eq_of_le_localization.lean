-- Prove2me | solution 1 for PI.DvRows.localization_eq_of_le_localization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:39:47.431001+00:00
-- url     : https://prove2.me/submissions/3ad20abc-f513-409e-bb69-f5b006bd9037

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndexDeterminant_NegLogValuation
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LatticeFinitelyGenerated
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_idem
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_mono


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
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv
open Formalism.HermitianLatticesTheory
variable {R : Type*} [CommRing R] {W W' : Type*} [AddCommGroup W] [Module R W]
  [AddCommGroup W'] [Module R W']
namespace PI.DvRows
theorem _root_.solution (p : Ideal R) [p.IsPrime] {X Y : Submodule R W} (h1 : X ≤ localization₂ p Y)
    (h2 : Y ≤ localization₂ p X) : localization₂ p X = localization₂ p Y := by
  unfold localization₂ at h1 h2 ⊢
  apply le_antisymm
  · calc locS p.primeCompl X ≤ locS p.primeCompl (locS p.primeCompl Y) :=
          locBasic_locS_mono _ h1
      _ = locS p.primeCompl Y := locBasic_locS_idem _ _
  · calc locS p.primeCompl Y ≤ locS p.primeCompl (locS p.primeCompl X) :=
          locBasic_locS_mono _ h2
      _ = locS p.primeCompl X := locBasic_locS_idem _ _
end PI.DvRows
