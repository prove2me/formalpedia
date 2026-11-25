-- Prove2me | solution 1 for PIW.AdelicOrbitU.uc_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:20:48.447929+00:00
-- url     : https://prove2.me/submissions/6add0258-5135-4db2-b4aa-5f7e6399b15d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_UnitChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_LocalSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelicOrbitU
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped RestrictedProduct
namespace PIW.AdelicOrbitU
theorem _root_.solution {A : Type} [CommRing A] {k : ℕ} (f a : Fin k → A) (h : ∑ i, a i * f i = 1) :
    Ideal.span (Set.range f) = ⊤ := by
  exact (Ideal.eq_top_iff_one _).mpr (Ideal.mem_span_range_iff_exists_fun.mpr ⟨a, h⟩)
end PIW.AdelicOrbitU
