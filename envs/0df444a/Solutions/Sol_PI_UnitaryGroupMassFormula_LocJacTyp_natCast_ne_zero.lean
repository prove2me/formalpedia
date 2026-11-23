-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.natCast_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:28:32.569098+00:00
-- url     : https://prove2.me/submissions/6339b005-2172-4e18-88e2-6ef37913048c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitAbs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.LocJacTyp
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace PI.UnitaryGroupMassFormula.LocJacTyp
theorem _root_.solution {g : ℕ} (hg : 0 < g) : (g : Fv F v) ≠ 0 := by
  intro h0
  have h1 : algebraMap F (Fv F v) (g : F) = algebraMap F (Fv F v) 0 := by
    rw [map_natCast, map_zero]
    exact h0
  exact (Nat.cast_ne_zero.2 hg.ne') ((algebraMap F (Fv F v)).injective h1)
end PI.UnitaryGroupMassFormula.LocJacTyp
