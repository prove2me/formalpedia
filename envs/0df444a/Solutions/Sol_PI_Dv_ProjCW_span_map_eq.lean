-- Prove2me | solution 1 for PI.Dv.ProjCW.span_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:36:22.250987+00:00
-- url     : https://prove2.me/submissions/56761fc2-91ad-407c-a1ba-d923e4f09e15

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSpans_SpanPowSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjCW
open Formalism.BasicNotions NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.ProjCW
theorem _root_.solution (φ : V →ₗ[K] V) (M : Submodule (𝓞 K) V) (hM : Submodule.span K (M : Set V) = ⊤) :
    Submodule.span K ((M.map (φ.restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V) =
      LinearMap.range φ := by
  rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hM, Submodule.map_top]
end PI.Dv.ProjCW
