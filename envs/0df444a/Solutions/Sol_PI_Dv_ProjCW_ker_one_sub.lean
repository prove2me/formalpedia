-- Prove2me | solution 1 for PI.Dv.ProjCW.ker_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:36:13.472458+00:00
-- url     : https://prove2.me/submissions/5d9a22a5-59fe-403b-843f-06b57a57ec53

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
theorem _root_.solution (e : Module.End K V) (he : e * e = e) :
    LinearMap.ker (1 - e) = LinearMap.range e := by
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hx
    exact ⟨x, hx.symm⟩
  · rintro ⟨y, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, ← Module.End.mul_apply, he, sub_self]
end PI.Dv.ProjCW
