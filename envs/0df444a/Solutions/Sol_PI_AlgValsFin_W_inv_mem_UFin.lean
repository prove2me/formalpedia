-- Prove2me | solution 1 for PI.AlgValsFin.W.inv_mem_UFin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:23:58.064025+00:00
-- url     : https://prove2.me/submissions/e7d9b5a9-1e9f-4a10-aeed-ab2cb6b7a148

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ClassSame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_InvMemUFin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Neutral.B1 Topology
open PI PI.AlgValsFin PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L]
namespace PI.AlgValsFin.W
theorem _root_.solution {x : Ideles L} (hx : x ∈ UFin L) : x⁻¹ ∈ UFin L := by
  have hmul : (x : AdeleRing (𝓞 L) L) * ((x⁻¹ : Ideles L) : AdeleRing (𝓞 L) L) = 1 := x.mul_inv
  refine ⟨?_, fun v => ?_⟩
  · have h2 : (x : AdeleRing (𝓞 L) L).1 * ((x⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).1 = 1 :=
      congrArg (fun y : AdeleRing (𝓞 L) L => y.1) hmul
    rw [hx.1, one_mul] at h2
    exact h2
  · have h2 : (x : AdeleRing (𝓞 L) L).2 v * ((x⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v = 1 :=
      congrArg (fun y : AdeleRing (𝓞 L) L => y.2 v) hmul
    have h3 := congrArg Valued.v h2
    rw [map_mul, hx.2 v, one_mul, map_one] at h3
    exact h3
end PI.AlgValsFin.W
