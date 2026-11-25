-- Prove2me | solution 1 for PI.AlgValsFin.W.val_inv_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:18:55.054212+00:00
-- url     : https://prove2.me/submissions/63c20621-7327-4c23-b3a9-b46e03466198

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ClassSame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_InvMemUFin
import Theorems.Thm_PI_AlgValsFin_W_inv_mem_UFin

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
theorem _root_.solution {x : Ideles L} (hx : x ∈ UFin L) (v : HeightOneSpectrum (𝓞 L)) :
    Valued.v ((x⁻¹ : Ideles L).val.2 v - 1) = Valued.v ((x : AdeleRing (𝓞 L) L).2 v - 1) := by
  have hmul : (x : AdeleRing (𝓞 L) L) * ((x⁻¹ : Ideles L) : AdeleRing (𝓞 L) L) = 1 := x.mul_inv
  have h2 : (x : AdeleRing (𝓞 L) L).2 v * ((x⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v = 1 :=
    congrArg (fun y : AdeleRing (𝓞 L) L => y.2 v) hmul
  have hz : Valued.v (((x⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v) = 1 := (inv_mem_UFin hx).2 v
  have heq : (x⁻¹ : Ideles L).val.2 v - 1 =
      ((x⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v * (1 - (x : AdeleRing (𝓞 L) L).2 v) := by
    rw [mul_sub, mul_one, mul_comm (((x⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v), h2]
  rw [heq, map_mul, hz, one_mul, Valuation.map_sub_swap]
end PI.AlgValsFin.W
