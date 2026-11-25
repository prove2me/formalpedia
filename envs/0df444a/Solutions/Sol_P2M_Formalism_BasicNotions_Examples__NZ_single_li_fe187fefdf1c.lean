-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_single_li_fe187fefdf1c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:32:41.380516+00:00
-- url     : https://prove2.me/submissions/ac2926f5-af7b-47a8-b163-8a2056caccd3

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_BasisOfBasisF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open scoped TensorProduct nonZeroDivisors
variable (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B]
  [Algebra.IsIntegral A B]
variable (ι : Type) [Fintype ι] [DecidableEq ι]
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution (hB : Function.Injective (algebraMap B (FractionRing B))) :
    LinearIndependent B (fun a : ι => (Pi.single a 1 : ι → FractionRing B)) := by
  have h := (Pi.basisFun (FractionRing B) ι).linearIndependent
  have h2 := h.restrict_scalars (R := B) (by
    intro x y hxy
    simpa [Algebra.smul_def] using hB (by simpa [Algebra.smul_def] using hxy))
  have e : (fun a : ι => (Pi.single a 1 : ι → FractionRing B)) = ⇑(Pi.basisFun (FractionRing B) ι) :=
    funext fun a => (Pi.basisFun_apply _ _ a).symm
  rw [e]; exact h2
end Formalism.BasicNotions.Examples₂.NZ
