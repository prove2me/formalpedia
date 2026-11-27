-- Prove2me | solution 1 for UpperTheory.V.W.UniversalOrdinaryDeterminantRing.P3core.p2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:33:44.828365+00:00
-- url     : https://prove2.me/submissions/ffa6b467-3ee5-41da-a127-25983e1f9d05

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_WeilGroupCharacters_RepAlg
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_UnitaryThreeGroups_BaseRepGL3NormalisedOfPsiEqOne
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_WeilGroupCharacters_UniversalOrdinaryDeterminantRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing Matrix UpperTheory.V.Alg
open UpperTheory UpperTheory.V UpperTheory.V.W
attribute [instance] GFrame.grp GFrame.top GFrame.tgrp GFrame.cpt GFrame.tdisc GFrame.finV GFrame.gv GFrame.tv GFrame.tgv
  GFrame.cv GFrame.dv GFrame.finT
variable {l : ℕ} [Fact l.Prime]
variable {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} (r : Resid F O n)
attribute [instance] UniversalOrdinaryDeterminantRing.ring UniversalOrdinaryDeterminantRing.alg UniversalOrdinaryDeterminantRing.co
attribute [instance] LamObj.ring LamObj.alg LamObj.co
attribute [instance] Point.field Point.fin Point.algk Point.algO Point.tower
variable {r}
open UpperTheory.V.W.UniversalOrdinaryDeterminantRing
variable (B : UniversalOrdinaryDeterminantRing r)
variable (J : Ideal B.B)
namespace UpperTheory.V.W.UniversalOrdinaryDeterminantRing
namespace P3core
theorem _root_.solution {B : UniversalOrdinaryDeterminantRing r} {J : Ideal B.B} (H : B.P3core J) : B.P2core J := fun x f hx hf h₁ q hq hs =>
  H 0 (fun _ => x) (fun _ => f) Fin.elim0 (fun _ => hx) (fun _ => hf) (fun i => i.elim0) h₁ q hq hs
end P3core
end UpperTheory.V.W.UniversalOrdinaryDeterminantRing
