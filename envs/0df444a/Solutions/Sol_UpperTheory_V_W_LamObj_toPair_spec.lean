-- Prove2me | solution 1 for UpperTheory.V.W.LamObj.toPair_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:35:38.92638+00:00
-- url     : https://prove2.me/submissions/09975b0f-8b30-46fd-93d5-d883f00005c8

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
namespace UpperTheory.V.W
namespace LamObj
theorem _root_.solution (Λ : LamObj r) {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (p : Pair r R) (v : F.Vl)
    (i : Fin n) : pushCh (Λ.toPair p : Λ.Λ →+* R) (Λ.κ v i) = (p.ψ v i).comp (F.Iv v).subtype :=
  (Λ.univ R (fun v i => (p.ψ v i).comp (F.Iv v).subtype) fun v i => ⟨_, p.psi v i, rfl⟩).choose_spec.1 v i
end LamObj
end UpperTheory.V.W
