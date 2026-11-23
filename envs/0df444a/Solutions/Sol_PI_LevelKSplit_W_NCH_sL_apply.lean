-- Prove2me | solution 1 for PI.LevelKSplit.W.NCH.sL_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:30:37.450917+00:00
-- url     : https://prove2.me/submissions/0193cc47-fbd6-4deb-a53b-808fd38f8d96

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ReflectionFixesNormal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnipotentRadicalActionFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.LevelKSplit.W.NCH
open PI.VolSemiDirect.W.PG PI.VolSemiDirect.W.PG.Dat
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
private theorem hLap_lemma (D : Dat A n r) (x v : n → A) : D.hL x v = D.h x v := rfl
variable {D : Dat A n r}
section Sec
variable (H : D.Hyp) {half : A} {y : Fin r → n → A} (hy : ∀ a, IsWp D (y a))
include H hy
end Sec
end PI.LevelKSplit.W.NCH
end
end

set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCH
open PI.VolSemiDirect.W.PG PI.VolSemiDirect.W.PG.Dat
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
namespace PI.LevelKSplit.W.NCH
theorem _root_.solution (D : Dat A n r) (half : A) (y : Fin r → n → A) (v : n → A) :
    sL D half y v = v + ∑ a, D.h (D.e a) v • uv D half y a - ∑ b, D.h (y b) v • D.e b := by
  simp only [sL, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply,
    LinearMap.sum_apply, LinearMap.smulRight_apply, hLap_lemma]
end PI.LevelKSplit.W.NCH
