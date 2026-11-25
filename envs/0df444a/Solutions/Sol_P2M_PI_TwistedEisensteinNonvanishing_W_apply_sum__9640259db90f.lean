-- Prove2me | solution 1 for P2M_PI_TwistedEisensteinNonvanishing_W_apply_sum__9640259db90f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:47:55.377531+00:00
-- url     : https://prove2.me/submissions/d948bcca-3ff8-4c0f-a7d0-fd70d5d4d42c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IsUnitRedP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_JacobianTransformationLaw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE
variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {N : ℕ} (f : Sp E N ≃ₗ[E] Sp E N) (v : Sp E N) (i : Fin N) :
    f v i = ∑ m : Fin N, v m * f (eN E N m.1) i := by
  have hv : v = ∑ m : Fin N, v m • eN E N m.1 := by
    funext l
    simp [eN, Finset.sum_apply, Fin.val_inj]
  conv_lhs => rw [hv]
  rw [map_sum]
  simp [Finset.sum_apply, map_smul]
end PI.TwistedEisensteinNonvanishing.W
