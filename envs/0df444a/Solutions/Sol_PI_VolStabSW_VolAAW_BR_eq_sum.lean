-- Prove2me | solution 1 for PI.VolStabSW.VolAAW.BR_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:50:34.840427+00:00
-- url     : https://prove2.me/submissions/0857f1a1-5b68-41ee-b2e5-4f790d43ec51

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensVolA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensVolB
import Theorems.Thm_PI_VolStabSW_VolAAW_BR_eT_left
import Theorems.Thm_PI_VolStabSW_SdDualW_BR_expand


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open PI.VolStabSW.VolAAW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW
  PositiveNearLattice SdDualW
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E)
variable [FiniteDimensional F E] (v : HeightOneSpectrum (𝓞 F))
namespace PI.VolStabSW.VolAAW
theorem _root_.solution (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X Y : Fin a → Fin M → Fv F v ⊗[F] E) :
    BR (Fv F v) σ J X Y =
      ∑ q, cT b v X q * ((gG b σ J a).map (algebraMap F (Fv F v))).mulVec (cT b v Y) q := by
  rw [BR_expand v b σ J X Y]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [BR_eT_left]
  rfl
end PI.VolStabSW.VolAAW
