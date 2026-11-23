-- Prove2me | solution 1 for PI.VolStabW.SdDualW.BR_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:12.956925+00:00
-- url     : https://prove2.me/submissions/b587150b-6091-4a17-a5fd-0f006b9b558c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdDual
import Theorems.Thm_PI_VolStabW_SdDualW_sum_eT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open PI.VolStabW.SdDualW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW PositiveNearLattice SdUniqW
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable {E : Type} [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
variable [FiniteDimensional F E] (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E)
namespace PI.VolStabW.SdDualW
theorem _root_.solution (X Y : Fin a → Fin M → Fv F v ⊗[F] E) :
    BR (Fv F v) σ J X Y =
      ∑ q : Fin a × Fin M × Fin d, crd b (Fv F v) (X q.1 q.2.1) q.2.2 * BR (Fv F v) σ J (eT v b q) Y := by
  have h := congrArg (brL v σ J Y) (sum_eT v b X)
  simp only [map_sum, map_smul, smul_eq_mul] at h
  exact h
end PI.VolStabW.SdDualW
