-- Prove2me | solution 1 for PI.LocGlobInclWork.smul_mem_idealSmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:00:37.407463+00:00
-- url     : https://prove2.me/submissions/2cc111ef-dd97-4d14-91fe-1e58f4c455fe

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocGlobIncl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalGlobalInclusion_SmulMemIdealSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.LocGlobInclWork
variable {K : Type} [Field K] [NumberField K]
variable [StarRing K] {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
  [IsScalarTower (𝓞 K) K W]
namespace PI.LocGlobInclWork
theorem _root_.solution (I J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (B : Submodule (𝓞 K) W) (t : 𝓞 K) (ht : algebraMap (𝓞 K) K t ∈ J) {y : W}
    (hy : y ∈ Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) B) :
    t • y ∈ Formalism.HermitianLatticesTheory.idealSmul ((I * J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
      Submodule (𝓞 K) K) B := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨c, hc, b, hb, rfl⟩ := hz
    apply Submodule.subset_span
    refine ⟨c * algebraMap (𝓞 K) K t, FractionalIdeal.mul_mem_mul hc ht, b, hb, ?_⟩
    rw [← smul_assoc, Algebra.smul_def, mul_comm]
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
  | smul r y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ r hy
end PI.LocGlobInclWork
