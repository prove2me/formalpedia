-- Prove2me | solution 1 for PI.VolStabW.AdmissibleCompactSupport.eventually_mem_latV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:06:18.021036+00:00
-- url     : https://prove2.me/submissions/915593b4-9886-4ff1-a45f-cf724d158f96

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_NuNeSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_AdmCpt
import Theorems.Thm_PI_VolStabW_AdmissibleCompactSupport_crd_projV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.AdmissibleCompactSupport
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open PI.VolStabW PI.VolStabW.PositiveNearLattice Set Filter
open scoped TensorProduct RestrictedProduct
variable {F : Type} [Field F] [NumberField F]
variable {E : Type} [Field E] [Algebra F E] [FiniteDimensional F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E)
namespace PI.VolStabW.AdmissibleCompactSupport
theorem _root_.solution {a M : ℕ} (Y : Fin a → Fin M → Af F ⊗[F] E) :
    ∀ᶠ v in cofinite, projV v Y ∈ latV b v := by
  have h : ∀ (i : Fin a) (j : Fin M) (k : Fin d), ∀ᶠ v in cofinite,
      (crd b (Af F) (Y i j) k) v ∈ v.adicCompletionIntegers F :=
    fun i j k => (crd b (Af F) (Y i j) k).2
  filter_upwards [eventually_all.2 fun i => eventually_all.2 fun j => eventually_all.2 fun k =>
    h i j k] with v hv
  intro i j k
  have := crd_projV b Y v i j k
  simp only [crd] at this
  rw [this]
  exact hv i j k
end PI.VolStabW.AdmissibleCompactSupport
