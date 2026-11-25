-- Prove2me | solution 1 for PI.VolStabW.VolAAW.ev_sig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:16:39.930913+00:00
-- url     : https://prove2.me/submissions/81f75ce5-451f-465a-99c9-56a98bced7b8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensVolB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensVolC
import Theorems.Thm_PI_VolStabW_VolAAW_crd_sigR
import Theorems.Thm_PI_VolStabW_VolAAW_ev_int_all


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
open PI.VolStabW.VolAAW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW
  PositiveNearLattice SdDualW
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) [FiniteDimensional F E] (v : HeightOneSpectrum (𝓞 F))
namespace PI.VolStabW.VolAAW
theorem _root_.solution (σ : E →ₐ[F] E) :
    ∀ᶠ v in cofinite, ∀ z ∈ latA v b, sigR (Fv F v) σ z ∈ latA v b := by
  filter_upwards [ev_int_all (fun q : Fin d × Fin d => b.repr (σ (b q.1)) q.2)] with v h
  intro z hz l
  rw [crd_sigR]
  exact sum_mem fun k _ => mul_mem (hz k) (h (k, l))
end PI.VolStabW.VolAAW
