-- Prove2me | solution 1 for PI.VolStabW.SdDualW.smul_mem_latS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:06:59.687301+00:00
-- url     : https://prove2.me/submissions/0e98294d-fc3a-4324-8d07-3dd10d0b7c19

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdDual
import Theorems.Thm_PI_VolStabW_SdDualW_mem_latS
import Theorems.Thm_PI_VolStabW_SdDualW_smul_mem_latA

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
variable [FiniteDimensional F E]
namespace PI.VolStabW.SdDualW
theorem _root_.solution (σ : E →ₐ[F] E) {s : Fv F v} (hs : s ∈ v.adicCompletionIntegers F)
    {z : Fv F v ⊗[F] E} (hz : z ∈ latS v b σ) : s • z ∈ latS v b σ := by
  rw [mem_latS] at hz ⊢
  obtain ⟨x, hx, y, hy, rfl⟩ := hz
  exact ⟨s • x, smul_mem_latA v b hs hx, s • y, smul_mem_latA v b hs hy, by
    rw [smul_add, sigR_smul]⟩
end PI.VolStabW.SdDualW
