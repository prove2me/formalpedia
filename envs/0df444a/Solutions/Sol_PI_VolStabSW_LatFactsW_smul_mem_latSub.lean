-- Prove2me | solution 1 for PI.VolStabSW.LatFactsW.smul_mem_latSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:04:32.410835+00:00
-- url     : https://prove2.me/submissions/8ef190ae-ed1e-44f2-8c7c-a5a53b70c46a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensHL

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
open PI.VolStabSW.LatFactsW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
namespace PI.VolStabSW.LatFactsW
theorem _root_.solution {a M : ℕ} {s : Fv F v} (hs : s ∈ v.adicCompletionIntegers F)
    {x : Fin a → Fin M → Fv F v ⊗[F] E} (hx : x ∈ latSub b v a M) : s • x ∈ latSub b v a M := by
  have hx' : x ∈ latV (M := M) (n := a) b v := hx
  show s • x ∈ latV (M := M) (n := a) b v
  simp only [latV, Set.mem_setOf_eq] at hx' ⊢
  intro i j k
  simp only [Pi.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact mul_mem hs (hx' i j k)
end PI.VolStabSW.LatFactsW
