-- Prove2me | solution 1 for PI.VolStabW.LatFactsW.smul_mem_latSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:56:52.399495+00:00
-- url     : https://prove2.me/submissions/c2a906ab-7900-4434-9a75-f90f5d5cb45b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHL

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
open PI.VolStabW.LatFactsW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
namespace PI.VolStabW.LatFactsW
theorem _root_.solution {a M : ℕ} {s : Fv F v} (hs : s ∈ v.adicCompletionIntegers F)
    {x : Fin a → Fin M → Fv F v ⊗[F] E} (hx : x ∈ latSub b v a M) : s • x ∈ latSub b v a M := by
  have hx' : ∀ i j k, (Algebra.TensorProduct.basis (Fv F v) b).repr (x i j) k ∈
      v.adicCompletionIntegers F := hx
  show ∀ i j k, (Algebra.TensorProduct.basis (Fv F v) b).repr ((s • x) i j) k ∈
      v.adicCompletionIntegers F
  intro i j k
  simp only [Pi.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact mul_mem hs (hx' i j k)
end PI.VolStabW.LatFactsW
