-- Prove2me | solution 1 for PI.VolStabW.VolAAW.mulVec_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:06:27.572817+00:00
-- url     : https://prove2.me/submissions/18b3802e-7ff9-44da-bf4f-b303bdb9be6f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensVolA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensVolB

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
  (b : Module.Basis (Fin d) F E)
variable [FiniteDimensional F E] (v : HeightOneSpectrum (𝓞 F))
namespace PI.VolStabW.VolAAW
theorem _root_.solution {ι : Type} [Fintype ι] (A : Matrix ι ι F)
    (hA : ∀ i j, algebraMap F (Fv F v) (A i j) ∈ v.adicCompletionIntegers F)
    (w : ι → Fv F v) (hw : ∀ i, w i ∈ v.adicCompletionIntegers F) (i : ι) :
    (A.map (algebraMap F (Fv F v))).mulVec w i ∈ v.adicCompletionIntegers F := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  exact sum_mem fun j _ => mul_mem (hA i j) (hw j)
end PI.VolStabW.VolAAW
