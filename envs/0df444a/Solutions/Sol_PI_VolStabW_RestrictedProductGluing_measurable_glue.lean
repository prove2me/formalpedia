-- Prove2me | solution 1 for PI.VolStabW.RestrictedProductGluing.measurable_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:16:46.788749+00:00
-- url     : https://prove2.me/submissions/3e14e12a-57f2-470f-90ec-b44ef0913810

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoPolish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RPGlue
import Theorems.Thm_PI_VolStabW_RestrictedProductGluing_measurable_crdA

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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Topology Filter
open scoped TensorProduct RestrictedProduct
open PI.VolStabW.RestrictedProductGluing
open PositiveNearLattice
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {M a d : ℕ} (b : Module.Basis (Fin d) F E)
namespace PI.VolStabW.RestrictedProductGluing
theorem _root_.solution :
    Measurable (glue (F := F) (E := E) (M := M) (a := a) b) := by
  have : BorelSpace (AF F) := ⟨rfl⟩
  have : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
  have hL : Continuous (Algebra.TensorProduct.basis (AF F) b).equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap
      ((Algebra.TensorProduct.basis (AF F) b).equivFun.symm.toLinearMap)
  exact measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
    hL.measurable.comp (measurable_pi_lambda _ fun k => measurable_crdA b i j k)
end PI.VolStabW.RestrictedProductGluing
