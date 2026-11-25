-- Prove2me | solution 1 for PI.VolStabW.RestrictedProductGluing.crd_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:57:29.897152+00:00
-- url     : https://prove2.me/submissions/f1e20e19-4bb0-4a68-ab4b-8e35ce33ee86

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoPolish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RPGlue

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
theorem _root_.solution (p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
    (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E)) (i : Fin a) (j : Fin M)
    (k : Fin d) : crd b (AF F) (glue b p i j) k = crdA b p i j k := by
  show (Algebra.TensorProduct.basis (AF F) b).repr
      ((Algebra.TensorProduct.basis (AF F) b).equivFun.symm fun k => crdA b p i j k) k = _
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
end PI.VolStabW.RestrictedProductGluing
