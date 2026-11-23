-- Prove2me | solution 1 for PI.ProdFormulaE.Base.trace_tower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:58:33.395832+00:00
-- url     : https://prove2.me/submissions/57ec4ccf-f6fe-48d9-b1f4-edf102bc12da

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ProdFormulaE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_BasisEApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField Formalism.MainNotions.S.Loc
open PI PI.ProdFormulaE PI.ProdFormulaE.Base
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}
namespace PI.ProdFormulaE.Base
theorem _root_.solution (L : LocAt F E sig p) (y : L.Ep) :
    (haveI := L.ellPrime
     letI := ((algebraMap L.Fp L.Ep).comp (algebraMap ℚ_[resChar p] L.Fp)).toAlgebra
     Algebra.trace ℚ_[resChar p] L.Ep y) =
    (haveI := L.ellPrime
     Algebra.trace ℚ_[resChar p] L.Fp (Algebra.trace L.Fp L.Ep y)) := by
  have := L.ellPrime
  let _ : Algebra ℚ_[resChar p] L.Ep :=
    ((algebraMap L.Fp L.Ep).comp (algebraMap ℚ_[resChar p] L.Fp)).toAlgebra
  have : IsScalarTower ℚ_[resChar p] L.Fp L.Ep := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := L.free
  have := finite L
  have := L.qlFin
  exact (Algebra.trace_trace (R := ℚ_[resChar p]) (S := L.Fp) (T := L.Ep) y).symm
end PI.ProdFormulaE.Base
