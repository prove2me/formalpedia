-- Prove2me | solution 1 for PI.VolStabW.repr_incl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:09:57.949403+00:00
-- url     : https://prove2.me/submissions/f66794ab-f594-4241-8091-218ef69e2262

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntRes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntL

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
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
variable {σ : E →ₐ[F] E} (A : AntiB F E σ)
namespace PI.VolStabW
theorem _root_.solution (e : E) (j : Fin 2) :
    (Algebra.TensorProduct.basis (Fv F v) A.c).repr (inclR (Fv F v) e) j =
      algebraMap F (Fv F v) (A.c.repr e j) := by
  show (Algebra.TensorProduct.basis (Fv F v) A.c).repr ((1 : Fv F v) ⊗ₜ e) j = _
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp
end PI.VolStabW
