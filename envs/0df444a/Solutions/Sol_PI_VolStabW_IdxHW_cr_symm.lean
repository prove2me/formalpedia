-- Prove2me | solution 1 for PI.VolStabW.IdxHW.cr_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:59:28.732082+00:00
-- url     : https://prove2.me/submissions/5c3879fe-645f-4c47-ad5e-bdbb8664f9b7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensIdxA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensIdxC

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
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  IsLocalRing
open PI.VolStabW.IdxHW
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (b : Module.Basis (Fin 2) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (a : ℕ)
namespace PI.VolStabW.IdxHW
theorem _root_.solution (f : Fin 2 → Fv F v) (k : Fin 2) :
    cr b v ((Algebra.TensorProduct.basis (Fv F v) b).equivFun.symm f) k = f k := by
  have : cr b v ((Algebra.TensorProduct.basis (Fv F v) b).equivFun.symm f) k =
      (Algebra.TensorProduct.basis (Fv F v) b).equivFun
        ((Algebra.TensorProduct.basis (Fv F v) b).equivFun.symm f) k := by
    simp [cr, Module.Basis.equivFun_apply]
  rw [this, LinearEquiv.apply_symm_apply]
end PI.VolStabW.IdxHW
