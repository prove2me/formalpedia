-- Prove2me | solution 1 for PI.VolStabW.VolAAW.cT_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:58:36.429478+00:00
-- url     : https://prove2.me/submissions/d8182627-cc6f-4e78-a0eb-5824b99d717c

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
theorem _root_.solution {a M : ℕ} (c : Fin a × Fin M × Fin d → Fv F v) :
    ∃ Y : Fin a → Fin M → Fv F v ⊗[F] E, cT b v Y = c := by
  refine ⟨fun p i => (Algebra.TensorProduct.basis (Fv F v) b).equivFun.symm
    (fun k => c (p, i, k)), ?_⟩
  funext q
  obtain ⟨p, i, k⟩ := q
  simp only [cT, crd]
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
end PI.VolStabW.VolAAW
