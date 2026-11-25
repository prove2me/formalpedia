-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.matGL_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:55:30.933994+00:00
-- url     : https://prove2.me/submissions/160daef6-4ff3-4afd-9879-579dcdff01f4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_EquivFunLinOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_CardStepOf
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_linOf_matGL
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_gram_linOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {E V : Type} [Field E] [StarRing E] [AddCommGroup V] [Module E V]
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution {F : Type} [Field F] [Algebra F E] (σ : E →ₐ[F] E) (hσ : ∀ a, σ a = star a)
    (h : V →ₗ⋆[E] V →ₗ[E] E) {M : ℕ} (b : Module.Basis (Fin M) E V) {u : V ≃ₗ[E] V} (hu : u ∈ isom h) :
    matGL b u ∈ UJ (σ : E →+* E) (gramOf h b) := by
  show cT (σ : E →+* E) ((matGL b u : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) * gramOf h b *
    ((matGL b u : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) = gramOf h b
  ext i j
  rw [← gram_linOf σ hσ h b, linOf_matGL]
  exact hu (b i) (b j)
end PI.UnitaryGroupMassFormula.UJClassMass
