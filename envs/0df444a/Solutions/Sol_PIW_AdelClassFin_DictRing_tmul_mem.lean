-- Prove2me | solution 1 for PIW.AdelClassFin.DictRing.tmul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:33:32.660796+00:00
-- url     : https://prove2.me/submissions/f65b9d03-df7e-45ee-89e3-7e61a2807975

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StrongApproximation_DedekindLFunctions
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField IsDedekindDomain
open scoped TensorProduct Matrix
open PIW.AdelClassFin.DictRing
variable {F : Type} [Field F] [NumberField F]
variable {E : Type} [Field E] [NumberField E] [Algebra F E]
namespace PIW.AdelClassFin.DictRing
theorem _root_.solution {x : E} (hx : x ∈ Formalism.UG.intOE E) {y : Af F} (hy : y ∈ Formalism.UG.intAd F) :
    x ⊗ₜ[F] y ∈ IntAf F E := by
  have h1 : x ⊗ₜ[F] (1 : Af F) ∈ IntAf F E := Subring.subset_closure (Or.inl ⟨⟨x, hx⟩, rfl⟩)
  have h2 : (1 : E) ⊗ₜ[F] y ∈ IntAf F E := Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)
  have h3 := mul_mem h1 h2
  rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at h3
end PIW.AdelClassFin.DictRing
