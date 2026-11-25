-- Prove2me | solution 1 for PIW.AdelicOrbitU.quad_sig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:22:12.325037+00:00
-- url     : https://prove2.me/submissions/e659f6cc-4172-4d18-8403-d9e5b25fc742

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdelicOrbitU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_QuadFiniteDimensional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PIW.AdelicOrbitU
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
section Field
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
end Field
section Ring
variable {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
  (h2 : Module.finrank F E = 2) {θ : E} (hli : LinearIndependent F ![(1 : E), θ])
  (R : Type) [CommRing R] [Algebra F R]
private lemma sigR_tmul_adelic_unitary_orbits (x : R) (y : E) : sigR R σ (x ⊗ₜ[F] y) = x ⊗ₜ[F] σ y := by
  first
  | rfl
  | simp [sigR]
  | (unfold sigR; simp)
end Ring
end PIW.AdelicOrbitU
end
end

set_option autoImplicit false
noncomputable section
open PIW PIW.AdelicOrbitU
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
variable {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
  (h2 : Module.finrank F E = 2) {θ : E} (hli : LinearIndependent F ![(1 : E), θ])
  (R : Type) [CommRing R] [Algebra F R]
namespace PIW.AdelicOrbitU
theorem _root_.solution (hσθ : σ θ = -θ) (a b : R) :
    sigR R σ (a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] θ) = a ⊗ₜ[F] (1 : E) + (-b) ⊗ₜ[F] θ := by
  rw [map_add, sigR_tmul_adelic_unitary_orbits, sigR_tmul_adelic_unitary_orbits, map_one, hσθ, TensorProduct.tmul_neg,
    TensorProduct.neg_tmul]
end PIW.AdelicOrbitU
