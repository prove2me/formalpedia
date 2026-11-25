-- Prove2me | solution 1 for PIW.AdelicOrbitU.quad_sig_sig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:32:48.764703+00:00
-- url     : https://prove2.me/submissions/414def44-35d5-4360-a25d-ea929169de2b

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
theorem _root_.solution (hσσ : ∀ a : E, σ (σ a) = a) (z : R ⊗[F] E) : sigR R σ (sigR R σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul x y => rw [sigR_tmul_adelic_unitary_orbits, sigR_tmul_adelic_unitary_orbits, hσσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
end PIW.AdelicOrbitU
