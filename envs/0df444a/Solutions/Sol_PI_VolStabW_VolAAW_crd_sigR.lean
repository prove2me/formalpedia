-- Prove2me | solution 1 for PI.VolStabW.VolAAW.crd_sigR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:58:41.832529+00:00
-- url     : https://prove2.me/submissions/d0da7767-768c-44af-ad49-8c9f3429b0dd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensVolB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensVolC

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
  (b : Module.Basis (Fin d) F E) [FiniteDimensional F E] (v : HeightOneSpectrum (𝓞 F))
namespace PI.VolStabW.VolAAW
theorem _root_.solution (σ : E →ₐ[F] E) (z : Fv F v ⊗[F] E) (l : Fin d) :
    crd b (Fv F v) (sigR (Fv F v) σ z) l =
      ∑ k, crd b (Fv F v) z k * algebraMap F (Fv F v) (b.repr (σ (b k)) l) := by
  set B := Algebra.TensorProduct.basis (Fv F v) b with hBdef
  have hB : ∀ k, B k = (1 : Fv F v) ⊗ₜ[F] b k := fun k => Algebra.TensorProduct.basis_apply _ _
  have hs : ∀ k, sigR (Fv F v) σ ((1 : Fv F v) ⊗ₜ[F] b k) = (1 : Fv F v) ⊗ₜ[F] σ (b k) := by
    intro k
    simp [sigR]
  conv_lhs => rw [← B.sum_repr z]
  rw [map_sum]
  simp only [sigR_smul, hB, hs, crd, map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul, Algebra.TensorProduct.basis_repr_tmul,
    Finsupp.mapRange_apply, one_smul]
  rfl
end PI.VolStabW.VolAAW
