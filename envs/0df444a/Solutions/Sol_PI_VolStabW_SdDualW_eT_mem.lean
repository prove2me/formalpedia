-- Prove2me | solution 1 for PI.VolStabW.SdDualW.eT_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:29:32.4638+00:00
-- url     : https://prove2.me/submissions/d886022d-f37b-487e-8351-ce711d43ef7f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdDual

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
open PI.VolStabW.SdDualW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW PositiveNearLattice SdUniqW
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable {E : Type} [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
variable [FiniteDimensional F E] (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E)
namespace PI.VolStabW.SdDualW
theorem _root_.solution (q : Fin a × Fin M × Fin d) : eT v b q ∈ latSub v b a M := by
  show ∀ p i l, (Algebra.TensorProduct.basis (Fv F v) b).repr (eT v b q p i) l ∈
    v.adicCompletionIntegers F
  intro p i l
  have hB : ∀ k, (Algebra.TensorProduct.basis (Fv F v) b) k = (1 : Fv F v) ⊗ₜ[F] b k :=
    fun k => Algebra.TensorProduct.basis_apply _ _
  by_cases h1 : p = q.1
  · subst h1
    by_cases h2 : i = q.2.1
    · subst h2
      simp only [eT, Pi.single_eq_same]
      rw [← hB, Module.Basis.repr_self, Finsupp.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · simp [eT, h2]
  · simp [eT, h1]
end PI.VolStabW.SdDualW
