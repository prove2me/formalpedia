-- Prove2me | solution 1 for PI.VolStabW.TensAllW.linIndep_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:41:37.279994+00:00
-- url     : https://prove2.me/submissions/699879ae-314d-45da-b3d8-079342970522

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibOfTens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensAll
import Theorems.Thm_PI_VolStabW_TensAllW_wMat_mulVec_eq_zero

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
open PI.VolStabW.TensAllW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW PositiveNearLattice Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
namespace PI.VolStabW.TensAllW
theorem _root_.solution (R : Type) [CommRing R] [Algebra F R] {a M : ℕ}
    (X : Fin a → Fin M → R ⊗[F] E) :
    LinearIndependent (R ⊗[F] E) X ↔ ∀ c, wMat b R X *ᵥ c = 0 → c = 0 := by
  set B := Algebra.TensorProduct.basis R b with hB
  have hBk : ∀ k, B k = (1 : R) ⊗ₜ[F] b k := fun k => Algebra.TensorProduct.basis_apply _ _
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro hX c hc
    rw [wMat_mulVec_eq_zero] at hc
    have h0 := hX (fun i => ∑ k, c (i, k) • ((1 : R) ⊗ₜ[F] b k)) (by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      exact hc j)
    funext p
    have h1 := h0 p.1
    have h2 : B.equivFun (∑ k, c (p.1, k) • B k) = fun k => c (p.1, k) := by
      rw [← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
    simp only [hBk] at h2
    rw [h1, map_zero] at h2
    exact (congrFun h2 p.2).symm
  · intro hW g hg i
    have hc := hW (fun p => B.repr (g p.1) p.2) (by
      rw [wMat_mulVec_eq_zero]
      intro j
      have e : ∀ i, ∑ k, B.repr (g i) k • ((1 : R) ⊗ₜ[F] b k) = g i := by
        intro i
        simp only [← hBk]
        exact B.sum_repr (g i)
      simp only [e]
      have := congrFun hg j
      simpa [Finset.sum_apply, smul_eq_mul] using this)
    rw [← B.sum_repr (g i)]
    simp [fun k => congrFun hc (i, k)]
end PI.VolStabW.TensAllW
