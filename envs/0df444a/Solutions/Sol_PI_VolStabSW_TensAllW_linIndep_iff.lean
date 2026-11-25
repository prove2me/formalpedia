-- Prove2me | solution 1 for PI.VolStabSW.TensAllW.linIndep_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:31:45.492319+00:00
-- url     : https://prove2.me/submissions/100312e6-0dbb-4407-8cad-e02c2b530f91

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibOfTens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensAll
import Theorems.Thm_PI_VolStabSW_TensAllW_wMat_mulVec_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open PI.VolStabSW.TensAllW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW PositiveNearLattice Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
namespace PI.VolStabSW.TensAllW
theorem _root_.solution (R : Type) [CommRing R] [Algebra F R] {a M : ℕ}
    (X : Fin a → Fin M → R ⊗[F] E) :
    LinearIndependent (R ⊗[F] E) X ↔ ∀ c, wMat b R X *ᵥ c = 0 → c = 0 := by
  have hexp : ∀ y : R ⊗[F] E, ∑ k, crd b R y k • ((1 : R) ⊗ₜ[F] b k) = y := by
    intro y
    have hs := (Algebra.TensorProduct.basis R b).sum_repr y
    simpa only [crd, Algebra.TensorProduct.basis_apply] using hs
  have hcrd : ∀ (g : Fin d → R) (l : Fin d), crd b R (∑ k, g k • ((1 : R) ⊗ₜ[F] b k)) l = g l := by
    intro g l
    have hb : ∀ k, ((1 : R) ⊗ₜ[F] b k) = Algebra.TensorProduct.basis R b k := fun k =>
      (Algebra.TensorProduct.basis_apply b k).symm
    simp only [crd, hb, map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finset_sum,
      Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h c hc
    rw [wMat_mulVec_eq_zero] at hc
    have hg := h (fun i => ∑ k, c (i, k) • ((1 : R) ⊗ₜ[F] b k)) (by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      exact hc j)
    funext q
    obtain ⟨i, k⟩ := q
    have hk := congrArg (fun y => crd b R y k) (hg i)
    rw [hcrd] at hk
    simpa [crd] using hk
  · intro h g hg i
    have hc := h (fun q => crd b R (g q.1) q.2) (by
      rw [wMat_mulVec_eq_zero]
      intro j
      have hj := congr_fun hg j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hj
      rw [← hj]
      refine Finset.sum_congr rfl fun i _ => ?_
      show (∑ k, crd b R (g i) k • ((1 : R) ⊗ₜ[F] b k)) * X i j = g i * X i j
      rw [hexp])
    rw [← hexp (g i)]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hk := congr_fun hc (i, k)
    simp only [Pi.zero_apply] at hk
    rw [hk, zero_smul]
end PI.VolStabSW.TensAllW
