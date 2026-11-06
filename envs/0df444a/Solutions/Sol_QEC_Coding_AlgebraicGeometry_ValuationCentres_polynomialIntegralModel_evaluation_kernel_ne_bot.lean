-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.ValuationCentres.polynomialIntegralModel_evaluation_kernel_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:25:58.224199+00:00
-- url     : https://prove2.me/submissions/7b51fd0e-bc43-417f-91e7-6a396edaf95e

import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.AlgebraicGeometry.StructureSheaf
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ValuationCentres

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.ValuationCentres
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.ValuationCentres
theorem _root_.solution
    {k K : Type*} [Field k] [Field K] [Algebra (Polynomial k) K]
    (hi : Function.Injective (algebraMap (Polynomial k) K))
    (e : integralClosure (Polynomial k) K →+* k)
    (hc : ∀ c : k, e ⟨algebraMap (Polynomial k) K (Polynomial.C c),
      isIntegral_algebraMap⟩ = c) : RingHom.ker e ≠ ⊥ := by
  let z : integralClosure (Polynomial k) K :=
    ⟨algebraMap (Polynomial k) K Polynomial.X,isIntegral_algebraMap⟩
  let c : k := e z
  let a : integralClosure (Polynomial k) K :=
    ⟨algebraMap (Polynomial k) K (Polynomial.C c),isIntegral_algebraMap⟩
  have hza : z-a ≠ 0 := by
    intro h
    have hv := congrArg Subtype.val h
    change algebraMap (Polynomial k) K Polynomial.X -
      algebraMap (Polynomial k) K (Polynomial.C c) = 0 at hv
    exact Polynomial.X_ne_C c (hi (sub_eq_zero.mp hv))
  have hm : z-a ∈ RingHom.ker e := by
    change e (z-a) = 0
    rw [map_sub,hc]
    exact sub_self _
  intro hbot
  rw [hbot,Ideal.mem_bot] at hm
  exact hza hm
end QEC.Coding.AlgebraicGeometry.ValuationCentres
