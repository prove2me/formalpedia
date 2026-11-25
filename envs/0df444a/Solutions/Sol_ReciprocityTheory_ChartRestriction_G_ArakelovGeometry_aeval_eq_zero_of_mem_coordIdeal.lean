-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.aeval_eq_zero_of_mem_coordIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:40:13.453839+00:00
-- url     : https://prove2.me/submissions/10e01172-2080-4eb5-9023-cd029ca38ab5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsBergDensity
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Jacobson.Ring
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeStB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial TensorProduct
variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {x : J → Ω} {f : MvPolynomial J ℤ}
    (hf : f ∈ coordIdeal ℤ x) : aeval x f = 0 := by
  have h0 : (aeval fun i => Polynomial.C (x i) * Polynomial.X : MvPolynomial J ℤ →ₐ[ℤ] Polynomial Ω) f = 0 :=
    RingHom.mem_ker.1 hf
  have h1 := MvPolynomial.comp_aeval_apply (fun i => Polynomial.C (x i) * Polynomial.X)
    ((Polynomial.aeval (1 : Ω)).restrictScalars ℤ) f
  rw [h0, map_zero] at h1
  simpa using h1.symm
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
