-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isIntegralElem_coneMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:51:30.3798+00:00
-- url     : https://prove2.me/submissions/dd762c41-269f-4599-9a20-c3f866b592ea

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_StepTStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemSec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_StepTStB

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {Ω : Type*} [Field Ω] [CharZero Ω] {J : Type} [Fintype J] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (v : J → Ω) (e : Fin (D + 1) → J) (hf : IsProjFrame v e)
    (q : MvPolynomial J ℤ) :
    (coneMap ℤ (v ∘ e) : MvPolynomial (Fin (D + 1)) ℤ →+* Polynomial Ω).IsIntegralElem
      (coneMap ℤ v q) := by
  have hinj : Function.Injective (coneMap ℤ (v ∘ e)) := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    have : p ∈ coordIdeal ℤ (v ∘ e) := by simpa [coordIdeal, RingHom.mem_ker] using hp
    rw [hf.free] at this
    exact (Ideal.mem_bot).mp this
  set φ := AlgEquiv.ofInjective (coneMap ℤ (v ∘ e)) hinj
  have hgen : ∀ i, (coneMap ℤ (v ∘ e) : MvPolynomial (Fin (D + 1)) ℤ →+* Polynomial Ω).IsIntegralElem
      (Polynomial.C (v i) * Polynomial.X) := by
    intro i
    have hi : IsIntegral (coneMap ℤ (v ∘ e)).range (Polynomial.C (v i) * Polynomial.X : Polynomial Ω) :=
      hf.integral i
    obtain ⟨p, hp, hps⟩ := hi
    refine ⟨p.map φ.symm.toRingEquiv.toRingHom,
      hp.map _, ?_⟩
    have hcomp : ((coneMap ℤ (v ∘ e) : MvPolynomial (Fin (D + 1)) ℤ →+* Polynomial Ω).comp
        φ.symm.toRingEquiv.toRingHom) = algebraMap (coneMap ℤ (v ∘ e)).range (Polynomial Ω) := by
      refine RingHom.ext fun r => ?_
      have h1 : ((φ (φ.symm r) : (coneMap ℤ (v ∘ e)).range) : Polynomial Ω) =
          coneMap ℤ (v ∘ e) (φ.symm r) := rfl
      rw [AlgEquiv.apply_symm_apply] at h1
      exact h1.symm
    rw [Polynomial.eval₂_map, hcomp]
    exact hps
  induction q using MvPolynomial.induction_on with
  | C a =>
    have : coneMap ℤ v (C a) = coneMap ℤ (v ∘ e) (C a) := by simp
    rw [this]
    exact RingHom.isIntegralElem_map _
  | add p q hp hq =>
    rw [map_add]
    exact RingHom.IsIntegralElem.add _ hp hq
  | mul_X p i hp =>
    rw [map_mul]
    refine RingHom.IsIntegralElem.mul _ hp ?_
    simpa [coneMap] using hgen i
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
