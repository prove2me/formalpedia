-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.quadratic_column_derivative
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:33:53.748464+00:00
-- url     : https://prove2.me/submissions/d7b0b084-3f96-45f8-a6c4-fa344c2d6a01

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_KillAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_KillAddQ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace ReciprocityTheory.ChartRestriction.G.TB
private theorem pderiv_X_eq_C_ite {k : Type} [CommRing k] {n d : ℕ} (p q : Fin n × Fin d) :
    pderiv k p (X q : PS k n d) = C (if q = p then (1 : k) else 0) := by
  classical
  rw [MvPowerSeries.pderiv_X, Pi.single_apply]
  split_ifs <;> simp
private theorem pderiv_C_mul' {k : Type} [CommRing k] {n d : ℕ} (p : Fin n × Fin d) (a : k)
    (Y : PS k n d) : pderiv k p (C a * Y) = C a * pderiv k p Y := by
  rw [Derivation.leibniz, MvPowerSeries.pderiv_C, smul_zero, add_zero, smul_eq_mul]
private theorem pderiv_C_mul_X_mul_X {k : Type} [CommRing k] {n d : ℕ} (p q r : Fin n × Fin d) (a : k) :
    pderiv k p (C a * X q * X r : PS k n d) =
      C (a * (if r = p then 1 else 0)) * X q + C (a * (if q = p then 1 else 0)) * X r := by
  rw [Derivation.leibniz, pderiv_C_mul', pderiv_X_eq_C_ite, pderiv_X_eq_C_ite, smul_eq_mul, smul_eq_mul,
    map_mul, map_mul]
  ring
private theorem sum_quadratic_column_indicator_eq_dotProduct_mulVec {k : Type} [CommRing k] {d n : ℕ} (β : Matrix (Fin d) (Fin d) k)
    (u v : Fin d → k) (b b' : Fin n) :
    (∑ m : Fin d, ∑ j : Fin d, ∑ c : Fin n, ∑ i : Fin d, ∑ l : Fin d,
      (u m * (v j * (β i l * (if ((c, l) : Fin n × Fin d) = (b', j) then 1 else 0)) *
          (if ((c, i) : Fin n × Fin d) = (b, m) then 1 else 0)) +
        u m * (v j * (β i l * (if ((c, i) : Fin n × Fin d) = (b', j) then 1 else 0)) *
          (if ((c, l) : Fin n × Fin d) = (b, m) then 1 else 0)))) =
      if b = b' then dotProduct u (β.mulVec v) + dotProduct v (β.mulVec u) else 0 := by
  by_cases hb : b = b'
  · subst hb
    simp only [Prod.mk.injEq, ite_and, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
      Finset.sum_add_distrib, if_true]
    simp [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  · rw [if_neg hb]
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ =>
      Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun l _ => ?_
    by_cases hc : c = b
    · subst hc
      simp [Prod.mk.injEq, hb]
    · simp [Prod.mk.injEq, hc]
end ReciprocityTheory.ChartRestriction.G.TB
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB
namespace ReciprocityTheory.ChartRestriction.G.TB
theorem _root_.solution : QuadColDerivSt := by
  intro k _ d n β
  classical
  refine ⟨?_, ?_, ?_⟩
  · simp [quadCol, map_sum]
  · intro u b
    simp only [dAdd, quadCol, map_sum, pderiv_C_mul_X_mul_X, pderiv_C_mul', map_add, map_mul,
      MvPowerSeries.constantCoeff_X, mul_zero, add_zero, Finset.sum_const_zero]
  · intro u v b b'

    simp only [dAdd, quadCol, map_sum, pderiv_C_mul_X_mul_X, pderiv_C_mul', map_add, Finset.mul_sum,
      mul_add, pderiv_X_eq_C_ite]
    simp only [← mul_assoc, ← map_mul]
    simp only [← map_add, ← map_sum]
    congr 1
    rw [← sum_quadratic_column_indicator_eq_dotProduct_mulVec β u v b b']
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun l _ => by ring
end ReciprocityTheory.ChartRestriction.G.TB
