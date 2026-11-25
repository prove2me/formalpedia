-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_expS_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:55:50.333829+00:00
-- url     : https://prove2.me/submissions/9c82154f-86ee-4d3d-b3de-2550beac4be9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {k : Type} [CommRing k] {d : ℕ}
section Exp
variable [Algebra ℚ k]
private theorem coeff_mul_eq_zero_of_order_two_of_degree_le_two {n : ℕ} (f g : PS k n d)
    (hf : ∀ m : Fin n × Fin d →₀ ℕ, m.degree < 2 → coeff m f = 0)
    (hg : ∀ m : Fin n × Fin d →₀ ℕ, m.degree < 2 → coeff m g = 0)
    (m : Fin n × Fin d →₀ ℕ) (hm : m.degree ≤ 2) : coeff m (f * g) = 0 := by
  classical
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have hdeg : p.1.degree + p.2.degree = m.degree := by rw [← hp, map_add]
  by_cases h1 : p.1.degree < 2
  · rw [hf _ h1, zero_mul]
  · rw [hg _ (by omega), mul_zero]
private theorem coeff_mul_eq_zero_of_left_vanishes_degree_le_two {n : ℕ} (F g : PS k n d)
    (hF : ∀ m : Fin n × Fin d →₀ ℕ, m.degree ≤ 2 → coeff m F = 0)
    (m : Fin n × Fin d →₀ ℕ) (hm : m.degree ≤ 2) : coeff m (F * g) = 0 := by
  classical
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have hdeg : p.1.degree + p.2.degree = m.degree := by rw [← hp, map_add]
  rw [hF _ (by omega), zero_mul]
end Exp
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {k : Type} [CommRing k] {d : ℕ}
variable [Algebra ℚ k]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution {n : ℕ} (f : PS k n d) (hf : ∀ m : Fin n × Fin d →₀ ℕ, m.degree < 2 → coeff m f = 0)
    (m : Fin n × Fin d →₀ ℕ) (hm : m.degree = 2) : coeff m (FB.expS k f) = coeff m f := by
  classical
  have haS : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero
    (by rw [← coeff_zero_eq_constantCoeff_apply]; exact hf 0 (by simp))
  show coeff m (PowerSeries.subst f (PowerSeries.exp k)) = _
  rw [PowerSeries.coeff_subst haS, finsum_eq_single _ 1]
  · simp [PowerSeries.coeff_exp]
  · intro j hj
    rcases j with _ | _ | j
    · have hm0 : m ≠ 0 := by
        rintro rfl
        simp at hm
      simp [hm0, coeff_one]
    · exact absurd rfl hj
    · rw [show f ^ (j + 2) = f * f * f ^ j by ring,
        coeff_mul_eq_zero_of_left_vanishes_degree_le_two (f * f) _ (fun q hq => coeff_mul_eq_zero_of_order_two_of_degree_le_two f f hf hf q hq) m hm.le,
        smul_zero]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
