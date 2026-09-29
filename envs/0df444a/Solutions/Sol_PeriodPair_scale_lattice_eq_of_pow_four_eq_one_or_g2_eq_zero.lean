-- Prove2me | solution 1 for PeriodPair.scale_lattice_eq_of_pow_four_eq_one_or_g2_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/15c3e521-692f-57ef-9a95-e3b5ac40f557

import Mathlib
import Definitions.Def_PeriodPair_Uniformization
import Theorems.Thm_PeriodPair_lattice_eq_of_g2_eq_of_g3_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PeriodPair_scale_lattice_eq_of_pow_four_eq_one_or_g2_eq_zero

set_option autoImplicit false

noncomputable section

namespace PeriodPair
p2m_export "PeriodPair" "lattice ω₁ latticeEquivProd g₃ ω₂ latticeEquiv_symm_apply G g₂ scale scale_ω₁ scale_ω₂ lattice_eq_of_g2_eq_of_g3_eq"
namespace ScaleUnits
p2m_open "PeriodPair"

p2m_open "PeriodPair P2MW.S_PeriodPair_scale_lattice_eq_of_pow_four_eq_one_or_g2_eq_zero.PeriodPair"

theorem G_scale (L : PeriodPair) (α : ℂˣ) (k : ℕ) :
    (L.scale α).G k = ((α : ℂ) ^ k)⁻¹ * L.G k := by
  rw [PeriodPair.G, PeriodPair.G, ← (L.scale α).latticeEquivProd.symm.toEquiv.tsum_eq,
    ← L.latticeEquivProd.symm.toEquiv.tsum_eq, ← tsum_mul_left]
  congr 1 with p
  simp only [LinearEquiv.coe_toEquiv, latticeEquiv_symm_apply, scale_ω₁, scale_ω₂]
  rw [show (p.1 : ℂ) * (α * L.ω₁) + p.2 * (α * L.ω₂) = α * (p.1 * L.ω₁ + p.2 * L.ω₂) by ring,
    mul_pow, mul_inv]

theorem g₂_scale (L : PeriodPair) (α : ℂˣ) : (L.scale α).g₂ = ((α : ℂ) ^ 4)⁻¹ * L.g₂ := by
  rw [PeriodPair.g₂, PeriodPair.g₂, G_scale]; ring

theorem g₃_scale (L : PeriodPair) (α : ℂˣ) : (L.scale α).g₃ = ((α : ℂ) ^ 6)⁻¹ * L.g₃ := by
  rw [PeriodPair.g₃, PeriodPair.g₃, G_scale]; ring

end PeriodPair.ScaleUnits

open PeriodPair.ScaleUnits in
theorem solution (L : PeriodPair) (α : ℂˣ)
    (h₂ : (α : ℂ) ^ 4 = 1 ∨ L.g₂ = 0) (h₃ : (α : ℂ) ^ 6 = 1 ∨ L.g₃ = 0) :
    (L.scale α).lattice = L.lattice := by
  apply PeriodPair.lattice_eq_of_g2_eq_of_g3_eq
  · rw [g₂_scale]
    rcases h₂ with h | h
    · rw [h, inv_one, one_mul]
    · rw [h, mul_zero]
  · rw [g₃_scale]
    rcases h₃ with h | h
    · rw [h, inv_one, one_mul]
    · rw [h, mul_zero]

end
end S_PeriodPair_scale_lattice_eq_of_pow_four_eq_one_or_g2_eq_zero
end P2MW
export P2MW.S_PeriodPair_scale_lattice_eq_of_pow_four_eq_one_or_g2_eq_zero (solution)
