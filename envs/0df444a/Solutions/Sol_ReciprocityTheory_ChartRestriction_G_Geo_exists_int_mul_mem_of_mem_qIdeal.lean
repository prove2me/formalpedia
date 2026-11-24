-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.exists_int_mul_mem_of_mem_qIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:19:52.396803+00:00
-- url     : https://prove2.me/submissions/ac80f606-d8ce-47d7-914a-292c2fc71091

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_exists_int_mul_eq_qmap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
variable {σ : Type}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (P : Ideal (MvPolynomial σ ℤ)) {g : MvPolynomial σ ℚ}
    (hg : g ∈ qIdeal P) :
    ∃ N : ℤ, N ≠ 0 ∧ ∃ h ∈ P, (N : MvPolynomial σ ℚ) * g = qmap h := by
  have hg' : g ∈ Submodule.span (MvPolynomial σ ℚ) (qmap '' (P : Set (MvPolynomial σ ℤ))) := hg
  clear hg
  induction hg' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, hh, rfl⟩ := hx
    exact ⟨1, one_ne_zero, h, hh, by simp⟩
  | zero => exact ⟨1, one_ne_zero, 0, P.zero_mem, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨N₁, hN₁, h₁, hh₁, e₁⟩ := hx
    obtain ⟨N₂, hN₂, h₂, hh₂, e₂⟩ := hy
    refine ⟨N₁ * N₂, mul_ne_zero hN₁ hN₂, (N₂ : MvPolynomial σ ℤ) * h₁ + (N₁ : MvPolynomial σ ℤ) * h₂,
      P.add_mem (P.mul_mem_left _ hh₁) (P.mul_mem_left _ hh₂), ?_⟩
    rw [map_add, map_mul, map_mul, map_intCast, map_intCast, ← e₁, ← e₂]
    push_cast
    ring
  | smul a x _ hx =>
    obtain ⟨N, hN, h, hh, e⟩ := hx
    obtain ⟨D, hD, a', ha'⟩ := exists_int_mul_eq_qmap a
    refine ⟨D * N, mul_ne_zero hD hN, a' * h, P.mul_mem_left _ hh, ?_⟩
    rw [map_mul, ← ha', ← e, smul_eq_mul]
    push_cast
    ring
end ReciprocityTheory.ChartRestriction.G.Geo
