-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.scale_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:27.731854+00:00
-- url     : https://prove2.me/submissions/3003a8ec-0ccb-4996-9c71-0bd4612e979c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcAdd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_zero_of_scale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {k : Type} [CommRing k] [Algebra ℚ k]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution {d : ℕ} (f : PS k 2 d) (c0 c1 : ℕ)
    (h : ev (n := 2) (![fun i => (2 : k) ^ c0 • (X ((0 : Fin 2), i) : PS k 2 d),
      fun i => (2 : k) ^ c1 • (X ((1 : Fin 2), i) : PS k 2 d)] : Fin 2 → Pt k 2 d) f = (2 : k) • f)
    (n : Fin 2 × Fin d →₀ ℕ) (hn : c0 * (∑ i, n (0, i)) + c1 * (∑ i, n (1, i)) ≠ 1) : coeff n f = 0 := by
  let w : Fin 2 × Fin d → ℕ := fun p => if p.1 = 0 then c0 else c1
  have hfam : ((fun s => (2 : k) ^ w s) • (X : Fin 2 × Fin d → PS k 2 d)) = fun p =>
      (![fun i => (2 : k) ^ c0 • (X ((0 : Fin 2), i) : PS k 2 d),
        fun i => (2 : k) ^ c1 • (X ((1 : Fin 2), i) : PS k 2 d)] : Fin 2 → Pt k 2 d) p.1 p.2 := by
    funext p
    rcases p with ⟨j, i⟩
    fin_cases j <;> simp [w]
  refine coeff_zero_of_scale w f ?_ n ?_
  · rw [hfam]
    exact h
  · rw [Fintype.sum_prod_type, Fin.sum_univ_two]
    simpa [w, Finset.mul_sum] using hn
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
