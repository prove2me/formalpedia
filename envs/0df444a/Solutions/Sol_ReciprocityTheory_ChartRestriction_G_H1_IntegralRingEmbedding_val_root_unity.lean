-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding.val_root_unity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:54:11.86585+00:00
-- url     : https://prove2.me/submissions/c9dfed9d-3aab-4b52-83dc-acc17d99ecba

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_NakayamaChar
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_IntegralRingEmbedding

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding
open Module
variable {F : Type} [Field F] (v : AddValuation F (WithTop ℚ))
namespace ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding
theorem _root_.solution {N : ℕ} (hN : 1 ≤ N) {z : F} (hz : z ^ N = 1) : v z = 0 := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hz
    exact zero_ne_one hz
  have h1 : v (z ^ N) = N • v z := AddValuation.map_pow v z N
  rw [hz, AddValuation.map_one] at h1
  have h2 : v z + v z⁻¹ = 0 := by
    rw [← AddValuation.map_mul, mul_inv_cancel₀ hz0, AddValuation.map_one]
  generalize v z = w at h1 h2 ⊢
  induction w using WithTop.recTopCoe with
  | top => simp at h2
  | coe q =>
    have h3 : ((N • q : ℚ) : WithTop ℚ) = 0 := by
      rw [WithTop.coe_nsmul]
      exact h1.symm
    have h4 : N • q = 0 := by exact_mod_cast h3
    rw [nsmul_eq_mul] at h4
    have h5 : q = 0 := (mul_eq_zero.1 h4).resolve_left (by exact_mod_cast (show N ≠ 0 by omega))
    simp [h5]
end ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding
