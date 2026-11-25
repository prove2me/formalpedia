-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume.ech_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:54:35.493042+00:00
-- url     : https://prove2.me/submissions/e3df52ee-01fb-4628-a476-fec26ce6e522

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FixedPointImaginarySpan
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCubeVolume
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCubeVolume_pair_Bv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices MeasureTheory Set Filter
open scoped ComplexConjugate
noncomputable section
variable {ι : Type} [Fintype ι] {N : ℕ} (ω : Fin N → ι → Fin 2 → Fin 2 → ℂ)
namespace ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume
theorem _root_.solution (χ : ι → Fin 2 → Fin 2 → ℂ) {k : Fin N → ℤ} (hk : ∀ j, 2 * pr χ (ω j) = k j)
    (n : Fin N → ℤ) : ech ω χ (fun i => (n i : ℝ)) = 1 := by
  have hk' : ∀ j, pr χ (ω j) = (k j : ℝ) / 2 := fun j => by linarith [hk j]
  rw [ech, pair_Bv, Complex.exp_eq_one_iff]
  refine ⟨-∑ j, n j * k j, ?_⟩
  simp only [hk']
  push_cast
  rw [Finset.mul_sum, neg_mul (∑ x, ((n x : ℂ) * (k x : ℂ))), Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring
end ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume
