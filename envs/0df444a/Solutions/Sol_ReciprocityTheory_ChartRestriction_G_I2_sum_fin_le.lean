-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.sum_fin_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:25:56.900272+00:00
-- url     : https://prove2.me/submissions/cca006b9-2ece-4aac-b90a-f95be4ab367e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfEqInner
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormSqNonnegGaussianTorus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {M : Type*} [AddCommMonoid M] {ρ N : ℕ} (h : ρ ≤ N) (f : Fin ρ → M) :
    ∑ k : Fin N, (if h' : k.val < ρ then f ⟨k, h'⟩ else 0) = ∑ s, f s := by
  have key : ∀ M, ∑ k : Fin M, (if h' : k.val < ρ then f ⟨k, h'⟩ else 0) =
      ∑ k ∈ Finset.range M, (if h' : k < ρ then f ⟨k, h'⟩ else 0) :=
    fun M => Fin.sum_univ_eq_sum_range (fun k => if h' : k < ρ then f ⟨k, h'⟩ else 0) M
  rw [key N]
  have hρ : ∑ s, f s = ∑ k ∈ Finset.range ρ, (if h' : k < ρ then f ⟨k, h'⟩ else 0) := by
    rw [← key ρ]
    exact Finset.sum_congr rfl fun s _ => by simp [s.isLt]
  rw [hρ]
  symm
  apply Finset.sum_subset (Finset.range_mono h)
  intro k _ hk'
  simp only [Finset.mem_range] at hk'
  simp [hk']
end ReciprocityTheory.ChartRestriction.G.I2
