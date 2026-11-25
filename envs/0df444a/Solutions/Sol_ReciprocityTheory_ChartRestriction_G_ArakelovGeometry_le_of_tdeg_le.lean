-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.le_of_tdeg_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:51:11.427179+00:00
-- url     : https://prove2.me/submissions/2f3a1292-3ddf-4737-a588-4d1d4b5b07e3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogX
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_DimOfMinimal

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
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {c a : K → ℕ} {a₀ : ℕ} (ha : ∀ k, a₀ + tdeg c ≤ a k) (k : K) :
    c k ≤ a k ∧ a₀ ≤ (a - c) k := by
  have hck : c k ≤ tdeg c := by
    unfold tdeg
    exact Finset.single_le_sum (f := c) (fun i _ => Nat.zero_le _) (Finset.mem_univ k)
  have hak := ha k
  refine ⟨by omega, ?_⟩
  show a₀ ≤ a k - c k
  omega
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
