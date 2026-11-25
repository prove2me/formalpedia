-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.weight_lexW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:46:37.611072+00:00
-- url     : https://prove2.me/submissions/fdf55bb1-00cb-4c8f-83c9-0c4f08f6806c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_DoubleBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsPrimeFiltrationOfIsMultiHomogIdeal

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
attribute [local instance 2000] lexDecEq
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (e : K ≃ Fin n) (m : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (lexW (ι := ι) e) m = toLex (fun j => ∑ i, m ⟨e.symm j, i⟩) := by
  rw [Finsupp.weight_apply,
    Finsupp.sum_fintype m (fun i c => c • lexW (ι := ι) e i) (fun i => zero_nsmul _)]
  show (∑ p, m p • (Pi.single (e p.1) 1 : Fin n → ℕ)) = fun j => ∑ i, m ⟨e.symm j, i⟩
  funext j
  rw [Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single (e.symm j)]
  · simp [Pi.single_apply]
  · intro k _ hk
    refine Finset.sum_eq_zero fun i _ => ?_
    have hjk : j ≠ e k := fun h => hk (by rw [h, Equiv.symm_apply_apply])
    simp [Pi.single_apply, hjk]
  · simp
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
