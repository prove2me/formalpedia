-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FlagSpanBounds.span_le_of_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:54:52.59143+00:00
-- url     : https://prove2.me/submissions/9e682e30-4356-411d-bfdb-79a79cfd299e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_NonvanishingNearMaximumHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlagSpanBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FlagSpanBounds
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.FlagSpanBounds
theorem _root_.solution (p : ℕ) (hp : p ≤ r) (M N : Matrix (Fin r) (Fin r) ℂ) (hN : N.BlockTriangular id) :
    Submodule.span ℂ (Set.range fun a : Fin p => col (M * N) (Fin.castLE hp a)) ≤
      Submodule.span ℂ (Set.range fun a : Fin p => col M (Fin.castLE hp a)) := by
  rw [Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  have hcol : col (M * N) (Fin.castLE hp a) = ∑ j : Fin r, N j (Fin.castLE hp a) • col M j := by
    funext i
    simp only [col, Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  show col (M * N) (Fin.castLE hp a) ∈ Submodule.span ℂ (Set.range fun a : Fin p => col M (Fin.castLE hp a))
  rw [hcol]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  by_cases hj : (j : ℕ) < p
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, congrArg (col M) (Fin.ext rfl)⟩)
  · have hlt : Fin.castLE hp a < j := Fin.lt_iff_val_lt_val.mpr (by show (a : ℕ) < j; omega)
    have h0 : N j (Fin.castLE hp a) = 0 := hN hlt
    rw [h0, zero_smul]
    exact Submodule.zero_mem _
end ReciprocityTheory.ChartRestriction.G.FD.FlagSpanBounds
