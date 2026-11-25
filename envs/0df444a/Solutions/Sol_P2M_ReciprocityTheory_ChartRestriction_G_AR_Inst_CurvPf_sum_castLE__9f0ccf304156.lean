-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_sum_castLE__9f0ccf304156
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:30:24.225053+00:00
-- url     : https://prove2.me/submissions/0c197846-3607-4315-829d-1e004948c293

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_CoeffMatrixZeroCorrectedLineGramPoly
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DiagonalCurvatureCoefficient

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
open Polynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P Filter Topology
variable {r m : ℕ} (hm : m ≤ r) (D : Fin r → ℝ) (Y : Matrix (Fin r) (Fin r) ℂ)
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
theorem _root_.solution {M : Type} [AddCommMonoid M] (g : Fin r → M) :
    ∑ j : Fin m, g (Fin.castLE hm j) = ∑ k : Fin r, if (k : ℕ) < m then g k else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun j _ => Fin.castLE hm j) ?_ ?_ ?_ ?_
  · intro j _
    simp
  · intro a _ b _ h
    exact Fin.ext (by simpa using congrArg Fin.val h)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    exact ⟨⟨k, hk⟩, Finset.mem_univ _, Fin.ext (by simp)⟩
  · intro j _
    rfl
end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
