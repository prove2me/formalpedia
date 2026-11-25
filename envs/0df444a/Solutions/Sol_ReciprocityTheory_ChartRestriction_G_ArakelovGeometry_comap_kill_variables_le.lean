-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.comap_kill_variables_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:07:14.058909+00:00
-- url     : https://prove2.me/submissions/7c5727fb-c837-4c95-aa6f-104bad56c067

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CardPieceIrrelevantIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_TwoLeKrullDimOfRelevantPrime
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_le_comap_kill_of_homogeneous

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
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {ι : Fin 2 → Type} [∀ k, Fintype (ι k)] {q : Ideal (MRing ι)}
    (hh : IsMultiHomogIdeal q) :
    q.comap (i2kill (ι := ι) 0) ≤ q.comap ((i2kill (ι := ι) 1).comp (i2kill 0)) := by
  intro g hg
  rw [Ideal.mem_comap] at hg
  have h1 := le_comap_kill_of_homogeneous hh 1 hg
  rw [Ideal.mem_comap] at h1
  rw [Ideal.mem_comap, AlgHom.comp_apply]
  exact h1
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
