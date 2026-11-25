-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.GS.prod_Iic_castLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:18:04.648961+00:00
-- url     : https://prove2.me/submissions/79c27d93-1c62-4a00-8110-5d88e9d00bb0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ExistsKmat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ProdIicCastLE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.GS
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
variable {k r : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.GS
theorem _root_.solution (l : Fin (r + 1)) (g : Fin (r + 1) → ℝ) :
    ∏ j ∈ Finset.Iic l, g j = ∏ j : Fin (l.val + 1), g (Fin.castLE (by omega) j) := by
  rw [show (∏ j : Fin (l.val + 1), g (Fin.castLE (by omega) j)) =
      ∏ j ∈ Finset.univ.map (Fin.castLEEmb (show l.val + 1 ≤ r + 1 by omega)), g j by
    rw [Finset.prod_map]; rfl]
  congr 1
  ext j
  simp only [Finset.mem_Iic, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · intro hj; exact ⟨⟨j.val, by rw [Fin.le_def] at hj; omega⟩, Fin.ext rfl⟩
  · rintro ⟨b, rfl⟩; rw [Fin.le_def]; simp; omega
end ReciprocityTheory.ChartRestriction.DS.Xi.GS
