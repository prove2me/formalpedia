-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.GSB.gram_det_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:59:51.228802+00:00
-- url     : https://prove2.me/submissions/b8ab8773-856c-4789-af33-ad3664f8ed72

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LinIndToLp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GramReDetLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix InnerProductSpace
open scoped ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.GSB
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B ReciprocityTheory.ChartRestriction.DS.Xi.GS
variable {n m : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.GSB
theorem _root_.solution (w : Fin m → EuclideanSpace ℂ (Fin n)) (hw : ¬ LinearIndependent ℂ w) :
    (GS.gram w).det = 0 := by
  rw [Fintype.not_linearIndependent_iff] at hw
  obtain ⟨g, hg, i, hi⟩ := hw
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨g, fun h => hi (congrFun h i), ?_⟩
  funext a
  simp only [mulVec, dotProduct, GS.gram, Matrix.of_apply, Pi.zero_apply]
  have hs : ∑ b, inner ℂ (w a) (w b) * g b = inner ℂ (w a) (∑ b, g b • w b) := by
    rw [inner_sum]
    congr 1
    funext b
    rw [inner_smul_right]
    ring
  rw [hs, hg, inner_zero_right]
end ReciprocityTheory.ChartRestriction.DS.Xi.GSB
