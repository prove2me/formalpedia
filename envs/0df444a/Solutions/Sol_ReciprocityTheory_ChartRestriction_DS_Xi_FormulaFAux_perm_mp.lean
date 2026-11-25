-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.perm_mp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:42:11.009744+00:00
-- url     : https://prove2.me/submissions/701c85a6-71fb-4df3-9411-cef44f384308

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_DelFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_IndexEmbeddingBijective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_index_embedding_bijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux
namespace ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux
theorem _root_.solution (k r' : ℕ) (hk : 1 ≤ k) : MeasurePreserving (permF k r') volume volume := by
  let E := Equiv.ofBijective (ix2 k r') (index_embedding_bijective k r' hk)
  have h1 := MeasurePreserving.symm _
    (measurePreserving_piCongrLeft (fun _ : Fin (2 * r' + k + 1) => (volume : Measure ℂ)) E)
  have h2 := measurePreserving_sumPiEquivProdPi
    (fun _ : Fin (1 + r') ⊕ (Fin (1 + r') ⊕ Fin (k - 1)) => (volume : Measure ℂ))
  have h3 := measurePreserving_sumPiEquivProdPi (fun _ : Fin (1 + r') ⊕ Fin (k - 1) => (volume : Measure ℂ))
  have h4 := (MeasurePreserving.id (volume : Measure (Fin (1 + r') → ℂ))).prod h3
  have h5 := h4.comp (h2.comp h1)
  first
    | exact h5
    | (convert h5 using 1; funext z; rfl)
end ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux
