-- Prove2me | solution 1 for P2M_Formalism_L2_GlobalTheoryTheory_LocalLatticeBases_sumAlgEquiv_rename_inr_eq_C__b87c83100f40
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:55.855529+00:00
-- url     : https://prove2.me/submissions/d3c6cb7d-a01a-4cfa-838a-53d100935921

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL6_LinearIndependentProdRenameOfCard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
open MvPolynomial
variable {K : Type*} [Field K] {S₁ S₂ : Type*}
namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
theorem _root_.solution (b : MvPolynomial S₂ K) :
    sumAlgEquiv K S₁ S₂ (rename Sum.inr b) = C b := by
  have h := AlgHom.congr_fun (sumAlgEquiv_comp_rename_inr K S₁ S₂) b
  simpa [MvPolynomial.algebraMap_eq] using h
end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
