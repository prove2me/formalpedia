-- Prove2me | solution 1 for P2M_Formalism_L2_Pj_FJ_emb_cc__a0a14d96c40b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:05:44.938228+00:00
-- url     : https://prove2.me/submissions/1bfff7af-bfe6-4736-81c0-29d076e3040e

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ

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
open ReciprocityTheory.ChartRestriction.G.FD NumberField Matrix
open scoped ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.FJ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
namespace Formalism.L2.Pj.FJ
theorem _root_.solution (τ : E →+* ℂ) (x : E) : τ (cc x) = conj (τ x) := by unfold cc; exact NumberField.IsCMField.complexEmbedding_complexConj E τ x
end Formalism.L2.Pj.FJ
