-- Prove2me | solution 1 for P2M_GlobalTheory_T_finite_lattices_between_of_smul_le__0bcadc6f8aea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:29:10.790988+00:00
-- url     : https://prove2.me/submissions/9f2ffede-08d3-45ae-b24e-002ae09ee05e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FiniteLatticesBetweenOfSmulLe
import Mathlib
import Definitions.Def_Formalism_HermitianLattices_FinalNeighbourConstruct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ClassSetAssembly
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FiniteLatticesBetweenOfSmulLeStatement
import Theorems.Thm_GlobalTheory_finite_lattices_between_of_smul_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V), M.FG → ∀ N : ℕ, 0 < N → {Λ : Submodule (𝓞 K) V | M ≤ Λ ∧ ∀ x ∈ Λ, (N : K) • x ∈ M}.Finite := by
  first | exact @GlobalTheory.finite_lattices_between_of_smul_le | exact GlobalTheory.finite_lattices_between_of_smul_le | (intros; apply GlobalTheory.finite_lattices_between_of_smul_le <;> assumption)
end _root_.GlobalTheory.T
