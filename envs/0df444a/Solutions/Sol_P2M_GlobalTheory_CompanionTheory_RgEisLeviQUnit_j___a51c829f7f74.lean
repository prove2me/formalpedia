-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_RgEisLeviQUnit_j___a51c829f7f74
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:59:54.339835+00:00
-- url     : https://prove2.me/submissions/e590298d-0e81-458c-9729-7ca16157d0fc

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviQuotientOfBlockDet
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_jQ_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisLeviQUnit
open PositivityTheory.RgEis
variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set ι}
  [Fintype ↥sᶜ] [DecidableEq ↥sᶜ] (A : Ad E R) (ε : ℤˣ) (hσ : ∀ x, A.σ (A.σ x) = x)
namespace GlobalTheory.CompanionTheory.RgEisLeviQUnit
theorem _root_.solution (m : A.U ε ↥sᶜ) (hm : m ∈ A.uΓ ε ↥sᶜ) : (jQ (s := s) A ε m : A.U ε ι) ∈ A.uΓ ε ι := by
  obtain ⟨g₀, hg⟩ := Subgroup.mem_subgroupOf.1 hm
  refine Subgroup.mem_subgroupOf.2 ⟨jG E g₀, Units.ext ?_⟩
  have e1 : ((g₀ : Matrix (↥sᶜ ⊕ ↥sᶜ) (↥sᶜ ⊕ ↥sᶜ) E)).map A.i = (m.1 : Matrix (↥sᶜ ⊕ ↥sᶜ) (↥sᶜ ⊕ ↥sᶜ) R) :=
    congrArg Units.val hg
  rw [jQ_val, jG_val, ← e1, ← jM_map]
  rfl
end GlobalTheory.CompanionTheory.RgEisLeviQUnit
