-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.kirrSpan_kStable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:34:37.068416+00:00
-- url     : https://prove2.me/submissions/10dfc8a7-d05e-4154-8942-d64176b4999c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KhwWeightEqOfIrr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kirr_compact_word

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {X : Type*} [AddCommGroup X] [Module ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X} {Λ : Fin n → ℝ} {V : Submodule ℂ X}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hA : IsGlRep A) {ν : Fin n → ℝ} {u : X} (hu : IsKHWVec ε A ν u) :
    IsKStableSub ε A (kirrSpan ε A u) := by
  intro a b hab v hv
  have h : kirrSpan ε A u ≤ (kirrSpan ε A u).comap (A a b) := Submodule.span_le.2 (by
    rintro _ ⟨l, hl, rfl⟩
    exact kirr_compact_word hA hu l hl a b hab)
  exact h hv
end ReciprocityTheory.ChartRestriction.DS
