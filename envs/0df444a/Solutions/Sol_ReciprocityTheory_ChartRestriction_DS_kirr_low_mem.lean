-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.kirr_low_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:13:54.577215+00:00
-- url     : https://prove2.me/submissions/050068fb-19eb-4b47-80b4-ebd06ef922b5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KhwWeightEqOfIrr

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
theorem _root_.solution {u : X} {a b : Fin n} (hba : b < a) (hab : ε a = ε b) {x : X}
    (hx : x ∈ kirrSpan ε A u) : A a b x ∈ kirrSpan ε A u := by
  have h : kirrSpan ε A u ≤ (kirrSpan ε A u).comap (A a b) := Submodule.span_le.2 (by
    rintro _ ⟨l, hl, rfl⟩
    exact Submodule.subset_span ⟨(a, b) :: l, fun p hp => by
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨hba, hab⟩
      · exact hl p hp, rfl⟩)
  exact h hx
end ReciprocityTheory.ChartRestriction.DS
