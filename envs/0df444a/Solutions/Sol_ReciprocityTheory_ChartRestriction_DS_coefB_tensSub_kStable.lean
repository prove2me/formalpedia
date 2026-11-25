-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.coefB_tensSub_kStable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:20:50.714987+00:00
-- url     : https://prove2.me/submissions/174e0898-8709-4c8a-809f-18a21518e72c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_HidaSetting
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_TensorV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasimirGapAtNoncompactWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KUnitB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefAInnerEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefBTensSubKStable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
section admitted
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {lam : Fin n → ℝ} {V : Submodule ℂ M}
end admitted
section Tr
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D]
private lemma tensF_apply {M : Type*} [AddCommGroup M] [Module ℂ M] (dual : Bool)
    (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (u : Fin n → M) :
    tensF dual E a b u c =
      E a b (u c) + cond dual (-(if c = b then u a else 0)) (if c = a then u b else 0) := by
  cases dual
  · by_cases h : c = a <;> simp [tensF, tensV, coordV, h]
  · by_cases h : c = b <;> simp [tensF, tensVd, coordV, h, sub_eq_add_neg]
end Tr
section Exist
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}
end Exist
end ReciprocityTheory.ChartRestriction.DS
end
end

set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (dual : Bool) {S : Submodule ℂ D} (hS : IsKStableSub ε E S) :
    IsKStableSub ε (tensF dual E) (tensSub S) := by
  intro a b hab v hv
  have hv' : ∀ d, v d ∈ S := fun d => (Submodule.mem_pi.mp hv) d (Set.mem_univ d)
  refine Submodule.mem_pi.mpr fun c _ => ?_
  rw [tensF_apply]
  refine Submodule.add_mem _ (hS a b hab _ (hv' c)) ?_
  cases dual
  · by_cases h : c = a <;> simp [h, hv']
  · by_cases h : c = b <;> simp [h, hv']
end ReciprocityTheory.ChartRestriction.DS
