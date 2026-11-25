-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.kirrPs_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:41:08.986847+00:00
-- url     : https://prove2.me/submissions/d21fc8a3-7885-47b4-867f-592158d9c1bc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KhwWeightEqOfIrr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kirrWord_wt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kirrWord_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kirrSpan_kStable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kirrSpan_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kirrPs_wt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kirrH_apply

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
theorem _root_.solution (hA : IsGlRep A) (hV : IsKIrrHW ε A Λ V) {u : X} (hu : u ∈ V) (hu0 : u ≠ 0)
    {ν : Fin n → ℝ} (hν : IsKHWVec ε A ν u) {w : X} (hw : w ∈ V) (hw0 : w ≠ 0) {μ : Fin n → ℝ}
    (hμ : ∀ a, A a a w = (μ a : ℂ) • w) (k : ℕ) : kirrPs k μ ≤ kirrPs k ν := by
  classical
  obtain ⟨-, hVs, hirr, -⟩ := id hV
  have hspan : kirrSpan ε A u = V := by
    rcases hirr _ (kirrSpan_le hVs hu) (kirrSpan_kStable hA hν) with h | h
    · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ kirrWord_mem (l := []) u (fun p hp => by simp at hp))) hu0
    · exact h
  have hle : kirrSpan ε A u ≤
      ⨆ z ∈ {z : ℂ | ∃ r : ℝ, r ≤ kirrPs k ν ∧ z = r}, Module.End.eigenspace (kirrH A k) z :=
    Submodule.span_le.2 (by
      rintro _ ⟨l, hl, rfl⟩
      refine Submodule.mem_iSup_of_mem ((kirrPs k (kirrWt ν l) : ℝ) : ℂ)
        (Submodule.mem_iSup_of_mem (Set.mem_setOf.2 ⟨_, kirrPs_wt k ν l hl, rfl⟩) ?_)
      rw [Module.End.mem_eigenspace_iff]
      exact kirrH_apply k (kirrWord_wt hA hν.1 l))
  have hwS := hle (by rw [hspan]; exact hw)
  by_contra hlt
  push_neg at hlt
  have hwE : w ∈ Module.End.eigenspace (kirrH A k) ((kirrPs k μ : ℝ) : ℂ) := by
    rw [Module.End.mem_eigenspace_iff]; exact kirrH_apply k hμ
  have hx : ((kirrPs k μ : ℝ) : ℂ) ∉ {z : ℂ | ∃ r : ℝ, r ≤ kirrPs k ν ∧ z = r} := by
    rintro ⟨r, hr, he⟩
    have := Complex.ofReal_injective he
    linarith
  have hd : Disjoint (Module.End.eigenspace (kirrH A k) ((kirrPs k μ : ℝ) : ℂ))
      (⨆ z ∈ {z : ℂ | ∃ r : ℝ, r ≤ kirrPs k ν ∧ z = r}, Module.End.eigenspace (kirrH A k) z) := by
    first
      | exact (Module.End.eigenspaces_iSupIndep (kirrH A k)).disjoint_biSup hx
      | exact (Module.End.eigenspaces_independent (kirrH A k)).disjoint_biSup hx
  exact hw0 (Submodule.disjoint_def.1 hd w hwE hwS)
end ReciprocityTheory.ChartRestriction.DS
