-- Prove2me | solution 1 for PositivityTheory.RgUd.Prod.Asm.irreducible_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:03:35.506243+00:00
-- url     : https://prove2.me/submissions/71017e36-c1fe-4704-84a9-b2ae7c2ef185

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CentralProducts_UnitarisableHypotheses_IrrSub
import Theorems.Thm_PositivityTheory_RgUd_Prod_Asm_mem_fixed_iff
import Theorems.Thm_PositivityTheory_RgUd_Prod_Asm_fixed_split

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.Prod PositivityTheory.RgUd.Prod.Asm
open GlobalTheory.PRep
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
namespace PositivityTheory.RgUd.Prod.Asm
theorem _root_.solution (K : Subgroup G)
    (hcompl : ∀ S : Subrepresentation ρ, ∃ T : Subrepresentation ρ, IsCompl S.toSubmodule T.toSubmodule)
    (W : Subrepresentation ρ) (h1 : fixed ρ K ⊓ W.toSubmodule ≠ ⊥)
    (h2 : ∀ U : Subrepresentation ρ, U.toSubmodule ≤ W.toSubmodule → fixed ρ K ⊓ U.toSubmodule ≠ ⊥ →
      fixed ρ K ⊓ W.toSubmodule ≤ U.toSubmodule)
    (h3 : ∀ U : Subrepresentation ρ, fixed ρ K ⊓ W.toSubmodule ≤ U.toSubmodule →
      W.toSubmodule ≤ U.toSubmodule) :
    W.toRepresentation.IsIrreducible := by
  obtain ⟨w, hwF, hwW, hw0⟩ : ∃ w, w ∈ fixed ρ K ∧ w ∈ W.toSubmodule ∧ w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply h1
    rw [Submodule.eq_bot_iff]
    intro x hx
    exact hcon x hx.1 hx.2
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    have h1' : (⟨w, hwW⟩ : W.toSubmodule) ∈ (⊤ : Subrepresentation W.toRepresentation).toSubmodule :=
      Submodule.mem_top
    rw [← h] at h1'
    have h2' : (⟨w, hwW⟩ : W.toSubmodule) = 0 := (Submodule.mem_bot ℂ).1 h1'
    exact hw0 (congrArg Subtype.val h2')
  · intro U
    let U' : Subrepresentation ρ :=
      { toSubmodule := U.toSubmodule.map W.toSubmodule.subtype
        apply_mem_toSubmodule := by
          intro g v hv
          obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 hv
          exact Submodule.mem_map.2 ⟨W.toRepresentation g u, U.apply_mem_toSubmodule g hu, rfl⟩ }
    have hU'le : U'.toSubmodule ≤ W.toSubmodule := by
      intro v hv
      obtain ⟨u, _, rfl⟩ := Submodule.mem_map.1 hv
      exact u.2
    by_cases hF : fixed ρ K ⊓ U'.toSubmodule = ⊥
    · left
      obtain ⟨C, hC⟩ := hcompl U'
      have hFC : fixed ρ K ⊓ W.toSubmodule ≤ C.toSubmodule := by
        rintro x ⟨hxF, hxW⟩
        have hx : x ∈ U'.toSubmodule ⊔ C.toSubmodule := by
          rw [hC.sup_eq_top]
          exact Submodule.mem_top
        obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.1 hx
        have huF : u ∈ fixed ρ K := (mem_fixed_iff ρ K u).2 fun k =>
          fixed_split ρ U' C hC.inf_eq_bot k hu hc ((mem_fixed_iff ρ K _).1 hxF k)
        have hu0 : u ∈ fixed ρ K ⊓ U'.toSubmodule := ⟨huF, hu⟩
        rw [hF] at hu0
        rw [(Submodule.mem_bot ℂ).1 hu0, zero_add]
        exact hc
      have hWC := h3 C hFC
      apply Subrepresentation.ext
      show U.toSubmodule = (⊥ : Submodule ℂ W.toSubmodule)
      rw [Submodule.eq_bot_iff]
      intro u hu
      have hm : (u : V) ∈ U'.toSubmodule ⊓ C.toSubmodule :=
        ⟨Submodule.mem_map_of_mem hu, hWC u.2⟩
      rw [hC.inf_eq_bot] at hm
      exact Subtype.ext ((Submodule.mem_bot ℂ).1 hm)
    · right
      have hWU := h3 U' (h2 U' hU'le hF)
      apply Subrepresentation.ext
      show U.toSubmodule = (⊤ : Submodule ℂ W.toSubmodule)
      rw [eq_top_iff]
      intro x _
      obtain ⟨u, hu, hux⟩ := Submodule.mem_map.1 (hWU x.2)
      have : u = x := Subtype.ext hux
      rw [← this]
      exact hu
end PositivityTheory.RgUd.Prod.Asm
