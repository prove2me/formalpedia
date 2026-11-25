-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sdd_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:03:34.542312+00:00
-- url     : https://prove2.me/submissions/216aacec-1e66-4852-9545-dccd4eb449bd

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegDB
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_proj_eq_zero_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open NumberField
variable {K : Type} [Field K] [NumberField K] {r e : ℕ}
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {k₀ k₁ : ℕ} (B : Submodule (𝓞 K) (Fin r → K)) (b₀ : Fin k₀ → Fin r → K)
    (c b₁ : Fin k₁ → Fin r → K) (hsat : satSub B b₀ = B ⊓ cutSub K r e) (hcB : ∀ j, c j ∈ B)
    (hcb : ∀ j, projGe K r e (c j) = b₁ j) :
    (satSub B b₀ ⊔ Submodule.span (𝓞 K) (Set.range c)).toAddSubgroup.relIndex B.toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range b₁)).toAddSubgroup.relIndex
        (B.map (projGe K r e)).toAddSubgroup := by
  have hspan : Submodule.span (𝓞 K) (Set.range b₁) =
      (Submodule.span (𝓞 K) (Set.range c)).map (projGe K r e) := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2
    funext j
    exact (hcb j).symm
  have hcle : Submodule.span (𝓞 K) (Set.range c) ≤ B := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hcB j
  rw [Submodule.map_toAddSubgroup, ← AddSubgroup.relIndex_comap,
    ← AddSubgroup.inf_relIndex_right, eq_comm, ← AddSubgroup.inf_relIndex_right]
  congr 1
  ext x
  simp only [AddSubgroup.mem_inf, AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, hsat,
    hspan]
  constructor
  · rintro ⟨⟨y, hy, hxy⟩, hx⟩
    have hxy' : projGe K r e y = projGe K r e x := hxy
    have hyB := hcle hy
    refine ⟨?_, hx⟩
    have hs : x - y ∈ B ⊓ cutSub K r e :=
      ⟨B.sub_mem hx hyB, (sdd_proj_eq_zero_iff _).mp (by rw [map_sub, hxy', sub_self])⟩
    have := Submodule.add_mem_sup hs hy
    rwa [sub_add_cancel] at this
  · rintro ⟨hsup, hx⟩
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hsup
    refine ⟨⟨t, ht, ?_⟩, hx⟩
    show projGe K r e t = projGe K r e (s + t)
    rw [map_add, (sdd_proj_eq_zero_iff s).mpr hs.2, zero_add]
end ReciprocityTheory.MultiplicativeHeights
