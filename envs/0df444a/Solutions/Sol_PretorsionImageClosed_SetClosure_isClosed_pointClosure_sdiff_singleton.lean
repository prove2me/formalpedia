-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.isClosed_pointClosure_sdiff_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:27:42.079236+00:00
-- url     : https://prove2.me/submissions/a4e44130-1df1-4f40-88cf-a93b8e323e8e

module
public import Mathlib.Data.Set.Finite.Powerset
public import Mathlib.Order.Closure
public import Mathlib.Order.Preorder.Finite
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Basic
public import Theorems.Thm_PretorsionImageClosed_SetClosure_isClosed_sdiff_singleton_of_not_mem_closure

set_option autoImplicit true
@[expose] public section
public section
open Set
open PretorsionImageClosed
open PretorsionImageClosed.SetClosure
variable {E : Type*} (c : SetClosure E)
variable {c}
namespace PretorsionImageClosed.SetClosure
theorem _root_.solution
    (hfin : c.IsFinitary) (hae : c.IsAntiExchange)
    (hempty : c.IsClosed ∅) (x : E) :
    c.IsClosed (c ({x} : Set E) \ {x}) := by
  let J : Set E := c ({x} : Set E)
  have hJ : c.IsClosed J := c.isClosed_closure _
  by_contra hnot
  have hxc : x ∈ c (J \ {x}) := by
    by_contra hx
    exact hnot (isClosed_sdiff_singleton_of_not_mem_closure hJ hx)
  obtain ⟨S₀, hS₀fin, hS₀sub, hxS₀⟩ := hfin hxc
  let P : Set (Set E) := {S | S ⊆ S₀ ∧ x ∈ c S}
  have hPfin : P.Finite := by
    apply hS₀fin.powerset.subset
    intro S hS
    exact hS.1
  have hPnonempty : P.Nonempty := ⟨S₀, subset_rfl, hxS₀⟩
  obtain ⟨S, hSmin⟩ := hPfin.exists_minimal hPnonempty
  have hSne : S.Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro hSempty
    have : x ∈ c (∅ : Set E) := by
      simpa [hSempty] using hSmin.prop.2
    simp [hempty.closure_eq] at this
  obtain ⟨y, hyS⟩ := hSne
  have hproper : S \ {y} ⊂ S := by
    rw [Set.ssubset_iff_subset_ne]
    refine ⟨sdiff_subset, ?_⟩
    intro heq
    have : y ∈ S \ {y} := heq.symm ▸ hyS
    exact this.2 rfl
  have hxK : x ∉ c (S \ {y}) := by
    intro hx
    apply hSmin.not_prop_of_ssubset hproper
    exact ⟨sdiff_subset.trans hSmin.prop.1, hx⟩
  let K : Set E := c (S \ {y})
  have hKclosed : c.IsClosed K := c.isClosed_closure _
  have hxK' : x ∉ K := hxK
  have hyK : y ∉ K := by
    intro hy
    have hSK : S ⊆ K := by
      intro z hz
      by_cases hzy : z = y
      · simpa [hzy] using hy
      · exact c.le_closure (S \ {y}) ⟨hz, by simpa using hzy⟩
    have hxcK : x ∈ c K := c.monotone hSK hSmin.prop.2
    exact hxK' (by simpa [K] using hxcK)
  have hxy : x ≠ y := by
    intro hxy
    have hyS₀ : y ∈ S₀ := hSmin.prop.1 hyS
    have hyJdiff : y ∈ J \ {x} := hS₀sub hyS₀
    exact hyJdiff.2 (by simp [hxy])
  have hxInsert : x ∈ c (insert y K) := by
    apply c.monotone _ hSmin.prop.2
    intro z hz
    by_cases hzy : z = y
    · simp [hzy]
    · exact mem_insert_of_mem _ (c.le_closure (S \ {y}) ⟨hz, by simpa using hzy⟩)
  have hyJdiff : y ∈ J \ {x} := hS₀sub (hSmin.prop.1 hyS)
  have hyInsert : y ∈ c (insert x K) := by
    apply c.monotone _ hyJdiff.1
    exact singleton_subset_iff.mpr (mem_insert x K)
  exact (hae hKclosed hxK' hyK hxy hxInsert) hyInsert
end PretorsionImageClosed.SetClosure
