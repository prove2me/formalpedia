-- Prove2me | solution 1 for UlmsTheorem.exists_kaplanskyTarget_caseI
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:58:35.374334+00:00
-- url     : https://prove2.me/submissions/e92045f3-a556-4434-b42f-5b1217da3f9f

module
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmInvariants
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Pure
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Extension
public import Theorems.Thm_UlmsTheorem_coe_le_ulmHeight_of_mem
public import Theorems.Thm_UlmsTheorem_isProper_iff_forall_not_mem_succ
public import Theorems.Thm_UlmsTheorem_mem_pImage
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_add_one_iff
public import Theorems.Thm_UlmsTheorem_pHeight_zero
public import Theorems.Thm_UlmsTheorem_pOrder_zero
public import Theorems.Thm_UlmsTheorem_ulmHeight_eq_of_mem_not_mem_succ
public import Theorems.Thm_UlmsTheorem_ulmHeight_le_of_not_mem_succ
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_antitone
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_succ
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_zero
attribute [local simp] UlmsTheorem.mem_pImage
attribute [local simp] UlmsTheorem.mem_ulmSubgroup_add_one_iff
attribute [local simp] UlmsTheorem.pHeight_zero
attribute [local simp] UlmsTheorem.pOrder_zero
attribute [local simp] UlmsTheorem.ulmSubgroup_zero



set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
universe u
variable (p : ℕ) [hp : Fact p.Prime]
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]
omit hp
namespace UlmsTheorem
theorem _root_.solution
    {α : Ordinal.{0}} (s : UlmStageAt p (G := G) (H := H) α)
    {x : G}
    (hpxA : p • x ∈ s.A)
    (hxα : x ∈ ulmSubgroup p α (G := G))
    (hxSucc : x ∉ ulmSubgroup p (Order.succ α) (G := G))
    (hxProper : IsProper p s.A x)
    (hpxMax : ∀ y : G, y - x ∈ s.A → IsProper p s.A y →
      ulmHeight p (p • y) ≤ ulmHeight p (p • x))
    (hcaseI :
      p • x ∉ ulmSubgroup p (Order.succ (Order.succ α)) (G := G)) :
    ∃ w : H,
      p • w = (s.e ⟨p • x, hpxA⟩ : H) ∧
      w ∈ ulmSubgroup p α (G := H) ∧
      w ∉ ulmSubgroup p (Order.succ α) (G := H) ∧
      IsProper p s.B w := by
  have hxHeight : ulmHeight p x = (α : WithTop Ordinal.{0}) :=
    ulmHeight_eq_of_mem_not_mem_succ p x α hxα hxSucc
  -- `x ∈ G_α` puts `p • x` in `G_{α+1}`, so its image has a root `w ∈ H_α`.
  have hzSucc : (s.e ⟨p • x, hpxA⟩ : H) ∈ ulmSubgroup p (Order.succ α) (G := H) :=
    (s.hφ_succ _).mp (by rw [ulmSubgroup_succ]; exact ⟨x, hxα, rfl⟩)
  -- Case I says `p • x ∉ G_{α+2}`, so the root has exact height `α`.
  have hzSuccSucc :
      (s.e ⟨p • x, hpxA⟩ : H) ∉ ulmSubgroup p (Order.succ (Order.succ α)) (G := H) :=
    fun hz ↦ hcaseI ((s.hφ_succSucc _).mpr hz)
  rw [ulmSubgroup_succ] at hzSucc
  obtain ⟨w, hwα, hpw⟩ := hzSucc
  have hwSucc : w ∉ ulmSubgroup p (Order.succ α) (G := H) := fun hw ↦
    hzSuccSucc (by rw [← hpw, ulmSubgroup_succ]; exact ⟨w, hw, rfl⟩)
  refine ⟨w, hpw, hwα, hwSucc, ?_⟩
  -- Properness of `w`: a target translate `w + t` of height `> α` would pull
  -- back to a translate of `x` whose `p`-multiple beats the maximal height.
  refine (isProper_iff_forall_not_mem_succ p s.B hwα hwSucc).2 fun t hwtSucc ↦ ?_
  have htα : (t : H) ∈ ulmSubgroup p α (G := H) := by
    simpa using (ulmSubgroup p α (G := H)).sub_mem
      (ulmSubgroup_antitone p (Order.le_succ α) hwtSucc) hwα
  let a : s.A := s.e.symm t
  have hea : s.e a = t := by simp [a]
  have haα : (a : G) ∈ ulmSubgroup p α (G := G) :=
    (s.hφ_at a).mpr (by simpa [hea] using htα)
  let y : G := x + (a : G)
  have hyα : y ∈ ulmSubgroup p α (G := G) := (ulmSubgroup p α).add_mem hxα haα
  have hySucc : y ∉ ulmSubgroup p (Order.succ α) (G := G) :=
    (isProper_iff_forall_not_mem_succ p s.A hxα hxSucc).1 hxProper a
  have hyHeight : ulmHeight p y = (α : WithTop Ordinal.{0}) :=
    ulmHeight_eq_of_mem_not_mem_succ p y α hyα hySucc
  have hyProper : IsProper p s.A y := fun b ↦ by
    rw [hyHeight, ← hxHeight]
    simpa [y, add_assoc] using hxProper (a + b)
  have hycoset : y - x ∈ s.A := by simp [y]
  have hpyA : p • y ∈ s.A := by
    simpa [y, smul_add] using s.A.add_mem hpxA (s.A.nsmul_mem a.prop p)
  -- The image of `p • y` is `p • (w + t)`, which lies in `H_{α+2}`.
  have hepy : (s.e ⟨p • y, hpyA⟩ : H) = p • (w + (t : H)) := by
    have hdecomp : (⟨p • y, hpyA⟩ : s.A) = ⟨p • x, hpxA⟩ + p • a :=
      Subtype.ext (by simp [y, smul_add])
    rw [hdecomp, map_add, map_nsmul, hea]
    push_cast
    rw [← hpw, smul_add]
  have hpySuccSucc : p • y ∈ ulmSubgroup p (Order.succ (Order.succ α)) (G := G) :=
    (s.hφ_succSucc _).mpr <| by
      rw [hepy, ulmSubgroup_succ]
      exact ⟨w + (t : H), hwtSucc, rfl⟩
  -- But `y` is a proper translate of `x`, so maximality caps `h(p • y)` at `α+1`.
  exact absurd
    ((coe_le_ulmHeight_of_mem p (p • y) _ hpySuccSucc).trans
      ((hpxMax y hycoset hyProper).trans
        (ulmHeight_le_of_not_mem_succ p (p • x) (Order.succ α) hcaseI)))
    (not_le_of_gt (WithTop.coe_lt_coe.mpr (Order.lt_succ (Order.succ α))))
end UlmsTheorem
