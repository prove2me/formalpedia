-- Prove2me | solution 1 for UlmsTheorem.exists_kaplanskyTarget_caseII
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:00:04.201682+00:00
-- url     : https://prove2.me/submissions/9fa57f8f-52d9-4fbd-a128-ef78a394f407

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
public import Theorems.Thm_UlmsTheorem_kaplanskyMap_not_surjective_iff_proper
public import Theorems.Thm_UlmsTheorem_kaplansky_not_surjective_transfer
public import Theorems.Thm_UlmsTheorem_isProper_iff_forall_not_mem_succ
public import Theorems.Thm_UlmsTheorem_mem_pImage
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_add_one_iff
public import Theorems.Thm_UlmsTheorem_pHeight_zero
public import Theorems.Thm_UlmsTheorem_pOrder_zero
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
namespace UlmsTheorem
theorem _root_.solution
    {α : Ordinal.{0}} (s : UlmStageAt p (G := G) (H := H) α)
    {x : G}
    (hinv :
      ulmInvariant p α (G := G) = ulmInvariant p α (G := H))
    (hpxA : p • x ∈ s.A)
    (hxα : x ∈ ulmSubgroup p α (G := G))
    (hxSucc : x ∉ ulmSubgroup p (Order.succ α) (G := G))
    (hxProper : IsProper p s.A x)
    (hcaseII :
      p • x ∈ ulmSubgroup p (Order.succ (Order.succ α)) (G := G)) :
    ∃ w : H,
      p • w = (s.e ⟨p • x, hpxA⟩ : H) ∧
      w ∈ ulmSubgroup p α (G := H) ∧
      w ∉ ulmSubgroup p (Order.succ α) (G := H) ∧
      IsProper p s.B w := by
  -- Case II gives `p • x = p • v` with `v ∈ G_{α+1}`, so `q = x - v` is a socle
  -- element of exact height `α`, still proper over the stage.
  obtain ⟨v, hvSucc, hpv⟩ := (ulmSubgroup_succ p (Order.succ α) (G := G)) ▸ hcaseII
  let q : G := x - v
  have hpq : p • q = 0 := by simp [q, smul_sub, hpv]
  have hqα : q ∈ ulmSubgroup p α (G := G) :=
    (ulmSubgroup p α).sub_mem hxα (ulmSubgroup_antitone p (Order.le_succ α) hvSucc)
  have hqSucc : q ∉ ulmSubgroup p (Order.succ α) (G := G) := fun hq ↦ hxSucc <| by
    rw [show x = q + v by simp [q]]
    exact (ulmSubgroup p (Order.succ α)).add_mem hq hvSucc
  have hqProper : IsProper p s.A q :=
    (isProper_iff_forall_not_mem_succ p s.A hqα hqSucc).2 fun a hqa ↦
      (isProper_iff_forall_not_mem_succ p s.A hxα hxSucc).1 hxProper a <| by
        rw [show x + (a : G) = q + (a : G) + v by simp [q]; abel]
        exact (ulmSubgroup p (Order.succ α)).add_mem hqa hvSucc
  -- So the source Kaplansky map misses a class; equal Ulm invariants transfer
  -- that room to the target side, producing a proper socle element `w₀`.
  obtain ⟨w₀, hw₀P, hw₀Succ, hw₀Proper⟩ :=
    (kaplanskyMap_not_surjective_iff_proper p s.B α).1
      (kaplansky_not_surjective_transfer p s hinv
        ((kaplanskyMap_not_surjective_iff_proper p s.A α).2
          ⟨q, (mem_pSocleAt p α q).2 ⟨hpq, hqα⟩, hqSucc, hqProper⟩))
  obtain ⟨hpw₀, hw₀α⟩ := (mem_pSocleAt p α w₀).1 hw₀P
  -- The image of `p • x` lies in `H_{α+2}`, so it is `p • w₂` with `w₂ ∈ H_{α+1}`;
  -- adding the socle element gives a root of exact height `α`.
  obtain ⟨w₂, hw₂Succ, hpw₂⟩ :=
    (ulmSubgroup_succ p (Order.succ α) (G := H)) ▸ (s.hφ_succSucc ⟨p • x, hpxA⟩).mp hcaseII
  let w : H := w₀ + w₂
  have hpw : p • w = (s.e ⟨p • x, hpxA⟩ : H) := by simp [w, smul_add, hpw₀, hpw₂]
  have hwα : w ∈ ulmSubgroup p α (G := H) :=
    (ulmSubgroup p α).add_mem hw₀α (ulmSubgroup_antitone p (Order.le_succ α) hw₂Succ)
  have hwSucc : w ∉ ulmSubgroup p (Order.succ α) (G := H) := fun hw ↦ hw₀Succ <| by
    rw [show w₀ = w - w₂ by simp [w]]
    exact (ulmSubgroup p (Order.succ α)).sub_mem hw hw₂Succ
  refine ⟨w, hpw, hwα, hwSucc, ?_⟩
  -- `w` and `w₀` differ by `w₂ ∈ H_{α+1}`, so `w` inherits `w₀`'s properness.
  refine (isProper_iff_forall_not_mem_succ p s.B hwα hwSucc).2 fun t hwt ↦
    (isProper_iff_forall_not_mem_succ p s.B hw₀α hw₀Succ).1 hw₀Proper t ?_
  rw [show w₀ + (t : H) = w + (t : H) - w₂ by simp [w]; abel]
  exact (ulmSubgroup p (Order.succ α)).sub_mem hwt hw₂Succ
end UlmsTheorem
