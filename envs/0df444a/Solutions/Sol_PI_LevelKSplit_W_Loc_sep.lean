-- Prove2me | solution 1 for PI.LevelKSplit.W.Loc.sep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:48:37.386809+00:00
-- url     : https://prove2.me/submissions/f1103d30-5b2c-4b9c-aa49-40ec4e3ec1e2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MulVecSpanStable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace PI.LevelKSplit.W.Loc
open Submodule
variable {O B : Type} [CommRing O] [CommRing B] [Algebra O B] {n r : ℕ}
private theorem sep_lemma' (c v : Fin r → Fin n → B)
    (h : ∀ a b, c b ⬝ᵥ v a = if a = b then 1 else 0) (g : Fin n → B)
    (hg : g ∈ span B (Set.range v)) : g = ∑ a, (c a ⬝ᵥ g) • v a := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a', rfl⟩ := hx
    simp [h]
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [dotProduct_add, add_smul, Finset.sum_add_distrib]
    rw [← hx, ← hy]
  | smul s x _ hx =>
    simp only [dotProduct_smul, smul_eq_mul, mul_smul]
    rw [← Finset.smul_sum, ← hx]
private theorem units_eq_of_res_eq_of_le_iSup (c v : Fin r → Fin n → B) (h : ∀ a b, c b ⬝ᵥ v a = 0) (g : Fin n → B)
    (hg : g ∈ span B (Set.range v)) (b : Fin r) : c b ⬝ᵥ g = 0 := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a', rfl⟩ := hx
    exact h _ _
  | zero => simp
  | add x y _ _ hx hy => rw [dotProduct_add, hx, hy, add_zero]
  | smul s x _ hx => rw [dotProduct_smul, hx, smul_zero]
end PI.LevelKSplit.W.Loc
end

set_option autoImplicit false
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.Loc
open Submodule
variable {O B : Type} [CommRing O] [CommRing B] [Algebra O B] {n r : ℕ}
namespace PI.LevelKSplit.W.Loc
theorem _root_.solution (e f ce cf : Fin r → Fin n → B)
    (hee : ∀ a b, ce b ⬝ᵥ e a = 0)
    (hef : ∀ a b, ce b ⬝ᵥ f a = if a = b then 1 else 0)
    (hfe : ∀ a b, cf b ⬝ᵥ e a = if a = b then 1 else 0)
    (GX GW GY : Set (Fin n → B))
    (hGX : GX ⊆ span B (Set.range e)) (hGY : GY ⊆ span B (Set.range f))
    (hGW : ∀ w ∈ GW, ∀ b, ce b ⬝ᵥ w = 0 ∧ cf b ⬝ᵥ w = 0)
    (z y : Fin n → B) (hz : ∀ b, ce b ⬝ᵥ z = 0 ∧ cf b ⬝ᵥ z = 0)
    (hy : y ∈ span O (GX ∪ GW ∪ GY)) (hzy : z - y ∈ span B (Set.range e)) :
    z ∈ span O (GX ∪ GW ∪ GY) := by
  rw [Submodule.span_union, Submodule.span_union] at hy
  obtain ⟨s, hs, u, hu, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨x, hx, w, hw, rfl⟩ := Submodule.mem_sup.mp hs
  have hxB : x ∈ span B (Set.range e) :=
    Submodule.span_le.mpr hGX (Submodule.span_le_restrictScalars O B GX hx)
  have huB : u ∈ span B (Set.range f) :=
    Submodule.span_le.mpr hGY (Submodule.span_le_restrictScalars O B GY hu)
  have hwW' : ∀ v ∈ span O GW, ∀ b, ce b ⬝ᵥ v = 0 ∧ cf b ⬝ᵥ v = 0 := by
    intro v0 hv0 b
    induction hv0 using Submodule.span_induction with
    | mem v hv => exact hGW v hv b
    | zero => simp
    | add v v' _ _ h1 h2 => simp [dotProduct_add, h1.1, h1.2, h2.1, h2.2]
    | smul o v _ h1 => simp [dotProduct_smul, h1.1, h1.2]
  have hwW := hwW' w hw
  have hceu : ∀ b, ce b ⬝ᵥ u = 0 := by
    intro b
    have h2 : ce b ⬝ᵥ (z - (x + w + u)) = 0 := units_eq_of_res_eq_of_le_iSup ce e hee _ hzy b
    have h3 : ce b ⬝ᵥ x = 0 := units_eq_of_res_eq_of_le_iSup ce e hee _ hxB b
    rw [dotProduct_sub, dotProduct_add, dotProduct_add, (hz b).1, h3, (hwW b).1] at h2
    linear_combination -h2
  have hu0 : u = 0 := by
    rw [sep_lemma' ce f hef u huB]
    simp [hceu]
  have hzy' := sep_lemma' cf e hfe _ hzy
  have hxe := sep_lemma' cf e hfe x hxB
  have hcoef : ∀ a, cf a ⬝ᵥ (z - (x + w + u)) = -(cf a ⬝ᵥ x) := by
    intro a
    rw [hu0, dotProduct_sub, dotProduct_add, dotProduct_add, (hz a).2, (hwW a).2, dotProduct_zero]
    ring
  have hzx : z - (x + w + u) = -x := by
    rw [hzy']
    simp_rw [hcoef, neg_smul, Finset.sum_neg_distrib]
    rw [← hxe]
  rw [hu0, add_zero, sub_eq_iff_eq_add] at hzx
  rw [hzx, neg_add_cancel_left]
  exact Submodule.span_mono (fun v hv => Or.inl (Or.inr hv)) hw
end PI.LevelKSplit.W.Loc
