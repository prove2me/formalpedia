-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.YoungTableau.exists_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:38:17.325607+00:00
-- url     : https://prove2.me/submissions/a043c81d-7fd1-439d-9cd9-f3602df2dafa

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PYoungA
import Theorems.Thm_PositivityTheory_Rg_Cz_YoungTableau_mem_colG
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one


section
noncomputable section
open Formalism.REAL Matrix
namespace PositivityTheory.Rg.Cz
namespace YoungTableau
section Gen
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {X : Type} [Fintype X] [DecidableEq X]
  {C : Type} [DecidableEq C]
private theorem injOn_col_fiber_of_isTab (col : X → C) (b : X → Fin n) (hT : IsTab col b) (c : C) :
    Set.InjOn b ↑(Finset.univ.filter (fun x => col x = c)) := by
  unfold IsTab at hT
  intro x hx y hy hxy
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
  exact hT.1 x y (hx.trans hy.symm) hxy
private theorem card_col_fiber_sub_le_of_isTab (col : X → C) (b : X → Fin n) (hT : IsTab col b) (x : X) :
    n - (Finset.univ.filter (fun y => col y = col x)).card ≤ (b x : ℕ) := by
  have hinj := injOn_col_fiber_of_isTab col b hT (col x)
  unfold IsTab at hT
  have hsub : Finset.Ici (b x) ⊆ (Finset.univ.filter (fun y => col y = col x)).image b := by
    intro i hi
    rw [Finset.mem_Ici] at hi
    rcases hi.lt_or_eq with hlt | heq
    · obtain ⟨q, hq, hbq⟩ := hT.2 x i hlt
      exact Finset.mem_image.mpr ⟨q, by simp [hq], hbq⟩
    · exact Finset.mem_image.mpr ⟨x, by simp, heq⟩
  have h := Finset.card_le_card hsub
  rw [Fin.card_Ici, Finset.card_image_of_injOn hinj] at h
  omega
private theorem exists_mem_col_fiber_eq_of_isTab_of_le (col : X → C) (b : X → Fin n) (hT : IsTab col b) (c : C) (j : Fin n)
    (hj : n - (Finset.univ.filter (fun y => col y = c)).card ≤ (j : ℕ)) :
    ∃ x, col x = c ∧ b x = j := by
  have hinj := injOn_col_fiber_of_isTab col b hT c
  unfold IsTab at hT
  by_contra hne
  push_neg at hne
  have hsub : (Finset.univ.filter (fun y => col y = c)).image b ⊆ Finset.Ioi j := by
    intro i hi
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [Finset.mem_Ioi]
    rcases lt_trichotomy (b x) j with hlt | heq | hgt
    · obtain ⟨q, hq, hbq⟩ := hT.2 x j hlt
      exact absurd hbq (hne q (hq.trans hx))
    · exact absurd heq (hne x hx)
    · exact hgt
  have h := Finset.card_le_card hsub
  rw [Fin.card_Ioi, Finset.card_image_of_injOn hinj] at h
  have := j.isLt
  omega
end Gen
end YoungTableau
end PositivityTheory.Rg.Cz
end
end

set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.YoungTableau
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {X : Type} [Fintype X] [DecidableEq X]
  {C : Type} [DecidableEq C]
namespace PositivityTheory.Rg.Cz.YoungTableau
theorem _root_.solution (col : X → C) (b : X → Fin n) (hT : IsTab col b) (ζ : Equiv.Perm X)
    (hJ : ColInj col (b ∘ ζ)) : ∃ π ∈ colG col, b ∘ π = b ∘ ζ := by
  unfold ColInj at hJ
  have key : ∀ p, ∃ q, col q = col p ∧ b q = b (ζ p) := by
    by_contra hne
    push_neg at hne
    obtain ⟨p0, hp0⟩ := hne
    have hsmall : (Finset.univ.filter (fun y => col y = col p0)).card < n - (b (ζ p0) : ℕ) := by
      by_contra h
      push_neg at h
      obtain ⟨q, hq, hbq⟩ := exists_mem_col_fiber_eq_of_isTab_of_le col b hT (col p0) (b (ζ p0)) (by omega)
      exact hp0 q hq hbq
    have hfib : ∀ s : Finset X,
        s.card = ∑ c ∈ Finset.univ.image col, (s.filter (fun a => col a = c)).card := by
      intro s
      apply Finset.card_eq_sum_card_fiberwise
      intro x _
      exact Finset.mem_coe.mpr (Finset.mem_image_of_mem col (Finset.mem_univ x))
    have heq : (Finset.univ.filter (fun x => b (ζ p0) < b (ζ x))).card =
        (Finset.univ.filter (fun x => b (ζ p0) < b x)).card := by
      apply Finset.card_nbij' ζ ζ.symm
      · intro x hx
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact hx
      · intro x hx
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.apply_symm_apply] at hx ⊢
        exact hx
      · intro x _
        simp
      · intro x _
        simp
    have hsubR : ∀ c, (Finset.univ.filter (fun y => col y = c)).card < n - (b (ζ p0) : ℕ) →
        (Finset.univ.filter (fun y => col y = c)).card ≤
          ((Finset.univ.filter (fun x => b (ζ p0) < b x)).filter (fun a => col a = c)).card := by
      intro c hA
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      refine ⟨?_, hx⟩
      have h2 := card_col_fiber_sub_le_of_isTab col b hT x
      rw [hx] at h2
      show (b (ζ p0) : ℕ) < b x
      omega
    have hle : ∀ c ∈ Finset.univ.image col,
        ((Finset.univ.filter (fun x => b (ζ p0) < b (ζ x))).filter (fun a => col a = c)).card ≤
        ((Finset.univ.filter (fun x => b (ζ p0) < b x)).filter (fun a => col a = c)).card := by
      intro c _
      by_cases hA : (Finset.univ.filter (fun y => col y = c)).card < n - (b (ζ p0) : ℕ)
      · calc _ ≤ (Finset.univ.filter (fun y => col y = c)).card := by
              apply Finset.card_le_card
              intro x hx
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
              exact hx.2
          _ ≤ _ := hsubR c hA
      · push_neg at hA
        calc _ ≤ (Finset.Ioi (b (ζ p0))).card := by
              apply Finset.card_le_card_of_injOn (fun x => b (ζ x))
              · intro x hx
                simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioi] at hx ⊢
                exact hx.1
              · intro x hx y hy hxy
                simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
                exact hJ x y (hx.2.trans hy.2.symm) hxy
          _ ≤ (((Finset.univ.filter (fun x => b (ζ p0) < b x)).filter (fun a => col a = c)).image b).card := by
              apply Finset.card_le_card
              intro j hj
              rw [Finset.mem_Ioi] at hj
              have hj' : (b (ζ p0) : ℕ) < j := hj
              obtain ⟨x, hx, hbx⟩ := exists_mem_col_fiber_eq_of_isTab_of_le col b hT c j (by omega)
              refine Finset.mem_image.mpr ⟨x, ?_, hbx⟩
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              refine ⟨?_, hx⟩
              rw [hbx]
              exact hj
          _ ≤ _ := Finset.card_image_le
    have hlt : ((Finset.univ.filter (fun x => b (ζ p0) < b (ζ x))).filter (fun a => col a = col p0)).card <
        ((Finset.univ.filter (fun x => b (ζ p0) < b x)).filter (fun a => col a = col p0)).card := by
      calc _ ≤ ((Finset.univ.filter (fun y => col y = col p0)).erase p0).card := by
              apply Finset.card_le_card
              intro x hx
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hx ⊢
              refine ⟨?_, hx.2⟩
              rintro rfl
              exact lt_irrefl _ hx.1
          _ < (Finset.univ.filter (fun y => col y = col p0)).card :=
              Finset.card_erase_lt_of_mem (by simp)
          _ ≤ _ := hsubR (col p0) hsmall
    have hsum := Finset.sum_lt_sum hle ⟨col p0, Finset.mem_image_of_mem col (Finset.mem_univ p0), hlt⟩
    rw [← hfib, ← hfib, heq] at hsum
    exact lt_irrefl _ hsum
  choose f hf1 hf2 using key
  have hinj : Function.Injective f := by
    intro p p' h
    apply hJ p p'
    · rw [← hf1 p, ← hf1 p', h]
    · show b (ζ p) = b (ζ p')
      rw [← hf2 p, ← hf2 p', h]
  refine ⟨Equiv.ofBijective f hinj.bijective_of_finite, ?_, ?_⟩
  · rw [mem_colG]
    intro p
    exact hf1 p
  · funext p
    exact hf2 p
end PositivityTheory.Rg.Cz.YoungTableau
