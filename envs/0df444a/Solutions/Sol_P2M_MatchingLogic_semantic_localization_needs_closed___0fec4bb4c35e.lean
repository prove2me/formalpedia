-- Prove2me | solution 1 for P2M_MatchingLogic_semantic_localization_needs_closed___0fec4bb4c35e
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:45:24.59462+00:00
-- url     : https://prove2.me/submissions/09065a1f-c1dc-418f-a16b-874c6cf8d172

module
public import Definitions.Def_LeanPool_MatchingLogic_Localization
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Definitions.Def_LeanPool_MatchingLogic_Independence
public import Theorems.Thm_MatchingLogic_FV_app
public import Theorems.Thm_MatchingLogic_FV_bot
public import Theorems.Thm_MatchingLogic_FV_box
public import Theorems.Thm_MatchingLogic_FV_boxes
public import Theorems.Thm_MatchingLogic_FV_dia
public import Theorems.Thm_MatchingLogic_FV_ex
public import Theorems.Thm_MatchingLogic_FV_imp
public import Theorems.Thm_MatchingLogic_FV_var
public import Theorems.Thm_MatchingLogic_Model_reachWord_cons
public import Theorems.Thm_MatchingLogic_Model_reachWord_nil
public import Theorems.Thm_MatchingLogic_boxes_cons
public import Theorems.Thm_MatchingLogic_boxes_nil
public import Theorems.Thm_MatchingLogic_denote_al
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_bot
public import Theorems.Thm_MatchingLogic_denote_ex
public import Theorems.Thm_MatchingLogic_denote_imp
public import Theorems.Thm_MatchingLogic_denote_var
attribute [local simp] MatchingLogic.FV_app
attribute [local simp] MatchingLogic.FV_bot
attribute [local simp] MatchingLogic.FV_box
attribute [local simp] MatchingLogic.FV_boxes
attribute [local simp] MatchingLogic.FV_dia
attribute [local simp] MatchingLogic.FV_ex
attribute [local simp] MatchingLogic.FV_imp
attribute [local simp] MatchingLogic.FV_var
attribute [local simp] MatchingLogic.Model.reachWord_cons
attribute [local simp] MatchingLogic.Model.reachWord_nil
attribute [local simp] MatchingLogic.boxes_cons
attribute [local simp] MatchingLogic.boxes_nil
attribute [local simp] MatchingLogic.denote_app
attribute [local simp] MatchingLogic.denote_bot
attribute [local simp] MatchingLogic.denote_ex
attribute [local simp] MatchingLogic.denote_imp
attribute [local simp] MatchingLogic.denote_var



set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
namespace MatchingLogic
theorem _root_.solution :
    ¬ (∀ (S : Signature) (Var : Type) (_ : DecidableEq Var)
         (Γ : Set (Pattern S Var)) (φ : Pattern S Var), Closed φ →
         (GlobalCons Γ φ ↔ LocalCons (localize Γ) φ)) := by
  intro hall
  let S₀ : Signature := ⟨Empty, fun e => Empty.elim e⟩
  let Γ : Set (Pattern S₀ Bool) := {Pattern.var false}
  let φ : Pattern S₀ Bool :=
    Pattern.al false (Pattern.al true (.imp (.var false) (.var true)))
  have hφ : Closed φ := by
    simp [φ, Closed]
  have hglobal : GlobalCons Γ φ := by
    intro M hM ρ
    have hone : ∀ a b : M.carrier, a = b := by
      intro a b
      have htotal := hM (.var false) (by simp [Γ]) (fun _ => a)
      have hb : b ∈ M.denote (fun _ : Bool => a) (.var false) := by
        rw [htotal]
        exact Set.mem_univ b
      have hba : b = a := by simpa using hb
      exact hba.symm
    unfold Model.Total
    apply Set.eq_univ_iff_forall.mpr
    intro u
    change u ∈ M.denote ρ
      (Pattern.al false (Pattern.al true (.imp (.var false) (.var true))))
    rw [denote_al]
    simp only [Set.mem_iInter]
    intro a
    rw [denote_al]
    simp only [Set.mem_iInter]
    intro b
    simp only [denote_imp, Set.mem_union, Set.mem_compl_iff, denote_var,
      Set.mem_singleton_iff]
    right
    simpa using hone u b
  have hnotlocal : ¬LocalCons (localize Γ) φ := by
    intro hlocal
    let M₀ : Model S₀ :=
      { carrier := Bool
        nonempty := ⟨false⟩
        interp := fun e => Empty.elim e }
    let ρ₀ : Bool → Bool := fun _ => false
    have hwΓ : false ∈ M₀.denoteSet ρ₀ (localize Γ) := by
      simp only [Model.denoteSet, Set.mem_iInter]
      rintro ψ ⟨γ, hγ, p, rfl⟩
      have hγ' : γ = Pattern.var false := by simpa [Γ] using hγ
      subst γ
      cases p with
      | nil => rfl
      | cons e p => exact Empty.elim e.1
    have hwφ := hlocal M₀ ρ₀ hwΓ
    change false ∈ M₀.denote ρ₀
      (Pattern.al false (Pattern.al true (.imp (.var false) (.var true)))) at hwφ
    rw [denote_al] at hwφ
    simp only [Set.mem_iInter] at hwφ
    have h₁ := hwφ false
    rw [denote_al] at h₁
    simp only [Set.mem_iInter] at h₁
    have h₂ := h₁ true
    simp [M₀, ρ₀] at h₂
  exact hnotlocal ((hall S₀ Bool inferInstance Γ φ hφ).mp hglobal)
end MatchingLogic
