-- Prove2me | solution 1 for P2M_MatchingLogic_Sorted__3_not_derives__3_29a4e105aa74
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:16.161798+00:00
-- url     : https://prove2.me/submissions/a52bb97a-1343-40eb-a471-57708ba1974d

module
public import Definitions.Def_LeanPool_MatchingLogic_Sorted
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Definitions.Def_LeanPool_MatchingLogic_EntryPoints
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Definitions.Def_LeanPool_MatchingLogic_SortedProof
public import Theorems.Thm_MatchingLogic_Sorted_feedsStar_a_only_a
public import Theorems.Thm_MatchingLogic_Sorted_mprovable_empty_of_not_feeds
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
open MatchingLogic.Sorted
variable {S : MSignature} {Var : Type} [DecidableEq S.Srt] [DecidableEq Var]
namespace MatchingLogic.Sorted
theorem _root_.solution (hS : MSoundness S3 Var) (x y : Var) (hxy : x ≠ y) :
    ¬ MProvable (Γ3 (Var := Var) x y) (φ3 (Var := Var) x y) := by
  intro hprov
  have hnotfeed : ¬ FeedsStar S3 Srt3.a Srt3.c := by
    intro hfeed
    have hac := feedsStar_a_only_a Srt3.c hfeed
    cases hac
  have hempty : MProvable (∅ : Set (MPattern S3 Var Srt3.a))
      (φ3 (Var := Var) x y) :=
    mprovable_empty_of_not_feeds _ _ hnotfeed hprov
  have hvalid : MGlobalCons (∅ : Set (MPattern S3 Var Srt3.a))
      (φ3 (Var := Var) x y) :=
    hS _ _ hempty
  let M : MModel S3 :=
    { carrier := fun _ => Bool
      nonempty := fun _ => ⟨false⟩
      interp := fun σ a =>
        match σ with
        | .f => ∅
        | .g => {a 0} }
  have hsat : M.Sat (φ3 (Var := Var) x y) := by
    apply hvalid M
    intro γ hγ
    exact hγ.elim
  let ρ : MVal M Var := fun _ _ => false
  have htotal := hsat ρ
  have hfalse : (false : Bool) ∈ mdenote M ρ (φ3 (Var := Var) x y) := by
    rw [htotal]
    trivial
  have hfalse' :
      ((∀ f : Fin 1 → Bool,
          f 0 = false → ∃ g : Fin 1 → Bool, g 0 = false) ∧
          (∀ f : Fin 1 → Bool, f 0 = false → f 0 = true) ∧
            ∀ f : Fin 1 → Bool,
              f 0 = true → f 0 = false → ∃ g : Fin 1 → Bool, g 0 = false) ∧
        (∀ f : Fin 1 → Bool,
          f 0 = true → f 0 = false → ∃ g : Fin 1 → Bool, g 0 = false) ∧
          ∀ f : Fin 1 → Bool, f 0 = true := by
    simpa [mdenote, MModel.app, mupdate, M, hxy] using hfalse
  have hcontra := hfalse'.2.2 (fun _ => false)
  exact Bool.noConfusion hcontra
end MatchingLogic.Sorted
