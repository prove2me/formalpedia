-- Prove2me | solution 1 for P2M_MatchingLogic_semantic_localization_of_closed___79ca4e008704
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:29:45.73612+00:00
-- url     : https://prove2.me/submissions/870b7832-bdad-4676-9783-994ccd762cb7

module
public import Definitions.Def_LeanPool_MatchingLogic_DoubleCover
public import Definitions.Def_LeanPool_MatchingLogic_Localization
public import Definitions.Def_LeanPool_MatchingLogic_Locality
public import Definitions.Def_LeanPool_MatchingLogic_Composite
public import Theorems.Thm_MatchingLogic_cover_sat_iff
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
public import Theorems.Thm_MatchingLogic_backwardClosed_denoteSet_localize
public import Theorems.Thm_MatchingLogic_boxes_cons
public import Theorems.Thm_MatchingLogic_boxes_nil
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_bot
public import Theorems.Thm_MatchingLogic_denote_closed
public import Theorems.Thm_MatchingLogic_denote_ex
public import Theorems.Thm_MatchingLogic_denote_imp
public import Theorems.Thm_MatchingLogic_denote_var
public import Theorems.Thm_MatchingLogic_globalCons_of_localCons_localize
public import Theorems.Thm_MatchingLogic_locality
public import Theorems.Thm_MatchingLogic_two_copies
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
theorem _root_.solution {Γ : Set (Pattern S Var)}
    {φ : Pattern S Var} (hΓ : ∀ γ ∈ Γ, Closed γ) :
    GlobalCons Γ φ ↔ LocalCons (localize Γ) φ := by
  classical
  constructor
  · intro hglobal M ρ w hw
    by_contra hwφ
    let C : Set M.carrier := M.denoteSet ρ (localize Γ)
    have hwC : w ∈ C := hw
    have hCdata := backwardClosed_denoteSet_localize M ρ Γ
    have hC : M.BackwardClosed C := hCdata.1
    have hCΓ : C ⊆ M.denoteSet ρ Γ := hCdata.2
    by_cases hfull : C = Set.univ
    · have hsatΓ : M.SatSet Γ := by
        intro γ hγ ρ'
        unfold Model.Total
        rw [denote_closed M (hΓ γ hγ) ρ' ρ]
        apply Set.eq_univ_iff_forall.mpr
        intro u
        have huC : u ∈ C := by
          rw [hfull]
          exact Set.mem_univ u
        have huΓ := hCΓ huC
        have huΓ' : ∀ δ, δ ∈ Γ → u ∈ M.denote ρ δ := by
          simpa only [Model.denoteSet, Set.mem_iInter] using huΓ
        exact huΓ' γ hγ
      have hsatφ := hglobal M hsatΓ ρ
      apply hwφ
      rw [hsatφ]
      exact Set.mem_univ w
    · have hne : C.Nonempty := ⟨w, hwC⟩
      obtain ⟨star, hstar⟩ := (Set.ne_univ_iff_exists_notMem C).mp hfull
      let N : Model S := cover M C hne
      have hsatΓ : N.SatSet Γ := by
        intro γ hγ
        apply (cover_sat_iff M C hC hne star hstar (hΓ γ hγ) ρ).mpr
        intro u huC
        have huΓ := hCΓ huC
        have huΓ' : ∀ δ, δ ∈ Γ → u ∈ M.denote ρ δ := by
          simpa only [Model.denoteSet, Set.mem_iInter] using huΓ
        exact huΓ' γ hγ
      let ν : Var → C × Bool := fun x =>
        if hx : ρ x ∈ C then (⟨ρ x, hx⟩, false) else (⟨w, hwC⟩, true)
      let ρ' : Var → M.carrier := fun x => proj M C star false (ν x)
      have hagree : AgreeOn C ρ ρ' := by
        intro x
        by_cases hx : ρ x ∈ C
        · exact Or.inl ⟨by simp [ρ', ν, hx, proj], hx⟩
        · exact Or.inr ⟨hx, by simp [ρ', ν, hx, proj, hstar]⟩
      have hloc := locality M hC φ ρ ρ' hagree
      have hwφ' : w ∉ M.denote ρ' φ := by
        intro hw'
        have hm : w ∈ M.denote ρ' φ ∩ C := ⟨hw', hwC⟩
        rw [← hloc] at hm
        exact hwφ hm.1
      let q : C × Bool := (⟨w, hwC⟩, false)
      have hqφ : q ∉ N.denote ν φ := by
        intro hq
        have hproj := (two_copies M C hC hne star hstar φ ν q).mp hq
        apply hwφ'
        simpa [N, q, ρ'] using hproj
      apply hqφ
      have hsatφ := hglobal N hsatΓ ν
      rw [hsatφ]
      exact Set.mem_univ q
  · exact globalCons_of_localCons_localize
end MatchingLogic
