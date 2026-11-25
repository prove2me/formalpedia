-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.uq_exists_isometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:48:03.584842+00:00
-- url     : https://prove2.me/submissions/19d5a8ec-2b55-4a3a-8ae0-a0e3e8e0ed6b

import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_UniqueA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_uq_mem_kSpan
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_uq_kSpan_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_uq_kSpan_stable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_uq_bij
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_uq_exists_equiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped InnerProductSpace
namespace ReciprocityTheory.ChartRestriction.DS.HW
open Formalism.REAL
variable {n : ℕ}
section
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V)
end
section
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
end
section
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
private theorem eq_bot_of_KStable_of_highest_not_mem (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ)
    (w : V) (hR : KRel ε F) (hU : KUnit ε F) (hw : KHighest ε F Λ w) (hT : kSpan ε F w = ⊤)
    (S : Submodule ℂ V) (hS : KStable ε F S) (hwS : w ∉ S) : S = ⊥ := by
  classical
  obtain ⟨FU, hFUdef⟩ : ∃ FU : Fin n → Fin n → Module.End ℂ (V ⧸ S), FU = fun a b =>
      if h : ε a = ε b then S.mapQ S (F a b) (fun y hy => hS a b h y hy) else 0 := ⟨_, rfl⟩
  have hFU : ∀ a b, ε a = ε b → ∀ y, S.mkQ (F a b y) = FU a b (S.mkQ y) := by
    intro a b h y
    rw [hFUdef]
    simp only [dif_pos h]
    rfl
  have hTU : kSpan ε FU (S.mkQ w) = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨y, rfl⟩ := S.mkQ_surjective z
    have hle : kSpan ε F w ≤ (kSpan ε FU (S.mkQ w)).comap S.mkQ :=
      uq_kSpan_le ε F (uq_mem_kSpan ε FU (S.mkQ w)) (fun a b h y hy => by
        show S.mkQ (F a b y) ∈ kSpan ε FU (S.mkQ w)
        rw [hFU a b h y]
        exact uq_kSpan_stable ε FU (S.mkQ w) a b h _ hy)
    have hy : y ∈ kSpan ε F w := by rw [hT]; exact Submodule.mem_top
    exact hle hy
  have hpw : S.mkQ w ≠ 0 := by
    rwa [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have hbij := uq_bij ε F FU Λ w hR hU hw S.mkQ (fun a b h y => hFU a b h y) hpw hTU
  rw [eq_bot_iff]
  intro y hy
  have hy' : y ∈ kSpan ε F w := by rw [hT]; exact Submodule.mem_top
  have h0 : (0 : V) ∈ kSpan ε F w := Submodule.zero_mem _
  have key := hbij.1 (show (S.mkQ.domRestrict (kSpan ε F w)) ⟨y, hy'⟩ =
      (S.mkQ.domRestrict (kSpan ε F w)) ⟨0, h0⟩ by simpa using hy)
  rw [Submodule.mem_bot]
  exact congrArg Subtype.val key
end
end ReciprocityTheory.ChartRestriction.DS.HW
end
end

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open Formalism.REAL
variable {n : ℕ}
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V)
    (F' : Fin n → Fin n → Module.End ℂ V') (Λ : Fin n → ℝ) (w : V) (w' : V')
    (hR : KRel ε F) (hR' : KRel ε F') (hU : KUnit ε F) (hU' : KUnit ε F')
    (hw : KHighest ε F Λ w) (hw' : KHighest ε F' Λ w') (hw1 : ‖w‖ = 1) (hw1' : ‖w'‖ = 1)
    (hT : kSpan ε F w = ⊤) (hT' : kSpan ε F' w' = ⊤) :
    ∃ φ : V ≃ₗᵢ[ℂ] V', (∀ a b, ε a = ε b → ∀ v, φ (F a b v) = F' a b (φ v)) ∧ φ w = w' := by
  classical
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw1
  have hw0' : w' ≠ 0 := by rintro rfl; simp at hw1'
  obtain ⟨φ, hφ, hφw⟩ := uq_exists_equiv ε F F' Λ w w' hR hR' hU hU' hw hw' hw0 hw0' hT hT'
  obtain ⟨A, hA⟩ : ∃ A : Module.End ℂ V,
      A = LinearMap.adjoint (φ : V →ₗ[ℂ] V') ∘ₗ (φ : V →ₗ[ℂ] V') := ⟨_, rfl⟩
  have hAinner : ∀ u v, ⟪A u, v⟫_ℂ = ⟪φ u, φ v⟫_ℂ := by
    intro u v
    rw [hA, LinearMap.comp_apply, LinearMap.adjoint_inner_left] <;> rfl
  have hAF : ∀ a b, ε a = ε b → ∀ v, A (F a b v) = F a b (A v) := by
    intro a b hab v
    refine ext_inner_right ℂ fun u => ?_
    rw [hAinner, hφ a b hab, hU' a b hab, ← hφ b a hab.symm, ← hAinner, hU a b hab]
  haveI : Nontrivial V := ⟨⟨w, 0, hw0⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue A
  have hEst : KStable ε F (Module.End.eigenspace A c) := by
    intro a b hab v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    rw [hAF a b hab, hv, map_smul]
  have hwE : w ∈ Module.End.eigenspace A c := by
    by_contra hwE
    exact (Module.End.hasEigenvalue_iff.1 hc) (eq_bot_of_KStable_of_highest_not_mem ε F Λ w hR hU hw hT _ hEst hwE)
  have hEtop : ∀ v, A v = c • v := by
    intro v
    have h := uq_kSpan_le ε F hwE hEst
    rw [hT] at h
    exact Module.End.mem_eigenspace_iff.1 (h Submodule.mem_top)
  have hc1 : (starRingEnd ℂ) c = 1 := by
    have h1 := hAinner w w
    rw [hEtop, inner_smul_left, hφw, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hw1,
      hw1'] at h1
    simpa using h1
  have hinner : ∀ u v, ⟪φ u, φ v⟫_ℂ = ⟪u, v⟫_ℂ := by
    intro u v
    rw [← hAinner, hEtop, inner_smul_left, hc1, one_mul]
  refine ⟨φ.isometryOfInner hinner, fun a b hab v => ?_, ?_⟩
  · first | exact hφ a b hab v | simpa using hφ a b hab v
  · first | exact hφw | simpa using hφw
end ReciprocityTheory.ChartRestriction.DS.HW
