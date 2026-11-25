-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.wallAlg_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:56:16.354813+00:00
-- url     : https://prove2.me/submissions/3a347d26-390f-40f6-8a89-58604341b5ea

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PWallAlgA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PWallAlg
import Theorems.Thm_PositivityTheory_Rg_Cz_WallAlgP_alt_mem
import Theorems.Thm_PositivityTheory_Rg_Cz_WallAlgP_alt_zero
import Theorems.Thm_PositivityTheory_Rg_Cz_WallAlgP_card_highS
import Theorems.Thm_PositivityTheory_Rg_Cz_WallAlgP_card_lowS
import Theorems.Thm_PositivityTheory_Rg_Cz_WallAlgP_contr
import Theorems.Thm_PositivityTheory_Rg_Cz_WallAlgP_eigen
import Theorems.Thm_PositivityTheory_Rg_Cz_WallAlgP_eigen_val
import Theorems.Thm_PositivityTheory_Rg_Cz_WallAlgP_mem_firstG
import Theorems.Thm_PositivityTheory_Rg_Cz_WallAlgP_om_alt
import Theorems.Thm_PositivityTheory_Rg_Cz_WallAlgP_outer
import Theorems.Thm_PositivityTheory_Rg_Cz_WallAlgP_pm_alt_first
import Theorems.Thm_PositivityTheory_Rg_Cz_WallAlgP_symm_sum
import Theorems.Thm_PositivityTheory_Rg_Cz_WallAlgP_trace_rel
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



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open WallAlgP
namespace PositivityTheory.Rg.Cz
theorem _root_.solution (hA : TensorGl) (_hJ : JMComm) (hQ : QdetFacts) (hS : Spectrum) : WallAlg := by
  unfold WallAlg
  intro n M _ _ E₁ E₂ h₁ h₂ hcomm s₁ s₂ c hc₁ hc₂ m X hX hperm hOm htot
  obtain ⟨ξ0, hξ0X, hξ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hX
  have eqA : (n:ℂ) * (s₁ + s₂) + n * (n - 1) + m = n * c := by
    have tr₁ := (hQ n M E₁ h₁).2.2.1 _ hc₁
    have tr₂ := (hQ n M E₂ h₂).2.2.1 _ hc₂
    have key1 := trace_rel E₁ E₂ c _ _ ξ0 tr₁ tr₂ (fun a b => htot a b ξ0 hξ0X)
    have e := smul_left_injective ℂ hξ0 key1
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at e
    linear_combination e
  refine ⟨eqA, fun hm => ?_⟩
  have hOmC : ∀ (σ : Equiv.Perm (Fin m)) (p : Fin m), pm σ * Om E₁ p = Om E₁ (σ p) * pm σ :=
    (hA n M (Fin m) E₁ h₁ Finset.univ).2.2.2
  have key : ∀ k, k < n → k ≤ m → (∃ ξ ∈ X, alt (firstG m k) ξ ≠ 0) →
      k < m ∧ ∃ ξ ∈ X, alt (firstG m (k + 1)) ξ ≠ 0 := by
    intro k hkn hkm hPk
    by_contra hneg
    have hout : ∀ ξ ∈ X, ∀ i : Fin m, k ≤ (i:ℕ) →
        ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), pm (Equiv.swap j i) (alt (firstG m k) ξ) = alt (firstG m k) ξ := by
      intro ξ hξ i hi
      have hk : k < m := lt_of_le_of_lt hi i.isLt
      have hz : ∀ η ∈ X, alt (firstG m (k + 1)) η = 0 := by
        intro η hη
        by_contra hne
        exact hneg ⟨hk, η, hη, hne⟩
      exact outer hk X hperm hz ξ hξ i hi
    have hsw : ∀ ξ : TV n M (Fin m), ∀ i j : Fin m, i ≠ j → (i:ℕ) < k → (j:ℕ) < k →
        pm (Equiv.swap i j) (alt (firstG m k) ξ) = -alt (firstG m k) ξ := by
      intro ξ i j hij hi hj
      have hmem : Equiv.swap i j ∈ firstG m k := by
        rw [mem_firstG]
        intro l hl
        apply Equiv.swap_apply_of_ne_of_ne
        · intro h
          rw [h] at hl
          omega
        · intro h
          rw [h] at hl
          omega
      rw [pm_alt_first _ hmem, Equiv.Perm.sign_swap hij]
      simp
    have hinv : ∀ y ∈ X.map (alt (firstG m k)),
        (∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), xJ E₁ j) y ∈ X.map (alt (firstG m k)) := by
      intro y hy
      obtain ⟨ξ, hξ, rfl⟩ := Submodule.mem_map.mp hy
      simp only [xJ, LinearMap.sum_apply, LinearMap.add_apply, Finset.sum_add_distrib]
      refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun j hj => Submodule.sum_mem _ fun i hi => ?_)
      · rw [← om_alt E₁ hOmC k ξ]
        exact Submodule.mem_map_of_mem (Submodule.sum_mem _ fun j _ => hOm j ξ hξ)
      · have hi' := (Finset.mem_filter.mp hi).2
        have hj' := (Finset.mem_filter.mp hj).2
        rw [hsw ξ i j (ne_of_lt hi') (lt_trans (show (i:ℕ) < (j:ℕ) from hi') hj') hj']
        exact Submodule.neg_mem _ (Submodule.mem_map_of_mem hξ)
    obtain ⟨ξ1, hξ1X, hξ1⟩ := hPk
    obtain ⟨L₁, hL₁⟩ := (hS n M E₁ h₁ (fun _ => s₁) s₁ hc₁ (fun _ => ⟨0, by simp⟩) m).1 k hkm
    obtain ⟨L₂, hL₂⟩ := (hS n M E₂ h₂ (fun _ => s₂) s₂ hc₂ (fun _ => ⟨0, by simp⟩) m).1 k hkm
    obtain ⟨w, hwY, hw0, r₁, hw1⟩ := eigen (X.map (alt (firstG m k))) _ hinv
      (fun r : ℕ => (k:ℂ) * s₁ + r) L₁ hL₁ (alt (firstG m k) ξ1) (Submodule.mem_map_of_mem hξ1X) hξ1
    obtain ⟨ζ, hζ, rfl⟩ := Submodule.mem_map.mp hwY
    have hwX : alt (firstG m k) ζ ∈ X := alt_mem X hperm ζ hζ
    have hw := fun a b => htot a b _ hwX
    set w := alt (firstG m k) ζ with hwdef
    have hT : ∀ E : Fin n → Fin n → Module.End ℂ M, (∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), xJ E j) w =
        ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), Om E j w +
          ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), ∑ i ∈ Finset.univ.filter (fun i : Fin m => i < j), pm (Equiv.swap i j) w := by
      intro E
      simp only [xJ, LinearMap.sum_apply, LinearMap.add_apply, Finset.sum_add_distrib]
    have hsplit : ∀ j : Fin m, (j:ℕ) < k →
        ∑ p ∈ Finset.univ.filter (fun p : Fin m => p ≠ j), pm (Equiv.swap j p) w =
          ∑ p ∈ Finset.univ.filter (fun p : Fin m => (p:ℕ) < k ∧ p ≠ j), pm (Equiv.swap j p) w +
            ∑ p ∈ Finset.univ.filter (fun p : Fin m => k ≤ (p:ℕ)), pm (Equiv.swap j p) w := by
      intro j hj
      rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases h1 : p = j
      · subst h1
        simp [not_le.mpr hj]
      · by_cases h2 : (p:ℕ) < k
        · simp [h1, h2, not_le.mpr h2]
        · simp [h1, h2, not_lt.mp h2]
    have e1 : ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), ∑ p ∈ Finset.univ.filter (fun p : Fin m => p ≠ j), pm (Equiv.swap j p) w =
        ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), (∑ p ∈ Finset.univ.filter (fun p : Fin m => (p:ℕ) < k ∧ p ≠ j), pm (Equiv.swap j p) w +
            ∑ p ∈ Finset.univ.filter (fun p : Fin m => k ≤ (p:ℕ)), pm (Equiv.swap j p) w) :=
      Finset.sum_congr rfl fun j hj => hsplit j (Finset.mem_filter.mp hj).2
    have e2 : ∑ p ∈ Finset.univ.filter (fun p : Fin m => k ≤ (p:ℕ)), ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), pm (Equiv.swap j p) w =
        ∑ p ∈ Finset.univ.filter (fun p : Fin m => k ≤ (p:ℕ)), w :=
      Finset.sum_congr rfl fun p hp => hout ζ hζ p (Finset.mem_filter.mp hp).2
    have e3 : ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), ∑ p ∈ Finset.univ.filter (fun p : Fin m => (p:ℕ) < k ∧ p ≠ j), pm (Equiv.swap j p) w =
        2 • ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), ∑ i ∈ Finset.univ.filter (fun i : Fin m => i < j), pm (Equiv.swap i j) w :=
      symm_sum (fun i j => pm (Equiv.swap i j) w) (fun i j => by simp only [Equiv.swap_comm i j])
    have hmid : ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), ∑ p ∈ Finset.univ.filter (fun p : Fin m => p ≠ j), pm (Equiv.swap j p) w =
        2 • ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), ∑ i ∈ Finset.univ.filter (fun i : Fin m => i < j), pm (Equiv.swap i j) w +
          ((m:ℂ) - k) • w := by
      rw [e1, Finset.sum_add_distrib, e3, Finset.sum_comm, e2, Finset.sum_const, card_highS hkm,
        ← Nat.cast_smul_eq_nsmul ℂ (m - k), Nat.cast_sub hkm]
    have hsum : ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k),
        (Om E₁ j w + Om E₂ j w + ∑ p ∈ Finset.univ.filter (fun p : Fin m => p ≠ j), pm (Equiv.swap j p) w + (n:ℂ) • w) =
          ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), c • w :=
      Finset.sum_congr rfl fun j _ => contr E₁ E₂ c w hw j
    simp only [Finset.sum_add_distrib, Finset.sum_const, card_lowS hkm] at hsum
    rw [hmid] at hsum
    have h1 := hw1
    rw [hT E₁] at h1
    have hT2 : (∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), xJ E₂ j) w =
        ((k:ℂ) * c - k * n - (m - k) - ((k:ℂ) * s₁ + r₁)) • w := by
      rw [hT E₂]
      linear_combination (norm := module) hsum - h1
    obtain ⟨r₂, hr₂⟩ := eigen_val _ (fun r : ℕ => (k:ℂ) * s₂ + r) L₂ hL₂ w hw0 _ hT2
    have hr : (k:ℂ) * c - k * n - (m - k) - ((k:ℂ) * s₁ + r₁) = k * s₂ + r₂ := hr₂
    have hfin : (m:ℂ) * k = m * n + n * (r₁ + r₂) := by
      linear_combination (n:ℂ) * hr + (k:ℂ) * eqA
    have hnat : m * k = m * n + n * (r₁ + r₂) := by exact_mod_cast hfin
    have h3 : m * (k + 1) ≤ m * n := Nat.mul_le_mul_left m hkn
    nlinarith [Nat.zero_le (n * (r₁ + r₂))]
  have hall : ∀ k, k ≤ n → k ≤ m ∧ ∃ ξ ∈ X, alt (firstG m k) ξ ≠ 0 := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨Nat.zero_le _, ξ0, hξ0X, by rwa [alt_zero]⟩
    | succ k ih =>
      intro hk
      obtain ⟨hkm, hP⟩ := ih (Nat.le_of_succ_le hk)
      exact key k (Nat.lt_of_succ_le hk) hkm hP
  exact hall n le_rfl
end PositivityTheory.Rg.Cz
