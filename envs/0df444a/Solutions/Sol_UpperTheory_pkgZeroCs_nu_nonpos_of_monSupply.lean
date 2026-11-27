-- Prove2me | solution 1 for UpperTheory.pkgZeroCs_nu_nonpos_of_monSupply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:38:03.64272+00:00
-- url     : https://prove2.me/submissions/ce77416b-19be-4dac-971c-2d8bab3c14c7

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_RowDefs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsCutIntoBoundedGroupsFinset
import Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_PkgZeroCsNuNonposOfMonSupply
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum
import Theorems.Thm_GlobalTheory_exists_cut_columns_bounded_width

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Formalism.L2.FormalSeriesBounds UpperTheory.G2
open Formalism.IncomingBounds in

private theorem cut (K s B : ℕ) (e : ℕ → ℕ) : ∃ pc : Fin s → ℕ → ℕ,
    (∀ u, ∑ k ∈ Finset.Icc 1 K, pc u k ≤ B) ∧
    (∑ k ∈ Finset.Icc 1 K, e k ≤ s * B → (∀ k, e k ≠ 0 → 1 ≤ k ∧ k ≤ K) → ∀ k, ∑ u, pc u k = e k) := by
  by_cases h : ∑ k ∈ Finset.Icc 1 K, e k ≤ s * B
  · obtain ⟨pc, h1, h2, h3⟩ := GlobalTheory.exists_cut_columns_bounded_width K s B e h
    refine ⟨pc, h2, fun _ hs k => ?_⟩
    by_cases hk : k ∈ Finset.Icc 1 K
    · exact h1 k hk
    · have : e k = 0 := by
        by_contra h0
        exact hk (Finset.mem_Icc.2 (hs k h0))
      rw [this]
      exact Finset.sum_eq_zero fun u _ => h3 u k hk
  · exact ⟨fun _ _ => 0, by simp, fun h' => absurd h' h⟩
open Formalism.IncomingBounds in

private theorem monAl_le_first (K rk : ℕ) (e : ℕ → ℕ) (ρ : ℕ) :
    monAl K rk e ρ ≤ ∑ k ∈ Finset.Icc 1 K, e k := by
  unfold monAl
  apply Finset.sum_le_sum_of_subset
  intro k hk
  rw [Finset.mem_Icc] at hk ⊢
  exact ⟨le_trans (Nat.le_add_left 1 ρ) hk.1, le_trans hk.2 (min_le_left _ _)⟩
end

set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds UpperTheory.G2
namespace UpperTheory
theorem _root_.solution :
    RF.MONSupply → ∀ (P : RF.Par) (l : ℕ) (Pk : PkgZeroCs P l), Pk.ν ≤ 0 := by
  intro hM P l Pk
  have hl : Pk.R.V.l = l := Pk.R.hVl
  have hl2 : 2 ≤ l := hl ▸ Pk.R.V.l_prime.two_le
  have hc := fun (o : ↥Pk.Z) (σ : ZMod (2 * P.d)) => cut Pk.K Pk.s (l - 1) (Pk.ga o σ)
  choose pc hpcB hpcE using hc
  have hE : ∀ o σ k, ∑ u, pc o σ u k = Pk.ga o σ k := fun o σ =>
    hpcE o σ (Pk.first o σ) (fun k hk => ⟨(Pk.supp o σ k hk).1, (Pk.supp o σ k hk).2.2⟩)
  let blk : ↥Pk.Z → ZMod (2 * P.d) → Fin Pk.s → RF.GlobalTheory (2 * P.d) := fun o σ u =>
    RF.GlobalTheory.mon 0 (fun a k => if a = σ then pc o σ u k else 0) Pk.K
  let L : ↥Pk.Z → List (RF.GlobalTheory (2 * P.d) × ℝ) := fun o =>
    (Finset.univ : Finset (ZMod (2 * P.d) × Fin Pk.s)).toList.map (fun p => (blk o p.1 p.2, (0 : ℝ)))
  have hmem : ∀ o, ∀ q ∈ L o, ∃ σ u, q = (blk o σ u, (0 : ℝ)) := by
    intro o q hq
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hq
    exact ⟨p.1, p.2, rfl⟩
  have hzero : ∑ o, (List.map Prod.snd (L o)).sum = 0 := by
    apply Finset.sum_eq_zero
    intro o _
    simp [L]
  rw [← hzero]
  apply Pk.val L
  · intro o q hq
    obtain ⟨σ, u, rfl⟩ := hmem o q hq
    apply (hM _ _ _ _ _ (Pk.R.X o) (Pk.R.F o) 0 _ Pk.K).2
    intro a ρ
    rw [hl]
    calc monAl Pk.K ((Pk.R.X o).rkF 0 a) (fun k => if a = σ then pc o σ u k else 0) ρ
        ≤ ∑ k ∈ Finset.Icc 1 Pk.K, (fun k => if a = σ then pc o σ u k else 0) k := monAl_le_first _ _ _ _
      _ ≤ l - 1 := by
        by_cases ha : a = σ
        · simp only [ha, if_true]
          exact hpcB o σ u
        · simp [ha]
      _ < l := by omega
  · intro o q hq g e N hqe
    obtain ⟨σ, u, rfl⟩ := hmem o q hq
    obtain ⟨-, rfl, -⟩ := RF.GlobalTheory.mon.inj hqe
    exact ⟨σ, fun a k ha => if_neg ha⟩
  · have hrow : ∀ o, (List.map (fun q => RF.GlobalTheory.what₂ (Pk.R.X o).n q.1) (L o)).sum = 2 * P.d * Pk.s * Pk.K := by
      intro o
      simp [L, blk, RF.GlobalTheory.what₂]
    simp only [hrow]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul]
    calc 2 * (Pk.Z.card * (2 * P.d * Pk.s * Pk.K)) = 4 * Pk.K * Pk.s * (Pk.Z.card * P.d) := by ring
      _ ≤ Pk.nW := Pk.what₂
  · intro o s k
    simp [L, blk, RF.GlobalTheory.wt]
    split_ifs with hk
    · rw [Fintype.sum_prod_type, Finset.sum_eq_single s]
      · simp [hE]
      · intro b _ hb
        simp [Ne.symm hb]
      · intro hs
        exact absurd (Finset.mem_univ s) hs
    · by_contra hne
      have h3 := Pk.supp o s k (Ne.symm hne)
      exact hk ⟨h3.1, h3.2.2, h3.2.1⟩
end UpperTheory
