-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra.piece
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:40:48.449931+00:00
-- url     : https://prove2.me/submissions/f4086a46-1975-493a-b6bd-378a0005323d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PBlocksAlg
import Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_BlockAlgebra_common_ker
import Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_BlockAlgebra_poly_eq
import Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_BlockAlgebra_isUnit_poly
import Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_BlockAlgebra_comm_sub
import Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_BlockAlgebra_apply_eig
import Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_BlockAlgebra_spoly_monic
import Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_BlockAlgebra_spoly_natDegree
import Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_BlockAlgebra_spoly_eval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.Cz PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra
variable {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra
theorem _root_.solution [Nontrivial M] (r s : ℕ) (a b : ℕ → Module.End ℂ M) (haa : ∀ k l, Commute (a k) (a l))
    (hab : ∀ k l, Commute (a k) (b l)) (hbb : ∀ k l, Commute (b k) (b l))
    (ha : a r = 1) (hb : b s = 1) (m : Multiset ℂ) (hm : m.Nodup)
    (hrel : ∀ u : ℂ, (∑ k ∈ Finset.range (r + 1), u ^ k • a k) * (∑ l ∈ Finset.range (s + 1), u ^ l • b l) =
      (m.map (u + ·)).prod • (1 : Module.End ℂ M))
    (χa χb : ℕ → ℂ) (hna : ∀ k, IsNilpotent (a k - χa k • 1)) (hnb : ∀ l, IsNilpotent (b l - χb l • 1)) :
    ∃ σ : Multiset ℂ, σ ≤ m ∧ Multiset.card σ = r ∧ ∀ u : ℂ,
      (∑ k ∈ Finset.range (r + 1), u ^ k • a k) = (σ.map (u + ·)).prod • 1 ∧
      (∑ l ∈ Finset.range (s + 1), u ^ l • b l) = ((m - σ).map (u + ·)).prod • 1 := by
  classical

  set L : List (Module.End ℂ M) := ((List.range (r + 1)).map fun k => a k - χa k • 1) ++
    (List.range (s + 1)).map fun l => b l - χb l • 1 with hL
  have hLn : ∀ N ∈ L, IsNilpotent N := by
    intro N hN
    rcases List.mem_append.1 hN with h | h
    · obtain ⟨k, -, rfl⟩ := List.mem_map.1 h; exact hna k
    · obtain ⟨l, -, rfl⟩ := List.mem_map.1 h; exact hnb l
  have hLc : ∀ N ∈ L, ∀ N' ∈ L, Commute N N' := by
    intro N hN N' hN'
    rcases List.mem_append.1 hN with h | h <;> rcases List.mem_append.1 hN' with h' | h'
    · obtain ⟨k, -, rfl⟩ := List.mem_map.1 h; obtain ⟨l, -, rfl⟩ := List.mem_map.1 h'
      exact comm_sub (haa k l) _ _
    · obtain ⟨k, -, rfl⟩ := List.mem_map.1 h; obtain ⟨l, -, rfl⟩ := List.mem_map.1 h'
      exact comm_sub (hab k l) _ _
    · obtain ⟨k, -, rfl⟩ := List.mem_map.1 h; obtain ⟨l, -, rfl⟩ := List.mem_map.1 h'
      exact comm_sub (hab l k).symm _ _
    · obtain ⟨k, -, rfl⟩ := List.mem_map.1 h; obtain ⟨l, -, rfl⟩ := List.mem_map.1 h'
      exact comm_sub (hbb k l) _ _
  obtain ⟨y, -, hy0, hyL⟩ := common_ker L hLn hLc ⊤ top_ne_bot (fun _ _ _ _ => Submodule.mem_top)
  have hya : ∀ k ∈ Finset.range (r + 1), a k y = χa k • y := fun k hk => by
    have := hyL _ (List.mem_append_left _ (List.mem_map.2 ⟨k, List.mem_range.2 (Finset.mem_range.1 hk), rfl⟩))
    rwa [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at this
  have hyb : ∀ l ∈ Finset.range (s + 1), b l y = χb l • y := fun l hl => by
    have := hyL _ (List.mem_append_right _ (List.mem_map.2 ⟨l, List.mem_range.2 (Finset.mem_range.1 hl), rfl⟩))
    rwa [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at this
  have hχa : χa r = 1 := by
    have h1 := hya r (Finset.self_mem_range_succ r)
    rw [ha, Module.End.one_apply] at h1
    exact (smul_left_injective ℂ hy0 (h1.symm.trans (one_smul ℂ y).symm))
  have hχb : χb s = 1 := by
    have h1 := hyb s (Finset.self_mem_range_succ s)
    rw [hb, Module.End.one_apply] at h1
    exact (smul_left_injective ℂ hy0 (h1.symm.trans (one_smul ℂ y).symm))

  set pC := spoly r χa with hpC
  set pD := spoly s χb with hpD
  set S : ℂ[X] := (m.map fun x => X - C (-x)).prod with hS
  have hSe : ∀ u, S.eval u = (m.map (u + ·)).prod := fun u => by
    simp [hS, eval_multiset_prod, Multiset.map_map, sub_neg_eq_add]
  have hscal : ∀ u, pC.eval u * pD.eval u = S.eval u := by
    intro u
    have h1 := congrArg (fun T : Module.End ℂ M => T y) (hrel u)
    simp only [Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply] at h1
    rw [apply_eig s b χb y hyb, map_smul, apply_eig r a χa y hya, smul_smul] at h1
    rw [spoly_eval r χa hχa, spoly_eval s χb hχb, hSe, mul_comm]
    exact smul_left_injective ℂ hy0 h1
  have hCD : pC * pD = S := Polynomial.funext fun u => by rw [eval_mul, hscal]
  have hSm : S.Monic := monic_multiset_prod_of_monic _ _ fun x _ => monic_X_sub_C _
  have hS0 : S ≠ 0 := hSm.ne_zero
  have hSr : S.roots = m.map Neg.neg := by
    have e : (m.map fun x => X - C (-x)) = (m.map Neg.neg).map (fun x => X - C x) := by
      rw [Multiset.map_map]; rfl
    rw [hS, e, roots_multiset_prod_X_sub_C]
  have hroots : pC.roots + pD.roots = m.map Neg.neg := by
    rw [← roots_mul (hCD ▸ hS0), hCD, hSr]
  have hnd : (pC.roots + pD.roots).Nodup := hroots ▸ hm.map neg_injective
  have hdisj := (Multiset.nodup_add.1 hnd).2.2
  have hpC0 : pC ≠ 0 := (spoly_monic r χa).ne_zero
  have hpD0 : pD ≠ 0 := (spoly_monic s χb).ne_zero

  set σ := pC.roots.map Neg.neg with hσ
  have hσm : σ ≤ m := by
    have h1 : pC.roots ≤ m.map Neg.neg := hroots ▸ Multiset.le_add_right _ _
    have h2 := Multiset.map_le_map (f := Neg.neg) h1
    rwa [Multiset.map_map, show (Neg.neg ∘ Neg.neg : ℂ → ℂ) = id from funext neg_neg, Multiset.map_id] at h2
  have hσc : Multiset.card σ = r := by
    rw [hσ, Multiset.card_map, IsAlgClosed.card_roots_eq_natDegree, spoly_natDegree]
  have hσn : σ.Nodup := Multiset.nodup_of_le hσm hm
  have hCr : pC.roots = σ.map Neg.neg := by
    rw [hσ, Multiset.map_map, show (Neg.neg ∘ Neg.neg : ℂ → ℂ) = id from funext neg_neg, Multiset.map_id]
  set τ := m - σ with hτ
  have hmστ : m = σ + τ := (add_tsub_cancel_of_le hσm).symm
  have hDr : pD.roots = τ.map Neg.neg := by
    have h1 : pC.roots + pD.roots = pC.roots + τ.map Neg.neg := by
      rw [hroots, hCr, ← Multiset.map_add, ← hmστ]
    exact add_left_cancel h1
  have hτn : τ.Nodup := Multiset.nodup_of_le tsub_le_self hm
  have hmc : Multiset.card m = r + s := by
    have h1 := congrArg natDegree hCD
    rw [natDegree_mul hpC0 hpD0, spoly_natDegree, spoly_natDegree] at h1
    rw [h1, ← IsAlgClosed.card_roots_eq_natDegree, hSr, Multiset.card_map]
  have hτc : Multiset.card τ = s := by
    rw [hτ, Multiset.card_sub hσm, hmc, hσc]; omega

  have hCe : ∀ w, (∑ k ∈ Finset.range (r + 1), w ^ k * χa k) = pC.eval w := fun w => (spoly_eval r χa hχa w).symm
  have hDe : ∀ w, (∑ k ∈ Finset.range (s + 1), w ^ k * χb k) = pD.eval w := fun w => (spoly_eval s χb hχb w).symm
  have hzero : ∀ x ∈ m, (∑ k ∈ Finset.range (r + 1), (-x) ^ k • a k) * (∑ l ∈ Finset.range (s + 1), (-x) ^ l • b l) = 0 := by
    intro x hx
    rw [hrel, Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨x, hx, by ring⟩), zero_smul]
  refine ⟨σ, hσm, hσc, fun u => ⟨?_, ?_⟩⟩
  · refine poly_eq r a ha σ hσn hσc (fun x hx => ?_) u
    have hD : IsUnit (∑ l ∈ Finset.range (s + 1), (-x) ^ l • b l) := by
      refine isUnit_poly s b χb hbb hnb (-x) ?_
      rw [hDe]
      intro h0
      have h1 : -x ∈ pD.roots := (mem_roots hpD0).2 h0
      have h2 : -x ∈ pC.roots := by rw [hCr]; exact Multiset.mem_map.2 ⟨x, hx, rfl⟩
      exact Multiset.disjoint_left.1 hdisj h2 h1
    exact (hD.mul_left_eq_zero).1 (hzero x (Multiset.mem_of_le hσm hx))
  · refine poly_eq s b hb τ hτn hτc (fun x hx => ?_) u
    have hC : IsUnit (∑ k ∈ Finset.range (r + 1), (-x) ^ k • a k) := by
      refine isUnit_poly r a χa haa hna (-x) ?_
      rw [hCe]
      intro h0
      have h1 : -x ∈ pC.roots := (mem_roots hpC0).2 h0
      have h2 : -x ∈ pD.roots := by rw [hDr]; exact Multiset.mem_map.2 ⟨x, hx, rfl⟩
      exact Multiset.disjoint_left.1 hdisj h1 h2
    exact (hC.mul_right_eq_zero).1 (hzero x (Multiset.mem_of_le tsub_le_self hx))
end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra
