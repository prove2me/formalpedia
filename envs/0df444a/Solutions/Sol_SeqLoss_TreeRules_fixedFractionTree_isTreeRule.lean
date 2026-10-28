-- Prove2me | solution 1 for SeqLoss.TreeRules.fixedFractionTree_isTreeRule
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T02:44:11.434001+00:00
-- url     : https://prove2.me/submissions/2643cc9d-b53d-49ad-a40d-00dbf99b14cd

import Definitions.Def_SeqLoss_TreeRules_Setting
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option autoImplicit false
open scoped BigOperators
open SeqLoss.TreeRules

private lemma root_data (T : Finset (ℕ × ℕ)) (hT : IsTree T) :
    ∃ r ∈ N T, ∀ i ∈ N T, (∀ e ∈ T, e.2 ≠ i) ↔ i = r := by
  rcases hT with ⟨r, hr, hno, hparent, hreach⟩
  have hrN : r ∈ N T := by
    rcases Finset.mem_union.mp hr with h | h
    · exact h
    · rcases Finset.mem_image.mp h with ⟨e, he, heq⟩
      exact False.elim (hno e he heq)
  refine ⟨r, hrN, ?_⟩
  intro i hi
  constructor
  · intro hn
    by_contra hir
    have hiV : i ∈ V T := Finset.mem_union_left _ hi
    obtain ⟨u, hu, _⟩ := hparent i hiV hir
    exact hn (u,i) hu rfl
  · rintro rfl
    exact hno

private lemma fraction_scale (lam : ℝ) (T : Finset (ℕ × ℕ))
    (ℓ : ℕ × ℕ → ℝ) (a : ℝ) (i : ℕ) :
    fixedFractionTree lam T (a • ℓ) i = a * fixedFractionTree lam T ℓ i := by
  simp only [fixedFractionTree, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  split_ifs <;> ring

theorem solution (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    IsTreeRule (fixedFractionTree lam) := by
  intro T hT ℓ hℓ
  classical
  obtain ⟨r, hr, hroot⟩ := root_data T hT
  have htotal : 0 ≤ ∑ e ∈ T, ℓ e := Finset.sum_nonneg fun e _ => hℓ e
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    unfold fixedFractionTree
    apply add_nonneg (mul_nonneg hlam.1 (Finset.sum_nonneg fun e _ => hℓ e))
    split_ifs
    · exact mul_nonneg (sub_nonneg.mpr hlam.2) htotal
    · exact le_rfl
  · have hgroup : ∑ i ∈ N T, ∑ e ∈ T.filter (fun e => e.1 = i), ℓ e =
        ∑ e ∈ T, ℓ e := by
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e he
      have hem : e.1 ∈ N T := Finset.mem_image.mpr ⟨e,he,rfl⟩
      simp [hem]
    simp only [fixedFractionTree, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hbonus : ∑ i ∈ N T, (if ∀ e ∈ T, e.2 ≠ i then
        (1-lam) * ∑ e ∈ T, ℓ e else 0) = (1-lam) * ∑ e ∈ T, ℓ e := by
      calc
        _ = ∑ i ∈ N T, (if i = r then (1-lam) * ∑ e ∈ T, ℓ e else 0) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [hroot i hi]
        _ = _ := by simp [hr]
    rw [hgroup, hbonus]
    ring
  · intro π ℓ' hℓ' heq i hi
    have hsum : ∑ e ∈ relabel π T, ℓ' e = ∑ e ∈ T, ℓ e := by
      simp only [relabel, Finset.sum_map, Equiv.toEmbedding_apply,
        Equiv.prodCongr_apply]
      exact Finset.sum_congr rfl heq
    have hlocal : ∑ e ∈ (relabel π T).filter (fun e => e.1 = π i), ℓ' e =
        ∑ e ∈ T.filter (fun e => e.1 = i), ℓ e := by
      simp only [Finset.sum_filter, relabel, Finset.sum_map,
        Equiv.toEmbedding_apply, Equiv.prodCongr_apply]
      apply Finset.sum_congr rfl
      intro e he
      change (if π e.1 = π i then ℓ' (π e.1, π e.2) else 0) =
        (if e.1 = i then ℓ e else 0)
      simp only [Equiv.apply_eq_iff_eq, heq e he]
    have hno : (∀ e ∈ relabel π T, e.2 ≠ π i) ↔ ∀ e ∈ T, e.2 ≠ i := by
      constructor
      · intro h e he heq
        apply h (π e.1, π e.2)
        · exact Finset.mem_map.mpr ⟨e, he, rfl⟩
        · exact congrArg π heq
      · intro h e he heq
        rcases Finset.mem_map.mp he with ⟨f, hf, rfl⟩
        exact h f hf (π.injective heq)
    simp only [fixedFractionTree, hlocal, hsum, hno]
  · intro i hi
    simp_rw [fraction_scale]
    simpa only [id_eq, one_mul] using
      (continuous_id.mul_const (fixedFractionTree lam T ℓ i)).tendsto (1 : ℝ)

#print axioms solution

