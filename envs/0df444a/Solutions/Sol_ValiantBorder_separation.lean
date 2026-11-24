-- Prove2me | solution 1 for ValiantBorder.separation
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-24T00:07:51.834887+00:00
-- url     : https://prove2.me/submissions/6d4c806e-674f-4815-bc30-5cb475eaae1f

import Theorems.Thm_ValiantBorder_allFields
import Theorems.Thm_ValiantBorder_exactIsApprox

/-! Independent proof of the elementary containment in Anthropic's statement of
*VP ≠ VNP over every field*. The imported circuit and family definitions are
those of `vp-vnp/Statement.lean` (Apache-2.0). -/

open MvPolynomial

universe u

private theorem rename_circuit {F : Type u} [Field F] {V W : Type} (r : V → W)
    {f : MvPolynomial V F} {s : ℕ} (h : Statement.Computes f s) :
    Statement.Computes (rename r f) s := by
  obtain ⟨gates, valid, k, hk, output⟩ := h
  refine ⟨fun j => rename r (gates j), ?_, k, hk, congrArg (rename r) output⟩
  intro j hj
  rcases valid j hj with ⟨v, hv⟩ | ⟨a, ha⟩ | ⟨i, hi, t, ht, hsum⟩ | ⟨i, hi, t, ht, hprod⟩
  · exact Or.inl ⟨r v, by simp [hv]⟩
  · exact Or.inr (Or.inl ⟨a, by simp [ha]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨i, hi, t, ht, by simp [hsum]⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨i, hi, t, ht, by simp [hprod]⟩))

/-- A VNP representation with no witness bits suffices for each VP family. -/
private theorem vp_subset_vnp (F : Type u) [Field F] : Statement.VP F ⊆ Statement.VNP F := by
  classical
  intro f hf
  obtain ⟨a, bounds⟩ := hf
  refine ⟨fun _ => 0, fun n => rename Sum.inl (f.poly n), ⟨a, ?_⟩, ?_⟩
  · intro n
    obtain ⟨hvars, hdeg, hcircuit⟩ := bounds n
    exact ⟨by simpa using hvars,
      le_trans (totalDegree_rename_le Sum.inl (f.poly n)) hdeg,
      rename_circuit Sum.inl hcircuit⟩
  · intro n
    rw [Fintype.sum_unique, aeval_rename]
    exact (aeval_X_left_apply (f.poly n)).symm

/-- Corollary 1.2 from Theorem 1.4 of Claude (Anthropic), *VP ≠ VNP over every field*. -/
theorem solution : Statement.Separation.{u} := by
  intro F _
  refine ⟨vp_subset_vnp F, fun reverse => ValiantBorder.allFields.{u}.2 F ?_⟩
  intro f hf
  obtain ⟨a, bound⟩ := reverse hf
  refine ⟨a, fun n => ?_⟩
  obtain ⟨hvars, hdeg, hcircuit⟩ := bound n
  exact ⟨hvars, hdeg, ValiantBorder.exactIsApprox _ _ hcircuit⟩
