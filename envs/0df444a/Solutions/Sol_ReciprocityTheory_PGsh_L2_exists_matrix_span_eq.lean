-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.exists_matrix_span_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:31:23.34043+00:00
-- url     : https://prove2.me/submissions/60390404-7291-4cd4-8c69-ac93ed8e1878

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitDetOfSpanEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution (hv : v.Integers R) {X : Type} [Fintype X] [DecidableEq X]
    (M : Submodule R (X → C)) (hfg : M.FG)
    (hsp : Submodule.span C (M : Set (X → C)) = ⊤) :
    ∃ β : Matrix X X C, IsUnit β.det ∧ M = Submodule.span R (Set.range fun j x => β x j) := by
  classical
  obtain ⟨S, rfl⟩ := hfg
  rw [Submodule.span_span_of_tower] at hsp
  suffices key : ∀ (n : ℕ) (S : Finset (X → C)), S.card = n →
      Submodule.span C (↑S : Set (X → C)) = ⊤ →
      ∃ β : Matrix X X C, IsUnit β.det ∧
        Submodule.span R (↑S : Set (X → C)) = Submodule.span R (Set.range fun j x => β x j) from
    key _ S rfl hsp
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hn hspC
  by_cases hli : LinearIndependent C (fun i : S => (i : X → C))
  · have hb := Module.Basis.mk hli (by simpa using hspC.ge)
    let e : X ≃ S := (hb.indexEquiv (Pi.basisFun C X)).symm
    refine ⟨Matrix.of fun x j => ((e j : S) : X → C) x, ?_, ?_⟩
    · refine (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_cols_iff_isUnit.1 ?_)
      exact hli.comp e e.injective
    · congr 1
      ext f
      constructor
      · intro hf
        exact ⟨e.symm ⟨f, hf⟩, by ext x; simp⟩
      · rintro ⟨j, rfl⟩
        exact (e j).2
  · obtain ⟨g, hg, i1, hi1⟩ := Fintype.not_linearIndependent_iff.1 hli
    obtain ⟨i0, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => v (g i))
      ⟨i1, Finset.mem_univ _⟩
    have hg0 : g i0 ≠ 0 := by
      intro h0
      have h2 := hmax i1 (Finset.mem_univ _)
      rw [h0, map_zero] at h2
      exact hi1 ((Valuation.zero_iff v).1 (le_antisymm h2 zero_le))
    have key : (i0 : X → C) =
        ∑ i ∈ Finset.univ.erase i0, (-(g i * (g i0)⁻¹)) • (i : X → C) := by
      have h1 := Finset.add_sum_erase Finset.univ (fun i => g i • (i : X → C)) (Finset.mem_univ i0)
      rw [hg] at h1
      have h2 : g i0 • (i0 : X → C) = -∑ i ∈ Finset.univ.erase i0, g i • (i : X → C) :=
        eq_neg_of_add_eq_zero_left h1
      calc (i0 : X → C) = (g i0)⁻¹ • (g i0 • (i0 : X → C)) := by
            rw [smul_smul, inv_mul_cancel₀ hg0, one_smul]
        _ = _ := by
          rw [h2, smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_smul, neg_smul, mul_comm]
    have hle1 : ∀ i, v (-(g i * (g i0)⁻¹)) ≤ 1 := by
      intro i
      rw [Valuation.map_neg, map_mul, map_inv₀]
      calc v (g i) * (v (g i0))⁻¹ ≤ v (g i0) * (v (g i0))⁻¹ :=
            mul_le_mul_of_nonneg_right (hmax i (Finset.mem_univ _)) zero_le
        _ = 1 := mul_inv_cancel₀ ((Valuation.ne_zero_iff v).2 hg0)
    choose r hr using fun i => hv.exists_of_le_one (hle1 i)
    have hx0R : (i0 : X → C) ∈ Submodule.span R (↑(S.erase (i0 : X → C)) : Set (X → C)) := by
      have hsum : (∑ i ∈ Finset.univ.erase i0, (-(g i * (g i0)⁻¹)) • (i : X → C)) ∈
          Submodule.span R (↑(S.erase (i0 : X → C)) : Set (X → C)) := by
        refine Submodule.sum_mem _ fun i hi => ?_
        rw [← hr i, algebraMap_smul]
        refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
        exact Finset.mem_coe.2 (Finset.mem_erase.2
          ⟨fun h => (Finset.mem_erase.1 hi).1 (Subtype.ext h), i.2⟩)
      rw [← key] at hsum
      exact hsum
    have hx0C : (i0 : X → C) ∈ Submodule.span C (↑(S.erase (i0 : X → C)) : Set (X → C)) :=
      Submodule.span_le_restrictScalars R C _ hx0R
    have hS : (↑S : Set (X → C)) = insert (i0 : X → C) ↑(S.erase (i0 : X → C)) := by
      rw [← Finset.coe_insert, Finset.insert_erase i0.2]
    have hspR : Submodule.span R (↑S : Set (X → C)) =
        Submodule.span R (↑(S.erase (i0 : X → C)) : Set (X → C)) := by
      rw [hS, Submodule.span_insert_eq_span hx0R]
    have hspC' : Submodule.span C (↑(S.erase (i0 : X → C)) : Set (X → C)) = ⊤ := by
      rw [← hspC, hS, Submodule.span_insert_eq_span hx0C]
    obtain ⟨β, hβ, hβS⟩ := ih _ (by rw [← hn]; exact Finset.card_erase_lt_of_mem i0.2)
      (S.erase (i0 : X → C)) rfl hspC'
    exact ⟨β, hβ, hspR.trans hβS⟩
end ReciprocityTheory.PGsh.L2
