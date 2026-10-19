-- Prove2me | solution 1 for SoficGroups.KunResidualExpanderDecomposition.exists_expanding_residual_finpartition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/7e86ccf0-3287-41b8-b0ce-a53eda38072d

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunResidualExpanderDecomposition_boundary_inter_add_boundary_sdiff_le
import Theorems.Thm_SoficGroups_KunResidualExpanderDecomposition_exists_minimum_sparse_residual_cut
import Theorems.Thm_SoficGroups_KunResidualExpanderDecomposition_close_residual_inter_properties
import Theorems.Thm_SoficGroups_KunResidualExpanderDecomposition_minimum_sparse_cut_expands_close_residual_part

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunResidualExpanderDecomposition
open Filter Topology
open scoped BigOperators symmDiff
namespace SoficGroups.KunResidualExpanderDecomposition
theorem _root_.solution
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (B : Finset V) (γ α : ℝ)
    (hα : 0 ≤ α)
    (himprove : ∀ T : Finset V, T ⊆ Finset.univ \ B →
      (SoficGroups.boundary σ T : ℝ) < γ * (T.card : ℝ) →
      ∃ U : Finset V, 3 * (U ∆ T).card < T.card ∧
        (SoficGroups.boundary σ U : ℝ) ≤ α * (U.card : ℝ))
    (R : Finset V) (hRB : R ⊆ Finset.univ \ B) :
    ∃ P : Finpartition R,
      (∀ C ∈ P.parts, ∀ E : Finset V, E ⊆ C →
        2 * E.card ≤ C.card →
          γ * (E.card : ℝ) ≤ (SoficGroups.boundary σ E : ℝ)) ∧
      (∑ C ∈ P.parts, (SoficGroups.boundary σ C : ℝ)) ≤
        (SoficGroups.boundary σ R : ℝ) +
          4 * α * (R.card : ℝ) := by
  classical
  have hmain : ∀ R : Finset V, R ⊆ Finset.univ \ B →
      ∃ P : Finpartition R,
        (∀ C ∈ P.parts, ∀ E : Finset V, E ⊆ C →
          2 * E.card ≤ C.card →
            γ * (E.card : ℝ) ≤
              (SoficGroups.boundary σ E : ℝ)) ∧
        (∑ C ∈ P.parts, (SoficGroups.boundary σ C : ℝ)) ≤
          (SoficGroups.boundary σ R : ℝ) +
            4 * α * (R.card : ℝ) := by
    intro R
    refine Finset.strongInductionOn R ?_
    intro R ih hRgood
    by_cases hR : R.Nonempty
    · by_cases hsparse : ∃ T : Finset V, T ⊆ R ∧
          (SoficGroups.boundary σ T : ℝ) < γ * (T.card : ℝ)
      · obtain ⟨T, hTR, hTsparse, hTminimum⟩ :=
          exists_minimum_sparse_residual_cut σ R γ hsparse
        obtain ⟨U, hclose, hUboundary⟩ :=
          himprove T (hTR.trans hRgood) hTsparse
        have hpiece :=
          close_residual_inter_properties R T U hTR hclose
        let C : Finset V := R ∩ U
        have hCnonempty : C.Nonempty := by
          simpa only [C] using hpiece.1
        have hCR : C ⊆ R := Finset.inter_subset_left
        have hstrict : R \ C ⊂ R :=
          Finset.sdiff_ssubset hCR hCnonempty
        have hresgood : R \ C ⊆ Finset.univ \ B :=
          Finset.Subset.trans Finset.sdiff_subset hRgood
        obtain ⟨Q, hQexpand, hQbudget⟩ :=
          ih (R \ C) hstrict hresgood
        have hdisjoint : Disjoint (R \ C) C :=
          Finset.sdiff_disjoint
        have hunion : (R \ C) ⊔ C = R := by
          change (R \ C) ∪ C = R
          exact Finset.sdiff_union_of_subset hCR
        let P : Finpartition R :=
          Q.extend hCnonempty.ne_empty hdisjoint hunion
        have hCnot : C ∉ Q.parts := by
          intro hCQ
          have hsub := Q.subset hCQ
          obtain ⟨x, hx⟩ := hCnonempty
          exact (Finset.mem_sdiff.mp (hsub hx)).2 hx
        refine ⟨P, ?_, ?_⟩
        · intro D hD E hED hhalf
          have hparts : D = C ∨ D ∈ Q.parts := by
            simpa [P, Finpartition.extend] using hD
          rcases hparts with rfl | hDQ
          · exact minimum_sparse_cut_expands_close_residual_part
              σ R T U γ hTR hTminimum hclose E
              (by simpa only [C] using hED)
              (by simpa only [C] using hhalf)
          · exact hQexpand D hDQ E hED hhalf
        · have hUcard : (U.card : ℝ) ≤
              2 * (C.card : ℝ) := by
            exact_mod_cast hpiece.2.1
          have hUcost :
              2 * (SoficGroups.boundary σ U : ℝ) ≤
                4 * α * (C.card : ℝ) := by
            have hscale := mul_le_mul_of_nonneg_left hUcard hα
            nlinarith
          have hsplit :
              (SoficGroups.boundary σ C : ℝ) +
                  (SoficGroups.boundary σ (R \ C) : ℝ) ≤
                (SoficGroups.boundary σ R : ℝ) +
                  2 * (SoficGroups.boundary σ U : ℝ) := by
            have h := boundary_inter_add_boundary_sdiff_le σ R U
            have hres : R \ C = R \ U := by
              ext x
              simp [C]
            simpa only [C, hres, Nat.cast_add, Nat.cast_mul,
              Nat.cast_ofNat] using
              (show
                ((SoficGroups.boundary σ (R ∩ U) +
                  SoficGroups.boundary σ (R \ U) : ℕ) : ℝ) ≤
                ((SoficGroups.boundary σ R +
                  2 * SoficGroups.boundary σ U : ℕ) : ℝ)
                from by exact_mod_cast h)
          have hcard :
              ((R \ C).card : ℝ) + (C.card : ℝ) =
                (R.card : ℝ) := by
            exact_mod_cast Finset.card_sdiff_add_card_eq_card hCR
          calc
            (∑ D ∈ P.parts, (SoficGroups.boundary σ D : ℝ)) =
                (SoficGroups.boundary σ C : ℝ) +
                  ∑ D ∈ Q.parts,
                    (SoficGroups.boundary σ D : ℝ) := by
                  simp [P, Finpartition.extend, hCnot]
            _ ≤ (SoficGroups.boundary σ C : ℝ) +
                  ((SoficGroups.boundary σ (R \ C) : ℝ) +
                    4 * α * ((R \ C).card : ℝ)) :=
                    add_le_add (le_refl _) hQbudget
            _ ≤ (SoficGroups.boundary σ R : ℝ) +
                  2 * (SoficGroups.boundary σ U : ℝ) +
                    4 * α * ((R \ C).card : ℝ) := by
                  linarith
            _ ≤ (SoficGroups.boundary σ R : ℝ) +
                  4 * α * (C.card : ℝ) +
                    4 * α * ((R \ C).card : ℝ) := by
                  linarith
            _ = (SoficGroups.boundary σ R : ℝ) +
                  4 * α * (R.card : ℝ) := by
                  nlinarith [hcard]
      · refine ⟨Finpartition.indiscrete hR.ne_empty, ?_, ?_⟩
        · intro C hC E hEC _
          have hCR : C = R := by
            simpa [Finpartition.indiscrete] using hC
          subst C
          by_contra h
          apply hsparse
          exact ⟨E, hEC, lt_of_not_ge h⟩
        · simp only [Finpartition.indiscrete, Finset.sum_singleton]
          have hnonneg : 0 ≤ 4 * α * (R.card : ℝ) := by
            positivity
          linarith
    · have hzero : R = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hR
      subst R
      refine ⟨Finpartition.empty (Finset V), ?_, ?_⟩
      · simp
      · simp [SoficGroups.boundary]
  exact hmain R hRB
end SoficGroups.KunResidualExpanderDecomposition
