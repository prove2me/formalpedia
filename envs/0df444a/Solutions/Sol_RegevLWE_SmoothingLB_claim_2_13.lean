-- Prove2me | solution 1 for RegevLWE.SmoothingLB.claim_2_13
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T00:11:09.756333+00:00
-- url     : https://prove2.me/submissions/5e712edc-b2e3-49e1-b261-08bae64c1c53

import Mathlib
import Definitions.Def_RegevLWE_SmoothingLB_Lattice
import Theorems.Thm_RegevLWE_SmoothingLB_smoothing_remark
import Theorems.Thm_RegevLWE_SmoothingLB_proof_display
import Theorems.Thm_RegevLWE_SmoothingLB_lemma_2_3

open Filter Topology RegevLWE.SmoothingLB RegevLWE.GaussConv

namespace RegevLWE.SmoothingLB

private lemma inner_nondegenerate (n : ℕ) :
    (innerₗ (EuclideanSpace ℝ (Fin n))).Nondegenerate :=
  ⟨fun x hx => inner_self_eq_zero.mp (hx x), fun x hx => inner_self_eq_zero.mp (hx x)⟩

private lemma dual_eq_span {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℝ (EuclideanSpace ℝ (Fin n))),
      dual L = Submodule.span ℤ (Set.range b) := by
  classical
  have : Module.Free ℤ L := ZLattice.module_free ℝ L
  have : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  let b₀ := Module.Free.chooseBasis ℤ ↥L
  let b := b₀.ofZLatticeBasis ℝ L
  have hspan : Submodule.span ℤ (Set.range b) = L := b₀.ofZLatticeBasis_span ℝ
  refine ⟨Module.Free.ChooseBasisIndex ℤ ↥L, inferInstance,
    LinearMap.BilinForm.dualBasis (innerₗ (EuclideanSpace ℝ (Fin n))) (inner_nondegenerate n) b, ?_⟩
  change LinearMap.BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin n))) L = _
  conv_lhs => rw [← hspan]
  exact LinearMap.BilinForm.dualSubmodule_span_of_basis
    (innerₗ (EuclideanSpace ℝ (Fin n))) (inner_nondegenerate n) b

private instance instDiscreteTopologyDual {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    DiscreteTopology (dual L) := by
  obtain ⟨ι, _, b, h⟩ := dual_eq_span L
  rw [h]
  infer_instance

private instance instIsZLatticeDual {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    IsZLattice ℝ (dual L) := by
  obtain ⟨ι, _, b, h⟩ := dual_eq_span L
  exact ⟨by rw [h]; exact ZSpan.span_top b⟩

private lemma dualBasis_dualBasis_eq {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (EuclideanSpace ℝ (Fin n))) :
    LinearMap.BilinForm.dualBasis (innerₗ (EuclideanSpace ℝ (Fin n))) (inner_nondegenerate n)
      (LinearMap.BilinForm.dualBasis (innerₗ (EuclideanSpace ℝ (Fin n))) (inner_nondegenerate n) b) = b := by
  let B : LinearMap.BilinForm ℝ (EuclideanSpace ℝ (Fin n)) := innerₗ (EuclideanSpace ℝ (Fin n))
  let hB := inner_nondegenerate n
  let b' := LinearMap.BilinForm.dualBasis B hB b
  let b'' := LinearMap.BilinForm.dualBasis B hB b'
  ext i : 1
  change b'' i = b i
  rw [← sub_eq_zero]
  apply hB.1 (b'' i - b i)
  intro w
  have hw : ∀ j, (B (b'' i - b i)) (b' j) = 0 := by
    intro j
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero]
    have h1 : B (b'' i) (b' j) = if j = i then 1 else 0 :=
      LinearMap.BilinForm.apply_dualBasis_left hB b' i j
    have h2 : B (b i) (b' j) = if j = i then 1 else 0 := by
      change inner ℝ (b i) (b' j) = _
      rw [real_inner_comm]
      change B (b' j) (b i) = _
      rw [LinearMap.BilinForm.apply_dualBasis_left hB b j i]
      by_cases h : i = j <;> simp [h, eq_comm]
    rw [h1, h2]
  rw [← b'.sum_repr w, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_smul, hw j, smul_zero]

private lemma dual_dual_eq {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    dual (dual L) = L := by
  classical
  have : Module.Free ℤ L := ZLattice.module_free ℝ L
  have : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  let b₀ := Module.Free.chooseBasis ℤ ↥L
  let b := b₀.ofZLatticeBasis ℝ L
  have hspan : Submodule.span ℤ (Set.range b) = L := b₀.ofZLatticeBasis_span ℝ
  let B : LinearMap.BilinForm ℝ (EuclideanSpace ℝ (Fin n)) := innerₗ (EuclideanSpace ℝ (Fin n))
  let hB := inner_nondegenerate n
  have h1 : dual L = Submodule.span ℤ (Set.range (LinearMap.BilinForm.dualBasis B hB b)) := by
    change LinearMap.BilinForm.dualSubmodule B L = _
    conv_lhs => rw [← hspan]
    exact LinearMap.BilinForm.dualSubmodule_span_of_basis B hB b
  have h2 : dual (dual L) =
      Submodule.span ℤ (Set.range (LinearMap.BilinForm.dualBasis B hB (LinearMap.BilinForm.dualBasis B hB b))) := by
    change LinearMap.BilinForm.dualSubmodule B (dual L) = _
    rw [h1]
    exact LinearMap.BilinForm.dualSubmodule_span_of_basis B hB (LinearMap.BilinForm.dualBasis B hB b)
  rw [h2, dualBasis_dualBasis_eq b, hspan]

theorem claim_2_13 {n : ℕ} (hn : 0 < n) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] (ε : ℝ) (hε : 0 < ε) :
    Real.sqrt (Real.log (1 / ε) / Real.pi) * (1 / lambda1 (RegevLWE.GaussConv.dual L)) ≤ RegevLWE.GaussConv.smoothingParam L ε ∧
    Real.sqrt (Real.log (1 / ε) / Real.pi) * (lambdaN L / n) ≤
      Real.sqrt (Real.log (1 / ε) / Real.pi) * (1 / lambda1 (RegevLWE.GaussConv.dual L)) := by
  obtain ⟨v, hv_mem, hv_ne, hv_norm, hε_eq, hrho_le, hrho_eq⟩ := proof_display hn L ε hε
  have hs_pos : 0 < smoothingParam L ε := ((smoothing_remark hn L).2.2.2.2 ε hε).1
  have hl1_pos : 0 < lambda1 (dual L) := by
    rw [← hv_norm]
    exact norm_pos_iff.mpr hv_ne
  have hexp_le : Real.exp (-Real.pi * (smoothingParam L ε * lambda1 (dual L)) ^ 2) ≤ ε := by
    linarith
  have h_first :
      Real.sqrt (Real.log (1 / ε) / Real.pi) * (1 / lambda1 (dual L)) ≤ smoothingParam L ε := by
    by_cases hε1 : 1 ≤ ε
    · have hdiv_le : 1 / ε ≤ 1 := div_le_one_of_le₀ hε1 hε.le
      have hlog_le : Real.log (1 / ε) ≤ 0 := Real.log_nonpos (by positivity) hdiv_le
      have harg_le : Real.log (1 / ε) / Real.pi ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hlog_le Real.pi_pos.le
      rw [Real.sqrt_eq_zero_of_nonpos harg_le, zero_mul]
      exact hs_pos.le
    · have hlog := Real.log_le_log (Real.exp_pos _) hexp_le
      rw [Real.log_exp] at hlog
      have hlog_inv : Real.log (1 / ε) = -Real.log ε := by
        rw [one_div, Real.log_inv]
      have h_ineq1 : Real.log (1 / ε) ≤ Real.pi * (smoothingParam L ε * lambda1 (dual L)) ^ 2 := by
        linarith
      have h_ineq2 : Real.log (1 / ε) / Real.pi ≤ (smoothingParam L ε * lambda1 (dual L)) ^ 2 := by
        rw [div_le_iff₀ Real.pi_pos]
        linarith
      have h_sqrt : Real.sqrt (Real.log (1 / ε) / Real.pi) ≤ smoothingParam L ε * lambda1 (dual L) := by
        calc Real.sqrt (Real.log (1 / ε) / Real.pi)
            ≤ Real.sqrt ((smoothingParam L ε * lambda1 (dual L)) ^ 2) := Real.sqrt_le_sqrt h_ineq2
          _ = smoothingParam L ε * lambda1 (dual L) :=
            Real.sqrt_sq (mul_pos hs_pos hl1_pos).le
      rw [mul_one_div, div_le_iff₀ hl1_pos]
      exact h_sqrt
  refine ⟨h_first, ?_⟩
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  have h_ban := (lemma_2_3 hn (dual L)).2
  rw [dual_dual_eq L] at h_ban
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [div_le_iff₀ hn_pos, one_div, inv_mul_eq_div, le_div_iff₀ hl1_pos]
  linarith

end RegevLWE.SmoothingLB

open RegevLWE.SmoothingLB

theorem solution {n : ℕ} (hn : 0 < n) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] (ε : ℝ) (hε : 0 < ε) :
    Real.sqrt (Real.log (1 / ε) / Real.pi) * (1 / lambda1 (RegevLWE.GaussConv.dual L)) ≤ RegevLWE.GaussConv.smoothingParam L ε ∧
    Real.sqrt (Real.log (1 / ε) / Real.pi) * (lambdaN L / n) ≤
      Real.sqrt (Real.log (1 / ε) / Real.pi) * (1 / lambda1 (RegevLWE.GaussConv.dual L)) :=
  RegevLWE.SmoothingLB.claim_2_13 hn L ε hε
