-- Prove2me | solution 1 for RegevLWE.SmoothingLB.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T00:30:34.210993+00:00
-- url     : https://prove2.me/submissions/e0d11383-e62c-4f00-8820-91fbd8525815

import Definitions.Def_RegevLWE_SmoothingLB_Lattice
import Definitions.Def_RegevLWE_Hyperplane_DiscreteGaussian
import Theorems.Thm_RegevLWE_Hyperplane_rhoLattice_poisson
import Theorems.Thm_RegevLWE_Hyperplane_expectation_chain

open Filter Topology RegevLWE.SmoothingLB RegevLWE.GaussConv RegevLWE.Hyperplane

set_option linter.unusedVariables false

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

private lemma nonempty_nonzero_lattice {n : ℕ} (hn : 0 < n)
    (M : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology M] [IsZLattice ℝ M] :
    Nonempty {y : M // y ≠ 0} := by
  have hrank : 0 < Module.finrank ℤ M := by
    rw [ZLattice.rank ℝ M, finrank_euclideanSpace_fin]
    exact hn
  have : Nontrivial M := Module.finrank_pos_iff.mp hrank
  obtain ⟨y, hy⟩ := exists_ne (0 : M)
  exact ⟨⟨y, hy⟩⟩

private lemma exists_norm_eq_lambda1 {n : ℕ} (hn : 0 < n)
    (M : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology M] [IsZLattice ℝ M] :
    ∃ v ∈ M, v ≠ 0 ∧ ‖v‖ = lambda1 M := by
  obtain ⟨⟨y₀, hy₀⟩⟩ := nonempty_nonzero_lattice hn M
  let v₀ : EuclideanSpace ℝ (Fin n) := y₀
  have hv₀_mem : v₀ ∈ M := y₀.2
  have hv₀_ne : v₀ ≠ 0 := Submodule.coe_eq_zero.not.mpr hy₀
  let S₀ : Set (EuclideanSpace ℝ (Fin n)) := {v | v ∈ M ∧ v ≠ 0 ∧ ‖v‖ ≤ ‖v₀‖}
  have hS₀_ne : S₀.Nonempty := ⟨v₀, hv₀_mem, hv₀_ne, le_rfl⟩
  have hS₀_fin : S₀.Finite := by
    have : DiscreteTopology M.toAddSubgroup := (inferInstance : DiscreteTopology M)
    have hball : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ‖v₀‖ ∩
        (M.toAddSubgroup : Set (EuclideanSpace ℝ (Fin n)))).Finite :=
      Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
        Metric.isBounded_closedBall inferInstance
    refine hball.subset (fun v hv => ?_)
    exact ⟨Metric.mem_closedBall.mpr (by simpa using hv.2.2), hv.1⟩
  let R₀ : Set ℝ := (fun v => ‖v‖) '' S₀
  have hR₀_ne : R₀.Nonempty := hS₀_ne.image _
  have hR₀_fin : R₀.Finite := hS₀_fin.image _
  obtain ⟨r₀, hr₀_least⟩ := hR₀_fin.isCompact.exists_isLeast hR₀_ne
  obtain ⟨v, hv_S₀, hv_norm⟩ := hr₀_least.1
  dsimp at hv_norm
  refine ⟨v, hv_S₀.1, hv_S₀.2.1, ?_⟩
  rw [hv_norm]
  unfold lambda1
  have h_least : IsLeast {r : ℝ | ∃ w ∈ M, w ≠ 0 ∧ ‖w‖ = r} r₀ := by
    refine ⟨⟨v, hv_S₀.1, hv_S₀.2.1, hv_norm⟩, ?_⟩
    rintro r ⟨w, hw_mem, hw_ne, rfl⟩
    by_cases hw : ‖w‖ ≤ ‖v₀‖
    · exact hr₀_least.2 ⟨w, ⟨hw_mem, hw_ne, hw⟩, rfl⟩
    · have hr₀_le_v₀ : r₀ ≤ ‖v₀‖ := hr₀_least.2 ⟨v₀, ⟨hv₀_mem, hv₀_ne, le_rfl⟩, rfl⟩
      linarith
  exact h_least.csInf_eq.symm

private lemma norm_ge_lambda1 {n : ℕ} (M : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    {v : EuclideanSpace ℝ (Fin n)} (hv_mem : v ∈ M) (hv_ne : v ≠ 0) :
    lambda1 M ≤ ‖v‖ := by
  unfold lambda1
  exact csInf_le ⟨0, fun r ⟨w, _, _, hr⟩ => hr ▸ norm_nonneg w⟩ ⟨v, hv_mem, hv_ne, rfl⟩

private lemma lambdaN_set_nonempty {n : ℕ} (M : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology M] [IsZLattice ℝ M] :
    {r : ℝ | ∃ v : Fin n → EuclideanSpace ℝ (Fin n),
      LinearIndependent ℝ v ∧ ∀ i, v i ∈ M ∧ ‖v i‖ ≤ r}.Nonempty := by
  classical
  have : Module.Free ℤ M := ZLattice.module_free ℝ M
  have : Module.Finite ℤ M := ZLattice.module_finite ℝ M
  let b₀ := Module.Free.chooseBasis ℤ ↥M
  let b := b₀.ofZLatticeBasis ℝ M
  have hspan : Submodule.span ℤ (Set.range b) = M := b₀.ofZLatticeBasis_span ℝ
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ ↥M) = n := by
    rw [← Module.finrank_eq_card_basis b, finrank_euclideanSpace_fin]
  let e : Fin n ≃ Module.Free.ChooseBasisIndex ℤ ↥M := (Fintype.equivFinOfCardEq hcard).symm
  let v : Fin n → EuclideanSpace ℝ (Fin n) := fun i => b (e i)
  have hv_li : LinearIndependent ℝ v := b.linearIndependent.comp e e.injective
  refine ⟨∑ i : Fin n, ‖v i‖, v, hv_li, fun i => ⟨?_, ?_⟩⟩
  · exact hspan ▸ Submodule.subset_span ⟨e i, rfl⟩
  · exact Finset.single_le_sum (fun j _ => norm_nonneg (v j)) (Finset.mem_univ i)

private lemma lambdaN_set_bddBelow {n : ℕ} (hn : 0 < n)
    (M : Submodule ℤ (EuclideanSpace ℝ (Fin n))) :
    BddBelow {r : ℝ | ∃ v : Fin n → EuclideanSpace ℝ (Fin n),
      LinearIndependent ℝ v ∧ ∀ i, v i ∈ M ∧ ‖v i‖ ≤ r} :=
  ⟨0, fun _r ⟨v, _, hv⟩ => (norm_nonneg (v ⟨0, hn⟩)).trans (hv ⟨0, hn⟩).2⟩

private lemma exists_inner_ne_zero_of_linearIndependent {n : ℕ}
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ≠ 0)
    {w : Fin n → EuclideanSpace ℝ (Fin n)} (hw : LinearIndependent ℝ w) :
    ∃ i : Fin n, inner ℝ v (w i) ≠ 0 := by
  by_contra h_all
  push Not at h_all
  have h_finrank : Module.finrank ℝ (Submodule.span ℝ (Set.range w)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [finrank_span_eq_card hw, Fintype.card_fin, finrank_euclideanSpace_fin]
  have h_top : Submodule.span ℝ (Set.range w) = ⊤ :=
    Submodule.eq_top_of_finrank_eq h_finrank
  let φ : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ := innerₗ (EuclideanSpace ℝ (Fin n)) v
  have h_le_ker : Submodule.span ℝ (Set.range w) ≤ LinearMap.ker φ := by
    rw [Submodule.span_le]
    rintro y ⟨i, rfl⟩
    exact h_all i
  rw [h_top] at h_le_ker
  have hv_ker : v ∈ LinearMap.ker φ := h_le_ker Submodule.mem_top
  exact hv (inner_self_eq_zero.mp hv_ker)

private lemma lower_bound_lemma_2_3 {n : ℕ} (hn : 0 < n)
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L] [IsZLattice ℝ L] :
    1 ≤ lambda1 L * lambdaN (dual L) := by
  obtain ⟨v, hv_mem, hv_ne, hv_norm⟩ := exists_norm_eq_lambda1 hn L
  have hl1_pos : 0 < lambda1 L := by
    rw [← hv_norm]
    exact norm_pos_iff.mpr hv_ne
  have h_le_csInf : (lambda1 L)⁻¹ ≤ lambdaN (dual L) := by
    unfold lambdaN
    refine le_csInf (lambdaN_set_nonempty (dual L)) ?_
    rintro r ⟨w, hw_li, hw⟩
    obtain ⟨i, hi_ne⟩ := exists_inner_ne_zero_of_linearIndependent hv_ne hw_li
    have h_mem_dual : w i ∈ LinearMap.BilinForm.dualSubmodule
        (innerₗ (EuclideanSpace ℝ (Fin n))) L := (hw i).1
    have h_in_one := (LinearMap.BilinForm.mem_dualSubmodule
      (innerₗ (EuclideanSpace ℝ (Fin n)))).mp h_mem_dual v hv_mem
    rw [Submodule.one_eq_span, Submodule.mem_span_singleton] at h_in_one
    obtain ⟨k, hk⟩ := h_in_one
    have hk_eq : (k : ℝ) = inner ℝ v (w i) := by
      rw [real_inner_comm]
      simpa using hk
    have hk_ne : k ≠ 0 := by
      intro hk0
      apply hi_ne
      rw [← hk_eq, hk0, Int.cast_zero]
    have hk_abs : (1 : ℝ) ≤ |inner ℝ v (w i)| := by
      have h1 : (1 : ℤ) ≤ |k| := Int.one_le_abs hk_ne
      have h2 : ((1 : ℤ) : ℝ) ≤ ((|k| : ℤ) : ℝ) := Int.cast_le.mpr h1
      rwa [Int.cast_one, Int.cast_abs, hk_eq] at h2
    have h_cs := abs_real_inner_le_norm v (w i)
    have h_mul : 1 ≤ r * lambda1 L := by
      calc (1 : ℝ)
          ≤ |inner ℝ v (w i)| := hk_abs
        _ ≤ ‖v‖ * ‖w i‖ := h_cs
        _ = lambda1 L * ‖w i‖ := by rw [hv_norm]
        _ ≤ lambda1 L * r := mul_le_mul_of_nonneg_left (hw i).2 hl1_pos.le
        _ = r * lambda1 L := mul_comm _ _
    rwa [inv_le_iff_one_le_mul₀ hl1_pos]
  rw [inv_le_iff_one_le_mul₀ hl1_pos] at h_le_csInf
  linarith

private lemma upper_bound_dim_one (L : Submodule ℤ (EuclideanSpace ℝ (Fin 1)))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    lambda1 L * lambdaN (dual L) ≤ (1 : ℕ) := by
  classical
  have : Module.Free ℤ L := ZLattice.module_free ℝ L
  have : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  let b₀ := Module.Free.chooseBasis ℤ ↥L
  let b := b₀.ofZLatticeBasis ℝ L
  have hspan : Submodule.span ℤ (Set.range b) = L := b₀.ofZLatticeBasis_span ℝ
  let B : LinearMap.BilinForm ℝ (EuclideanSpace ℝ (Fin 1)) := innerₗ (EuclideanSpace ℝ (Fin 1))
  let hB := inner_nondegenerate 1
  let b' := LinearMap.BilinForm.dualBasis B hB b
  have hdual : dual L = Submodule.span ℤ (Set.range b') := by
    change LinearMap.BilinForm.dualSubmodule B L = _
    conv_lhs => rw [← hspan]
    exact LinearMap.BilinForm.dualSubmodule_span_of_basis B hB b
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ ↥L) = 1 := by
    rw [← Module.finrank_eq_card_basis b, finrank_euclideanSpace_fin]
  let e : Fin 1 ≃ Module.Free.ChooseBasisIndex ℤ ↥L := (Fintype.equivFinOfCardEq hcard).symm
  let i₀ := e 0
  have hb_mem : b i₀ ∈ L := by
    have h_in : b i₀ ∈ Submodule.span ℤ (Set.range b) := Submodule.subset_span ⟨i₀, rfl⟩
    rwa [hspan] at h_in
  have hb_ne : b i₀ ≠ 0 := b.ne_zero i₀
  have hl1_le : lambda1 L ≤ ‖b i₀‖ := norm_ge_lambda1 L hb_mem hb_ne
  let w : Fin 1 → EuclideanSpace ℝ (Fin 1) := fun j => b' (e j)
  have hw_li : LinearIndependent ℝ w := b'.linearIndependent.comp e e.injective
  have hlN_le : lambdaN (dual L) ≤ ‖b' i₀‖ := by
    unfold lambdaN
    refine csInf_le (lambdaN_set_bddBelow (by decide) (dual L)) ⟨w, hw_li, fun j => ⟨?_, ?_⟩⟩
    · have h_in : w j ∈ Submodule.span ℤ (Set.range b') := Submodule.subset_span ⟨e j, rfl⟩
      rwa [← hdual] at h_in
    · have hj : j = 0 := Subsingleton.elim j 0
      subst hj
      exact le_rfl
  have h_inner : inner ℝ (b' i₀) (b i₀) = 1 := by
    change B (b' i₀) (b i₀) = 1
    rw [LinearMap.BilinForm.apply_dualBasis_left hB b i₀ i₀, if_pos rfl]
  have h_norm_b : ‖b i₀‖ ^ 2 = ((b i₀).ofLp 0) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs]
  have h_norm_b' : ‖b' i₀‖ ^ 2 = ((b' i₀).ofLp 0) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs]
  have h_in_eq : inner ℝ (b' i₀) (b i₀) = (b i₀).ofLp 0 * (b' i₀).ofLp 0 := by
    rw [PiLp.inner_apply, Fin.sum_univ_one]
    simp
  have h_prod_sq : (‖b i₀‖ * ‖b' i₀‖) ^ 2 = 1 := by
    calc (‖b i₀‖ * ‖b' i₀‖) ^ 2
        = ‖b i₀‖ ^ 2 * ‖b' i₀‖ ^ 2 := by ring
      _ = ((b i₀).ofLp 0) ^ 2 * ((b' i₀).ofLp 0) ^ 2 := by rw [h_norm_b, h_norm_b']
      _ = ((b i₀).ofLp 0 * (b' i₀).ofLp 0) ^ 2 := by ring
      _ = (inner ℝ (b' i₀) (b i₀)) ^ 2 := by rw [← h_in_eq]
      _ = 1 := by rw [h_inner, one_pow]
  have h_prod_le : ‖b i₀‖ * ‖b' i₀‖ ≤ 1 := by nlinarith
  obtain ⟨v, hv_mem, hv_ne, hv_norm⟩ := exists_norm_eq_lambda1 (by decide) L
  have hl1_nonneg : 0 ≤ lambda1 L := by rw [← hv_norm]; exact norm_nonneg v
  have hlN_nonneg : 0 ≤ lambdaN (dual L) := by
    have h_low := lower_bound_lemma_2_3 (by decide) L
    have hl1_pos : 0 < lambda1 L := by rw [← hv_norm]; exact norm_pos_iff.mpr hv_ne
    nlinarith
  have h_le : lambda1 L * lambdaN (dual L) ≤ ‖b i₀‖ * ‖b' i₀‖ :=
    mul_le_mul hl1_le hlN_le hlN_nonneg (norm_nonneg _)
  push_cast
  linarith

private lemma summable_rho_lattice {n : ℕ} (M : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology M] [IsZLattice ℝ M] {r : ℝ} (hr : 0 < r) :
    Summable (fun x : M => rho r (x : EuclideanSpace ℝ (Fin n))) ∧ 0 < rhoLattice r M := by
  have h_poiss := (rhoLattice_poisson M hr).2
  have h_cov_pos : 0 < ZLattice.covolume M := ZLattice.covolume_pos M MeasureTheory.volume
  have h_pos : 0 < rhoLattice r M :=
    lt_of_lt_of_le (mul_pos (inv_pos.mpr h_cov_pos) (pow_pos hr n)) h_poiss
  refine ⟨?_, h_pos⟩
  by_contra h_not
  have h_zero : rhoLattice r M = 0 := tsum_eq_zero_of_not_summable h_not
  linarith

private lemma rhoLattice_two_mul_le {n : ℕ} (M : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology M] [IsZLattice ℝ M] {r : ℝ} (hr : 0 < r) :
    rhoLattice (2 * r) M ≤ 2 ^ n * rhoLattice r M := by
  have hr2 : 0 < 2 * r := by positivity
  have h1 := (rhoLattice_poisson M hr).1
  have h2 := (rhoLattice_poisson M hr2).1
  have h_sum1 : Summable (fun y : dual M => rho (1 / r) (y : EuclideanSpace ℝ (Fin n))) :=
    (summable_rho_lattice (dual M) (one_div_pos.mpr hr)).1
  have h_sum2 : Summable (fun y : dual M => rho (1 / (2 * r)) (y : EuclideanSpace ℝ (Fin n))) :=
    (summable_rho_lattice (dual M) (one_div_pos.mpr hr2)).1
  have h_dual_le : rhoDual (1 / (2 * r)) M ≤ rhoDual (1 / r) M := by
    unfold rhoDual
    refine h_sum2.tsum_le_tsum (fun y => ?_) h_sum1
    unfold rho
    apply Real.exp_le_exp.mpr
    have h_eq1 : -Real.pi * ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2 / (1 / (2 * r)) ^ 2 =
        -4 * (Real.pi * r ^ 2 * ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2) := by
      rw [one_div, inv_pow, div_inv_eq_mul]
      ring
    have h_eq2 : -Real.pi * ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2 / (1 / r) ^ 2 =
        -(Real.pi * r ^ 2 * ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2) := by
      rw [one_div, inv_pow, div_inv_eq_mul]
      ring
    rw [h_eq1, h_eq2]
    have : 0 ≤ Real.pi * r ^ 2 * ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by positivity
    linarith
  have h_cov_pos : 0 < ZLattice.covolume M := ZLattice.covolume_pos M MeasureTheory.volume
  have h_fac_nonneg : 0 ≤ (ZLattice.covolume M)⁻¹ * (2 ^ n * r ^ n) := by positivity
  rw [h1, h2, mul_pow]
  calc (ZLattice.covolume M)⁻¹ * (2 ^ n * r ^ n) * rhoDual (1 / (2 * r)) M
      ≤ (ZLattice.covolume M)⁻¹ * (2 ^ n * r ^ n) * rhoDual (1 / r) M :=
        mul_le_mul_of_nonneg_left h_dual_le h_fac_nonneg
    _ = 2 ^ n * ((ZLattice.covolume M)⁻¹ * r ^ n * rhoDual (1 / r) M) := by ring

private lemma tsum_subtype_rho_le {n : ℕ} (M : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology M] [IsZLattice ℝ M] {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (P : Set M) (hP : ∀ x ∈ P, R ≤ ‖(x : EuclideanSpace ℝ (Fin n))‖) :
    (∑' x : P, rho r (x.1 : EuclideanSpace ℝ (Fin n))) ≤
      2 ^ n * Real.exp (-Real.pi * (3 / 4) * (R / r) ^ 2) * rhoLattice r M := by
  have hr2 : 0 < 2 * r := by positivity
  have h_sum2 : Summable (fun x : M => rho (2 * r) (x : EuclideanSpace ℝ (Fin n))) :=
    (summable_rho_lattice M hr2).1
  have h_sum1 : Summable (fun x : M => rho r (x : EuclideanSpace ℝ (Fin n))) :=
    (summable_rho_lattice M hr).1
  have h_pw : ∀ x : P, rho r (x.1 : EuclideanSpace ℝ (Fin n)) ≤
      Real.exp (-Real.pi * (3 / 4) * (R / r) ^ 2) * rho (2 * r) (x.1 : EuclideanSpace ℝ (Fin n)) := by
    intro x
    unfold rho
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hxR : R ≤ ‖(x.1 : EuclideanSpace ℝ (Fin n))‖ := hP x.1 x.2
    have h_sq : R ^ 2 ≤ ‖(x.1 : EuclideanSpace ℝ (Fin n))‖ ^ 2 :=
      pow_le_pow_left₀ hR hxR 2
    have h_div : (R / r) ^ 2 ≤ ‖(x.1 : EuclideanSpace ℝ (Fin n))‖ ^ 2 / r ^ 2 := by
      rw [div_pow]
      exact div_le_div_of_nonneg_right h_sq (sq_nonneg r)
    have h_split : -Real.pi * ‖(x.1 : EuclideanSpace ℝ (Fin n))‖ ^ 2 / r ^ 2 =
        -Real.pi * (3 / 4) * (‖(x.1 : EuclideanSpace ℝ (Fin n))‖ ^ 2 / r ^ 2) +
          (-Real.pi * ‖(x.1 : EuclideanSpace ℝ (Fin n))‖ ^ 2 / (2 * r) ^ 2) := by ring
    rw [h_split]
    have h_pi : 0 ≤ Real.pi * (3 / 4) := by positivity
    nlinarith
  have h_sub_sum1 : Summable (fun x : P => rho r (x.1 : EuclideanSpace ℝ (Fin n))) :=
    h_sum1.subtype P
  have h_sub_sum2 : Summable (fun x : P => rho (2 * r) (x.1 : EuclideanSpace ℝ (Fin n))) :=
    h_sum2.subtype P
  have h_le1 : (∑' x : P, rho r (x.1 : EuclideanSpace ℝ (Fin n))) ≤
      Real.exp (-Real.pi * (3 / 4) * (R / r) ^ 2) *
        ∑' x : P, rho (2 * r) (x.1 : EuclideanSpace ℝ (Fin n)) := by
    rw [← tsum_mul_left]
    exact h_sub_sum1.tsum_le_tsum h_pw (h_sub_sum2.mul_left _)
  have h_split2 := h_sum2.tsum_subtype_add_tsum_subtype_compl P
  have h_compl_nonneg : 0 ≤ ∑' x : ↑Pᶜ, rho (2 * r) (x.1 : EuclideanSpace ℝ (Fin n)) :=
    tsum_nonneg fun x => by unfold rho; positivity
  have h_le2 : (∑' x : P, rho (2 * r) (x.1 : EuclideanSpace ℝ (Fin n))) ≤ rhoLattice (2 * r) M := by
    unfold rhoLattice
    linarith
  calc (∑' x : P, rho r (x.1 : EuclideanSpace ℝ (Fin n)))
      ≤ Real.exp (-Real.pi * (3 / 4) * (R / r) ^ 2) * rhoLattice (2 * r) M :=
        h_le1.trans (mul_le_mul_of_nonneg_left h_le2 (Real.exp_nonneg _))
    _ ≤ Real.exp (-Real.pi * (3 / 4) * (R / r) ^ 2) * (2 ^ n * rhoLattice r M) :=
        mul_le_mul_of_nonneg_left (rhoLattice_two_mul_le M hr) (Real.exp_nonneg _)
    _ = 2 ^ n * Real.exp (-Real.pi * (3 / 4) * (R / r) ^ 2) * rhoLattice r M := by ring

private lemma finrank_span_short_le {n : ℕ} (hn : 0 < n)
    (M : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    {r₀ : ℝ} (hr₀ : r₀ < lambdaN M) :
    Module.finrank ℝ (Submodule.span ℝ {y : EuclideanSpace ℝ (Fin n) | y ∈ M ∧ ‖y‖ ≤ r₀}) ≤ n - 1 := by
  classical
  set A : Set (EuclideanSpace ℝ (Fin n)) := {y | y ∈ M ∧ ‖y‖ ≤ r₀}
  set H : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := Submodule.span ℝ A
  by_contra h_gt
  push Not at h_gt
  have h_le_n : Module.finrank ℝ H ≤ n := by
    have := H.finrank_le
    rwa [finrank_euclideanSpace_fin] at this
  have h_eq_n : Module.finrank ℝ H = n := by omega
  have h_top : H = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [h_eq_n, finrank_euclideanSpace_fin]
  obtain ⟨B, hBA, hB_span, hB_li⟩ := exists_linearIndependent ℝ A
  have hB_top : Submodule.span ℝ B = ⊤ := by
    rw [hB_span]
    exact h_top
  have : Finite B := hB_li.finite
  let _ : Fintype B := Fintype.ofFinite B
  have hB_card : Fintype.card B = n := by
    have h_fr := finrank_span_eq_card hB_li
    rw [Subtype.range_coe, hB_top, finrank_top, finrank_euclideanSpace_fin] at h_fr
    exact h_fr.symm
  let e : Fin n ≃ B := (Fintype.equivFinOfCardEq hB_card).symm
  let v : Fin n → EuclideanSpace ℝ (Fin n) := fun i => (e i : EuclideanSpace ℝ (Fin n))
  have hv_li : LinearIndependent ℝ v := hB_li.comp e e.injective
  have hr₀_mem : r₀ ∈ {r : ℝ | ∃ w : Fin n → EuclideanSpace ℝ (Fin n),
      LinearIndependent ℝ w ∧ ∀ i, w i ∈ M ∧ ‖w i‖ ≤ r} := by
    refine ⟨v, hv_li, fun i => ?_⟩
    exact hBA (e i).2
  have h_le : lambdaN M ≤ r₀ := csInf_le (lambdaN_set_bddBelow hn M) hr₀_mem
  linarith

private lemma exists_unit_orth {n : ℕ} (H : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hH : Module.finrank ℝ H ≤ n - 1) (hn : 0 < n) :
    ∃ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 ∧ ∀ u ∈ H, inner ℝ w u = 0 := by
  have h_finrank_tot : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n :=
    finrank_euclideanSpace_fin
  have h_orth_sum :
      Module.finrank ℝ H + Module.finrank ℝ Hᗮ =
        Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) :=
    H.finrank_add_finrank_orthogonal
  have h_exists_v : ∃ v : Hᗮ, v ≠ 0 := by
    by_contra h_all
    push Not at h_all
    have : Subsingleton Hᗮ := Subsingleton.intro (fun a b => by rw [h_all a, h_all b])
    have h0 : Module.finrank ℝ Hᗮ = 0 := Module.finrank_zero_of_subsingleton
    omega
  rcases h_exists_v with ⟨v, hv⟩
  have hv_coe : (v : EuclideanSpace ℝ (Fin n)) ≠ 0 := Submodule.coe_eq_zero.not.mpr hv
  have hv_norm : ‖(v : EuclideanSpace ℝ (Fin n))‖ ≠ 0 := norm_ne_zero_iff.mpr hv_coe
  let w : EuclideanSpace ℝ (Fin n) :=
    ‖(v : EuclideanSpace ℝ (Fin n))‖⁻¹ • (v : EuclideanSpace ℝ (Fin n))
  have hw : ‖w‖ = 1 := by
    dsimp [w]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hv_norm]
  have hw_mem : w ∈ Hᗮ := Hᗮ.smul_mem ‖(v : EuclideanSpace ℝ (Fin n))‖⁻¹ v.2
  refine ⟨w, hw, fun u hu => ?_⟩
  rw [real_inner_comm]
  exact (H.mem_orthogonal w).mp hw_mem u hu

private lemma tsum_in_H_le {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] {r : ℝ} (hr : 0 < r)
    (H : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖ = 1) (hw_orth : ∀ u ∈ H, inner ℝ w u = 0) :
    (∑' y : {y : dual L // (y : EuclideanSpace ℝ (Fin n)) ∈ H},
        rho r (y.1 : EuclideanSpace ℝ (Fin n))) ≤
      (1 / Real.sqrt 2) * rhoLattice (Real.sqrt 2 / r) L * rhoLattice r (dual L) := by
  let ε : ℝ := rhoDualNonzero (Real.sqrt 2 / r) (dual L) + 1
  have h_nonneg : 0 ≤ rhoDualNonzero (Real.sqrt 2 / r) (dual L) :=
    tsum_nonneg fun y => by unfold rho; positivity
  have hε : 0 < ε := by dsimp [ε]; linarith
  have h_sp : Real.sqrt 2 * smoothingParam (dual L) ε ≤ r := by
    have hs_pos : 0 < r / Real.sqrt 2 := by positivity
    have hs_mem : r / Real.sqrt 2 ∈ {s : ℝ | 0 < s ∧ rhoDualNonzero (1 / s) (dual L) ≤ ε} := by
      refine ⟨hs_pos, ?_⟩
      rw [one_div_div]
      dsimp [ε]
      linarith
    have h_bdd : BddBelow {s : ℝ | 0 < s ∧ rhoDualNonzero (1 / s) (dual L) ≤ ε} :=
      ⟨0, fun s hs => hs.1.le⟩
    have h_csInf : smoothingParam (dual L) ε ≤ r / Real.sqrt 2 := csInf_le h_bdd hs_mem
    rwa [le_div_iff₀ (by positivity), mul_comm] at h_csInf
  have h_chain := (expectation_chain (dual L) hε hr h_sp w hw).2.2.1
  obtain ⟨h_sum_rho, h_rho_pos⟩ := summable_rho_lattice (dual L) hr
  have h_sum_dg : Summable (RegevLWE.Hyperplane.discreteGaussian (dual L) r) :=
    h_sum_rho.div_const (rhoLattice r (dual L))
  have h_dg_nonneg : ∀ y : dual L, 0 ≤ RegevLWE.Hyperplane.discreteGaussian (dual L) r y := by
    intro y
    unfold RegevLWE.Hyperplane.discreteGaussian rho
    exact div_nonneg (Real.exp_nonneg _) h_rho_pos.le
  let f : dual L → ℝ := fun y =>
    RegevLWE.Hyperplane.discreteGaussian (dual L) r y *
      Real.exp (-Real.pi * (inner ℝ w (y : EuclideanSpace ℝ (Fin n))) ^ 2 / r ^ 2)
  have hf_nonneg : ∀ y : dual L, 0 ≤ f y :=
    fun y => mul_nonneg (h_dg_nonneg y) (Real.exp_nonneg _)
  have hf_le : ∀ y : dual L, f y ≤ RegevLWE.Hyperplane.discreteGaussian (dual L) r y := by
    intro y
    dsimp [f]
    have h_arg : -Real.pi * (inner ℝ w (y : EuclideanSpace ℝ (Fin n))) ^ 2 / r ^ 2 ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg
      · have : 0 ≤ Real.pi * (inner ℝ w (y : EuclideanSpace ℝ (Fin n))) ^ 2 := by positivity
        linarith
      · exact sq_nonneg r
    exact mul_le_of_le_one_right (h_dg_nonneg y) (Real.exp_le_one_iff.mpr h_arg)
  have h_sum_f : Summable f := Summable.of_nonneg_of_le hf_nonneg hf_le h_sum_dg
  let S : Set (dual L) := {y : dual L | (y : EuclideanSpace ℝ (Fin n)) ∈ H}
  have h_split_f := h_sum_f.tsum_subtype_add_tsum_subtype_compl S
  have h_compl_nonneg : 0 ≤ ∑' y : ↑Sᶜ, f y := tsum_nonneg fun y => hf_nonneg y.1
  have h_sub_le : (∑' y : S, f y) ≤ ∑' y : dual L, f y := by linarith
  have h_sub_eq : (∑' y : S, f y) =
      (∑' y : S, rho r (y.1 : EuclideanSpace ℝ (Fin n))) / rhoLattice r (dual L) := by
    rw [← tsum_div_const]
    refine tsum_congr fun y => ?_
    dsimp [f, RegevLWE.Hyperplane.discreteGaussian]
    rw [hw_orth (y.1 : EuclideanSpace ℝ (Fin n)) y.2]
    simp
  have h_dual_dual : rhoDual (Real.sqrt 2 / r) (dual L) = rhoLattice (Real.sqrt 2 / r) L := by
    unfold rhoDual rhoLattice
    rw [dual_dual_eq L]
  have h_poiss := (rhoLattice_poisson (dual L) hr).2
  have h_pref_le : (ZLattice.covolume (dual L))⁻¹ * r ^ n / (Real.sqrt 2 * rhoLattice r (dual L)) ≤
      1 / Real.sqrt 2 := by
    have h_sqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    rw [div_le_div_iff₀ (by positivity) h_sqrt2_pos]
    nlinarith
  have h_rhoL_nonneg : 0 ≤ rhoLattice (Real.sqrt 2 / r) L :=
    tsum_nonneg fun x => by unfold rho; positivity
  have h_div_le : (∑' y : S, rho r (y.1 : EuclideanSpace ℝ (Fin n))) / rhoLattice r (dual L) ≤
      (1 / Real.sqrt 2) * rhoLattice (Real.sqrt 2 / r) L := by
    calc (∑' y : S, rho r (y.1 : EuclideanSpace ℝ (Fin n))) / rhoLattice r (dual L)
        = ∑' y : S, f y := h_sub_eq.symm
      _ ≤ ∑' y : dual L, f y := h_sub_le
      _ ≤ (ZLattice.covolume (dual L))⁻¹ * r ^ n / (Real.sqrt 2 * rhoLattice r (dual L)) *
            rhoDual (Real.sqrt 2 / r) (dual L) := h_chain
      _ = (ZLattice.covolume (dual L))⁻¹ * r ^ n / (Real.sqrt 2 * rhoLattice r (dual L)) *
            rhoLattice (Real.sqrt 2 / r) L := by rw [h_dual_dual]
      _ ≤ (1 / Real.sqrt 2) * rhoLattice (Real.sqrt 2 / r) L :=
            mul_le_mul_of_nonneg_right h_pref_le h_rhoL_nonneg
  rwa [div_le_iff₀ h_rho_pos] at h_div_le

private lemma gamma_bound :
    2 * Real.exp (-Real.pi * (3 / 4) / Real.sqrt 2) ≤ 5 / 13 := by
  have h_pi : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
  have h_sqrt2_le : Real.sqrt 2 ≤ 1.4143 := by
    rw [Real.sqrt_le_iff]
    norm_num
  have h_sqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h_ratio : (333 / 200 : ℝ) ≤ Real.pi * (3 / 4) / Real.sqrt 2 := by
    rw [le_div_iff₀ h_sqrt2_pos]
    linarith
  have h_exp_ge : (26 / 5 : ℝ) ≤ Real.exp (333 / 200) := by
    have h_sum := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 333 / 200) 6
    have h_val : (26 / 5 : ℝ) ≤ ∑ i ∈ Finset.range 6, (333 / 200 : ℝ) ^ i / i.factorial := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    exact h_val.trans h_sum
  have h_exp_le : Real.exp (-Real.pi * (3 / 4) / Real.sqrt 2) ≤ Real.exp (-(333 / 200 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have h_neg_eq : -Real.pi * (3 / 4) / Real.sqrt 2 = -(Real.pi * (3 / 4) / Real.sqrt 2) := by
      ring
    rw [h_neg_eq]
    linarith
  rw [Real.exp_neg] at h_exp_le
  have h_inv_le : (Real.exp (333 / 200))⁻¹ ≤ (26 / 5 : ℝ)⁻¹ :=
    inv_anti₀ (by norm_num) h_exp_ge
  linarith

private lemma upper_bound_dim_ge_two {n : ℕ} (hn2 : 2 ≤ n)
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L] [IsZLattice ℝ L] :
    lambda1 L * lambdaN (dual L) ≤ n := by
  have hn : 0 < n := by omega
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  obtain ⟨v₁, hv₁_mem, hv₁_ne, hv₁_norm⟩ := exists_norm_eq_lambda1 hn L
  have hl1_pos : 0 < lambda1 L := by rw [← hv₁_norm]; exact norm_pos_iff.mpr hv₁_ne
  by_contra h_gt
  push Not at h_gt
  have h_lt_lN : (n : ℝ) / lambda1 L < lambdaN (dual L) := by
    rw [div_lt_iff₀ hl1_pos]
    linarith
  obtain ⟨r₀, hr₀_gt, hr₀_lt⟩ := exists_between h_lt_lN
  have hr₀_pos : 0 < r₀ := (div_pos hn_pos hl1_pos).trans hr₀_gt
  have h_prod_gt : (n : ℝ) < lambda1 L * r₀ := by
    rw [div_lt_iff₀ hl1_pos] at hr₀_gt
    linarith
  set A : Set (EuclideanSpace ℝ (Fin n)) := {y | y ∈ dual L ∧ ‖y‖ ≤ r₀}
  set H : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := Submodule.span ℝ A
  have hH_rank : Module.finrank ℝ H ≤ n - 1 := finrank_span_short_le hn (dual L) hr₀_lt
  obtain ⟨w, hw, hw_orth⟩ := exists_unit_orth H hH_rank hn
  let c : ℝ := Real.sqrt (Real.sqrt 2)
  have hc_pos : 0 < c := by positivity
  have hc_sq : c ^ 2 = Real.sqrt 2 := Real.sq_sqrt (by positivity)
  let r : ℝ := c * r₀ / Real.sqrt n
  have hr_pos : 0 < r := by positivity
  let u : ℝ := Real.sqrt 2 / r
  have hu_pos : 0 < u := by positivity
  have h_r0_div_r_sq : (r₀ / r) ^ 2 = (n : ℝ) / Real.sqrt 2 := by
    dsimp [r]
    have h_eq : r₀ / (c * r₀ / Real.sqrt n) = Real.sqrt n / c := by
      field_simp
    rw [h_eq, div_pow, Real.sq_sqrt hn_pos.le, hc_sq]
  have h_l1_div_u_sq : (n : ℝ) / Real.sqrt 2 ≤ (lambda1 L / u) ^ 2 := by
    dsimp [u, r]
    have h_eq : lambda1 L / (Real.sqrt 2 / (c * r₀ / Real.sqrt n)) =
        (lambda1 L * r₀) * c / (Real.sqrt 2 * Real.sqrt n) := by
      field_simp
    rw [h_eq, div_pow, mul_pow (lambda1 L * r₀) c 2, mul_pow (Real.sqrt 2) (Real.sqrt n) 2,
      hc_sq, Real.sq_sqrt (by norm_num), Real.sq_sqrt hn_pos.le]
    have h_sq_gt : (n : ℝ) ^ 2 ≤ (lambda1 L * r₀) ^ 2 :=
      pow_le_pow_left₀ hn_pos.le h_prod_gt.le 2
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    calc (n : ℝ) / Real.sqrt 2
        = (n : ℝ) ^ 2 * Real.sqrt 2 / (2 * (n : ℝ)) := by
          field_simp
          nlinarith [h2]
      _ ≤ (lambda1 L * r₀) ^ 2 * Real.sqrt 2 / (2 * (n : ℝ)) := by gcongr
  let q : ℝ := (2 * Real.exp (-Real.pi * (3 / 4) / Real.sqrt 2)) ^ n
  have h_gamma_nonneg : 0 ≤ 2 * Real.exp (-Real.pi * (3 / 4) / Real.sqrt 2) := by positivity
  have h_gamma_le : 2 * Real.exp (-Real.pi * (3 / 4) / Real.sqrt 2) ≤ 5 / 13 := gamma_bound
  have hq_le : q ≤ (5 / 13 : ℝ) ^ 2 := by
    dsimp [q]
    calc (2 * Real.exp (-Real.pi * (3 / 4) / Real.sqrt 2)) ^ n
        ≤ (5 / 13 : ℝ) ^ n := pow_le_pow_left₀ h_gamma_nonneg h_gamma_le n
      _ ≤ (5 / 13 : ℝ) ^ 2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn2
  have h_tail_factor_eq :
      2 ^ n * Real.exp (-Real.pi * (3 / 4) * ((n : ℝ) / Real.sqrt 2)) = q := by
    dsimp [q]
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  -- Tail bound on dual L \ H
  let S_H : Set (dual L) := {y : dual L | (y : EuclideanSpace ℝ (Fin n)) ∈ H}
  have h_compl_norm : ∀ y ∈ S_Hᶜ, r₀ ≤ ‖(y : EuclideanSpace ℝ (Fin n))‖ := by
    intro y hy
    by_contra h_lt
    push Not at h_lt
    apply hy
    exact Submodule.subset_span ⟨y.2, h_lt.le⟩
  have h_tail_dual : (∑' y : ↑S_Hᶜ, rho r (y.1 : EuclideanSpace ℝ (Fin n))) ≤
      q * rhoLattice r (dual L) := by
    have h_raw := tsum_subtype_rho_le (dual L) hr_pos hr₀_pos.le S_Hᶜ h_compl_norm
    rwa [h_r0_div_r_sq, h_tail_factor_eq] at h_raw
  -- Tail bound on L \ {0}
  let S_nz : Set L := {x : L | x ≠ 0}
  have h_nz_norm : ∀ x ∈ S_nz, lambda1 L ≤ ‖(x : EuclideanSpace ℝ (Fin n))‖ := by
    intro x hx
    exact norm_ge_lambda1 L x.2 (Submodule.coe_eq_zero.not.mpr hx)
  have h_tail_L : (∑' x : S_nz, rho u (x.1 : EuclideanSpace ℝ (Fin n))) ≤
      q * rhoLattice u L := by
    have h_raw := tsum_subtype_rho_le L hu_pos hl1_pos.le S_nz h_nz_norm
    have h_exp_le : Real.exp (-Real.pi * (3 / 4) * (lambda1 L / u) ^ 2) ≤
        Real.exp (-Real.pi * (3 / 4) * ((n : ℝ) / Real.sqrt 2)) := by
      apply Real.exp_le_exp.mpr
      have : 0 ≤ Real.pi * (3 / 4) := by positivity
      nlinarith
    have h_rho_u_nonneg : 0 ≤ rhoLattice u L := (summable_rho_lattice L hu_pos).2.le
    calc (∑' x : S_nz, rho u (x.1 : EuclideanSpace ℝ (Fin n)))
        ≤ 2 ^ n * Real.exp (-Real.pi * (3 / 4) * (lambda1 L / u) ^ 2) * rhoLattice u L := h_raw
      _ ≤ 2 ^ n * Real.exp (-Real.pi * (3 / 4) * ((n : ℝ) / Real.sqrt 2)) * rhoLattice u L := by
          gcongr
      _ = q * rhoLattice u L := by rw [h_tail_factor_eq]
  -- Split rhoLattice u L into {0} and S_nz
  obtain ⟨h_sum_u, h_rho_u_pos⟩ := summable_rho_lattice L hu_pos
  have h_compl_zero : ({0} : Set L)ᶜ = S_nz := by ext x; simp [S_nz]
  have h_split_L := h_sum_u.tsum_subtype_add_tsum_subtype_compl ({0} : Set L)
  rw [tsum_singleton 0 (fun x : L => rho u (x : EuclideanSpace ℝ (Fin n))), h_compl_zero] at h_split_L
  have h_zero_rho : rho u ((0 : L) : EuclideanSpace ℝ (Fin n)) = 1 := by simp [rho]
  have h_rho_u_eq : 1 + (∑' x : S_nz, rho u (x.1 : EuclideanSpace ℝ (Fin n))) = rhoLattice u L := by
    unfold rhoLattice
    rw [← h_split_L, h_zero_rho]
  have h_rho_u_bound : (1 - q) * rhoLattice u L ≤ 1 := by linarith
  have h_1_sub_q_pos : (144 / 169 : ℝ) ≤ 1 - q := by linarith
  have h_rho_u_le : rhoLattice u L ≤ 169 / 144 := by
    have : (144 / 169 : ℝ) * rhoLattice u L ≤ (1 - q) * rhoLattice u L :=
      mul_le_mul_of_nonneg_right h_1_sub_q_pos h_rho_u_pos.le
    linarith
  -- Combine in_H and out_of_H on dual L
  obtain ⟨h_sum_dual, h_rho_dual_pos⟩ := summable_rho_lattice (dual L) hr_pos
  have h_split_dual := h_sum_dual.tsum_subtype_add_tsum_subtype_compl S_H
  have h_in_H := tsum_in_H_le L hr_pos H w hw hw_orth
  change (∑' y : S_H, rho r (y.1 : EuclideanSpace ℝ (Fin n))) ≤
      (1 / Real.sqrt 2) * rhoLattice u L * rhoLattice r (dual L) at h_in_H
  have h_eq : (∑' y : S_H, rho r (y.1 : EuclideanSpace ℝ (Fin n))) +
      (∑' y : ↑S_Hᶜ, rho r (y.1 : EuclideanSpace ℝ (Fin n))) = rhoLattice r (dual L) := by
    unfold rhoLattice
    exact h_split_dual
  have h_sum_dual_le :
      rhoLattice r (dual L) ≤
        ((1 / Real.sqrt 2) * rhoLattice u L + q) * rhoLattice r (dual L) := by
    linarith
  have h_coeff_ge_one : 1 ≤ (1 / Real.sqrt 2) * rhoLattice u L + q := by
    nlinarith
  have h_sqrt2_ge : (1.4142 : ℝ) ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.4142)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h_inv_sqrt2_le : 1 / Real.sqrt 2 ≤ 1 / 1.4142 :=
    one_div_le_one_div_of_le (by norm_num) h_sqrt2_ge
  have h_coeff_lt_one : (1 / Real.sqrt 2) * rhoLattice u L + q < 1 := by
    calc (1 / Real.sqrt 2) * rhoLattice u L + q
        ≤ (1 / 1.4142) * (169 / 144) + (5 / 13) ^ 2 := by
          gcongr
      _ < 1 := by norm_num
  linarith

theorem lemma_2_3 {n : ℕ} (hn : 0 < n) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    1 ≤ lambda1 L * lambdaN (RegevLWE.GaussConv.dual L) ∧
      lambda1 L * lambdaN (RegevLWE.GaussConv.dual L) ≤ n := by
  refine ⟨lower_bound_lemma_2_3 hn L, ?_⟩
  by_cases hn1 : n = 1
  · subst hn1
    exact upper_bound_dim_one L
  · have hn2 : 2 ≤ n := by omega
    exact upper_bound_dim_ge_two hn2 L

end RegevLWE.SmoothingLB

open RegevLWE.SmoothingLB

theorem solution {n : ℕ} (hn : 0 < n) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    1 ≤ lambda1 L * lambdaN (RegevLWE.GaussConv.dual L) ∧
      lambda1 L * lambdaN (RegevLWE.GaussConv.dual L) ≤ n :=
  RegevLWE.SmoothingLB.lemma_2_3 hn L
