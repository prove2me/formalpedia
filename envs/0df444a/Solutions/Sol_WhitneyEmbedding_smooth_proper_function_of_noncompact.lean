-- Prove2me | solution 1 for WhitneyEmbedding.smooth_proper_function_of_noncompact
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-11T13:40:23.332884+00:00
-- url     : https://prove2.me/submissions/922f0ff6-222b-4a1f-adb0-3137a558c19e

import Mathlib

open Function Filter Module Set Topology
open scoped Manifold ContDiff

section KeyLemma

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- If a smooth partition of unity indexed by `ℕ` vanishes at `x` for all indices `≤ N`, then the
weighted sum `∑ᶠ i, f i x • (i : ℝ)` is at least `N + 1`. -/
theorem finsum_index_smul_ge (f : SmoothPartitionOfUnity ℕ I M univ) (x : M) (N : ℕ)
    (h : ∀ i ≤ N, f i x = 0) : (N : ℝ) + 1 ≤ ∑ᶠ i, f i x • (i : ℝ) := by
  have hfin : {i | f i x ≠ 0}.Finite := by
    simpa [Function.support] using f.locallyFinite.point_finite x
  have h1 : ∑ᶠ i, f i x = 1 := f.sum_eq_one (mem_univ x)
  have hsupp₁ : (Function.support fun i : ℕ => ((N : ℝ) + 1) * f i x).Finite :=
    hfin.subset (by intro i hi; simp only [Function.mem_support] at hi ⊢; grind)
  have hsupp₂ : (Function.support fun i : ℕ => f i x • (i : ℝ)).Finite :=
    hfin.subset (by
      intro i hi
      simp only [Function.mem_support, smul_eq_mul, ne_eq, mul_eq_zero, not_or] at hi ⊢
      exact hi.1)
  have hle : (fun i : ℕ => ((N : ℝ) + 1) * f i x) ≤ fun i : ℕ => f i x • (i : ℝ) := by
    intro i
    rcases le_or_gt i N with hi | hi
    · simp [h i hi]
    · have hN : (N : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast hi
      have := f.nonneg i x
      simp only [smul_eq_mul]
      nlinarith
  calc (N : ℝ) + 1 = ((N : ℝ) + 1) * ∑ᶠ i, f i x := by rw [h1]; ring
    _ = ∑ᶠ i, ((N : ℝ) + 1) * f i x := mul_finsum _ _
    _ ≤ ∑ᶠ i, f i x • (i : ℝ) := finsum_le_finsum' hsupp₁ hsupp₂ hle

end KeyLemma

/-- Existence of a smooth proper function (exhaustion function) on a Hausdorff,
second-countable smooth manifold. -/
theorem solution (n : ℕ)
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [T2Space M] [SecondCountableTopology M]
    (hM : ¬ CompactSpace M) :
    ∃ r : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ) ∞ r ∧ IsProperMap r := by
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  have : SigmaCompactSpace M := inferInstance
  -- a countable open cover by relatively compact sets
  have hcov : ∀ i : ℕ, ∃ V : Set M, IsOpen V ∧ compactCovering M i ⊆ V ∧ IsCompact (closure V) :=
    fun i => exists_isOpen_superset_and_isCompact_closure (isCompact_compactCovering M i)
  choose U hUopen hUsub hUcl using hcov
  have hUcover : (univ : Set M) ⊆ ⋃ i, U i := by
    intro x _
    have : x ∈ ⋃ i, compactCovering M i := by rw [iUnion_compactCovering]; trivial
    obtain ⟨i, hi⟩ := mem_iUnion.1 this
    exact mem_iUnion.2 ⟨i, hUsub i hi⟩
  obtain ⟨f, hf⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓡 n) (ι := ℕ) isClosed_univ U hUopen hUcover
  have hsmooth : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ fun x => ∑ᶠ i, f i x • (i : ℝ) :=
    f.contMDiff_finsum_smul (g := fun i _ => (i : ℝ)) fun i x _ => contMDiffAt_const
  refine ⟨fun x => ∑ᶠ i, f i x • (i : ℝ), hsmooth, ?_⟩
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨hsmooth.continuous, fun K hK => ?_⟩
  obtain ⟨C, hC⟩ := hK.isBounded.subset_closedBall (0 : ℝ)
  obtain ⟨N, hN⟩ := exists_nat_ge C
  refine IsCompact.of_isClosed_subset
    (Set.Finite.isCompact_biUnion (Finset.range (N + 1)).finite_toSet fun i _ => hUcl i)
    (hK.isClosed.preimage hsmooth.continuous) ?_
  intro x hx
  have hxK : (∑ᶠ i, f i x • (i : ℝ)) ∈ Metric.closedBall (0 : ℝ) C := hC hx
  have hxle : (∑ᶠ i, f i x • (i : ℝ)) ≤ (N : ℝ) := by
    have := (Real.norm_eq_abs _ ▸ (mem_closedBall_zero_iff.1 hxK) : |∑ᶠ i, f i x • (i : ℝ)| ≤ C)
    have h2 := (abs_le.1 this).2
    linarith
  by_contra hcon
  have hzero : ∀ i ≤ N, f i x = 0 := by
    intro i hi
    by_contra hne
    exact hcon (mem_biUnion (by simp only [Finset.coe_range, mem_Iio]; omega)
      (subset_closure (hf i (subset_tsupport _ hne))))
  have := finsum_index_smul_ge f x N hzero
  linarith
