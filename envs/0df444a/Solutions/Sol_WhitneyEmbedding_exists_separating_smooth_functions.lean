-- Prove2me | solution 1 for WhitneyEmbedding.exists_separating_smooth_functions
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-11T14:20:39.817111+00:00
-- url     : https://prove2.me/submissions/54eaab87-f346-4bb2-b020-50860bc70fe8

import Mathlib

/-!
# A countable separating family of compactly supported smooth functions

For a Hausdorff, second-countable smooth `n`-manifold `M` we construct a sequence
`seq : ℕ → M → ℝ` of smooth, compactly supported functions which separates points of `M`
and separates tangent vectors.

The construction: around every point `c` pick a smooth bump function `F c`, and let `bumpOne c`
be the open set of points at which `F c` is identically `1` on a neighbourhood.  These sets cover
`M`, and second countability (Lindelöf) yields a countable subcover indexed by a countable set
`T ⊆ M`.  The family then consists of the bumps `F c` together with the truncated coordinates
`x ↦ F c x * (extChartAt (𝓡 n) c x) j` for `c ∈ T` and `j : Fin n`.
-/

open Function Filter Module Set Topology Metric
open scoped Manifold ContDiff

namespace WhitneySeparating

/-- A vector of `EuclideanSpace ℝ (Fin n)` all of whose coordinates vanish is zero. -/
theorem euclidean_eq_zero_of_proj {n : ℕ} (w : EuclideanSpace ℝ (Fin n))
    (h : ∀ j, EuclideanSpace.proj (𝕜 := ℝ) j w = 0) : w = 0 := by
  ext j
  simpa using h j

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- The open set of points where the bump function `f` centred at `c` is identically one
on a neighbourhood. -/
def bumpOne (c : M) (f : SmoothBumpFunction (𝓡 n) c) : Set M :=
  (chartAt (EuclideanSpace ℝ (Fin n)) c).source ∩
    extChartAt (𝓡 n) c ⁻¹' ball (extChartAt (𝓡 n) c c) f.rIn

theorem isOpen_bumpOne (c : M) (f : SmoothBumpFunction (𝓡 n) c) : IsOpen (bumpOne c f) :=
  isOpen_extChartAt_preimage c isOpen_ball

theorem self_mem_bumpOne (c : M) (f : SmoothBumpFunction (𝓡 n) c) : c ∈ bumpOne c f :=
  ⟨mem_chart_source _ _, by simpa using f.rIn_pos⟩

theorem eventuallyEq_one_of_mem_bumpOne {c x : M} (f : SmoothBumpFunction (𝓡 n) c)
    (hx : x ∈ bumpOne c f) : (f : M → ℝ) =ᶠ[𝓝 x] 1 :=
  f.eventuallyEq_one_of_dist_lt hx.1 hx.2

theorem eq_one_of_mem_bumpOne {c x : M} (f : SmoothBumpFunction (𝓡 n) c)
    (hx : x ∈ bumpOne c f) : f x = 1 :=
  (eventuallyEq_one_of_mem_bumpOne f hx).eq_of_nhds

variable [IsManifold (𝓡 n) ∞ M] [T2Space M]

/-- The truncated coordinate functions of a chart are smooth on all of `M`. -/
theorem contMDiff_bump_mul_coord (c : M) (f : SmoothBumpFunction (𝓡 n) c) (j : Fin n) :
    ContMDiff (𝓡 n) 𝓘(ℝ) ∞ (fun x => f x * (extChartAt (𝓡 n) c x) j) := by
  have h : ContMDiff (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (fun x => f x • extChartAt (𝓡 n) c x) := f.contMDiff_smul contMDiffOn_extChartAt
  exact (EuclideanSpace.proj (𝕜 := ℝ) j).contMDiff.comp h

omit [IsManifold (𝓡 n) ∞ M] in
theorem hasCompactSupport_bump_mul (c : M) (f : SmoothBumpFunction (𝓡 n) c) (g : M → ℝ) :
    HasCompactSupport (fun x => f x * g x) :=
  f.hasCompactSupport.mul_right (f' := g)

omit [T2Space M] in
/-- The differential of a chart coordinate, computed through `extChartAt`. -/
theorem mfderiv_coord_apply {c x : M} (hx : x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) c).source)
    (j : Fin n) (v : TangentSpace (𝓡 n) x) :
    mfderiv (𝓡 n) 𝓘(ℝ) (fun y => (extChartAt (𝓡 n) c y) j) x v =
      EuclideanSpace.proj (𝕜 := ℝ) j
        (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) c) x v) := by
  have h1 : HasMFDerivAt (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (extChartAt (𝓡 n) c) x
      (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) c) x :) :=
    hasMFDerivAt_extChartAt hx
  have h2 := ((EuclideanSpace.proj (𝕜 := ℝ) j).hasMFDerivAt (x := extChartAt (𝓡 n) c x)).comp x h1
  have h3 : HasMFDerivAt (𝓡 n) 𝓘(ℝ) (fun y => (extChartAt (𝓡 n) c y) j) x
      ((EuclideanSpace.proj (𝕜 := ℝ) j).comp
        (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) c) x :)) := h2
  rw [h3.mfderiv]
  rfl

end WhitneySeparating

open WhitneySeparating in
/-- **Countable separating family.** A Hausdorff, second-countable smooth `n`-manifold carries a
sequence of smooth, compactly supported real functions separating points and tangent vectors. -/
theorem solution (n : ℕ)
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [T2Space M] [SecondCountableTopology M] :
    ∃ (seq : ℕ → M → ℝ),
      (∀ k, ContMDiff (𝓡 n) 𝓘(ℝ) ∞ (seq k)) ∧
      (∀ k, HasCompactSupport (seq k)) ∧
      (∀ x y, x ≠ y → ∃ k, seq k x ≠ seq k y) ∧
      (∀ x, ∀ (v : TangentSpace (𝓡 n) x), v ≠ 0 →
        ∃ k, mfderiv (𝓡 n) 𝓘(ℝ) (seq k) x v ≠ 0) := by
  classical
  rcases isEmpty_or_nonempty M with hM | hM
  · refine ⟨fun _ _ => 0, fun _ => contMDiff_const, fun _ => ?_, fun x => isEmptyElim x,
      fun x => isEmptyElim x⟩
    simp [HasCompactSupport, tsupport]
  · -- a bump function around every point
    have F : ∀ c : M, SmoothBumpFunction (𝓡 n) c := fun c => Classical.arbitrary _
    obtain ⟨T, hTc, hTU⟩ :=
      TopologicalSpace.isOpen_iUnion_countable (fun c : M => bumpOne c (F c))
        (fun c => isOpen_bumpOne c (F c))
    have hcov : ∀ x : M, ∃ c ∈ T, x ∈ bumpOne c (F c) := by
      intro x
      have hx : x ∈ ⋃ c, bumpOne c (F c) := mem_iUnion.2 ⟨x, self_mem_bumpOne x (F x)⟩
      rw [← hTU] at hx
      simpa using hx
    have : Countable T := hTc.to_subtype
    have : Nonempty T := by
      obtain ⟨x⟩ := hM
      obtain ⟨c, hc, -⟩ := hcov x
      exact ⟨⟨c, hc⟩⟩
    obtain ⟨enum, henum⟩ := exists_surjective_nat (T × Option (Fin n))
    -- the family: bumps and truncated coordinates
    set G : T × Option (Fin n) → M → ℝ := fun p x =>
      F (p.1 : M) x * p.2.elim 1 (fun j => (extChartAt (𝓡 n) (p.1 : M) x) j) with hGdef
    have hGsmooth : ∀ p, ContMDiff (𝓡 n) 𝓘(ℝ) ∞ (G p) := by
      rintro ⟨c, j | j⟩
      · simpa [hGdef] using (F (c : M)).contMDiff
      · simpa [hGdef] using contMDiff_bump_mul_coord (c : M) (F (c : M)) j
    have hGsupp : ∀ p, HasCompactSupport (G p) := by
      rintro ⟨c, o⟩
      exact hasCompactSupport_bump_mul (c : M) (F (c : M)) _
    refine ⟨fun k => G (enum k), fun k => hGsmooth _, fun k => hGsupp _, ?_, ?_⟩
    · -- separation of points
      intro x y hxy
      obtain ⟨c, hcT, hxU⟩ := hcov x
      by_contra hcon
      push_neg at hcon
      have hall : ∀ p, G p x = G p y := by
        intro p
        obtain ⟨k, rfl⟩ := henum p
        exact hcon k
      have hx1 : F c x = 1 := eq_one_of_mem_bumpOne (F c) hxU
      have hy1 : F c y = 1 := by
        have := hall (⟨c, hcT⟩, none)
        simpa [hGdef, hx1] using this.symm
      have hcoord : ∀ j : Fin n, (extChartAt (𝓡 n) c x) j = (extChartAt (𝓡 n) c y) j := by
        intro j
        have := hall (⟨c, hcT⟩, some j)
        simpa [hGdef, hx1, hy1] using this
      have hxy' : extChartAt (𝓡 n) c x = extChartAt (𝓡 n) c y := by
        ext j; exact hcoord j
      have hxs : x ∈ (extChartAt (𝓡 n) c).source := by
        rw [extChartAt_source]; exact hxU.1
      have hys : y ∈ (extChartAt (𝓡 n) c).source := by
        rw [extChartAt_source]
        exact (F c).support_subset_source (by simp [mem_support, hy1])
      exact hxy ((extChartAt (𝓡 n) c).injOn hxs hys hxy')
    · -- separation of tangent vectors
      intro x v hv
      obtain ⟨c, hcT, hxU⟩ := hcov x
      by_contra hcon
      push_neg at hcon
      have hall : ∀ p, mfderiv (𝓡 n) 𝓘(ℝ) (G p) x v = 0 := by
        intro p
        obtain ⟨k, rfl⟩ := henum p
        exact hcon k
      have hone : (F c : M → ℝ) =ᶠ[𝓝 x] 1 := eventuallyEq_one_of_mem_bumpOne (F c) hxU
      have hcoord : ∀ j : Fin n,
          mfderiv (𝓡 n) 𝓘(ℝ) (fun y => (extChartAt (𝓡 n) c y) j) x v = 0 := by
        intro j
        have heq : G (⟨c, hcT⟩, some j) =ᶠ[𝓝 x] fun y => (extChartAt (𝓡 n) c y) j := by
          filter_upwards [hone] with z hz
          simp [hGdef, hz]
        rw [← heq.mfderiv_eq]
        exact hall (⟨c, hcT⟩, some j)
      have hDv : ∀ j : Fin n, EuclideanSpace.proj (𝕜 := ℝ) j
          (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) c) x v) = 0 := by
        intro j
        have hj := hcoord j
        rwa [mfderiv_coord_apply hxU.1 j v] at hj
      have hker :=
        (mdifferentiable_chart (I := 𝓡 n) (M := M) c).ker_mfderiv_eq_bot (x := x) hxU.1
      have hmem : v ∈ (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) c) x).ker :=
        LinearMap.mem_ker.mpr (euclidean_eq_zero_of_proj _ hDv)
      rw [hker] at hmem
      exact hv hmem
