-- Prove2me | solution 1 for WhitneyEmbedding.exists_projection_linear_map
-- status  : ACCEPTED   (disprove)
-- author  : @Lucas
-- created : 2026-09-11T13:20:23.167708+00:00
-- url     : https://prove2.me/submissions/40b674ae-d522-403e-b3a5-4ccd1967ccbb

import Mathlib
open Function Filter Module Set Topology
open scoped Manifold ContDiff

/-!
# A counterexample to `WhitneyEmbedding.exists_projection_linear_map`

The statement claims that a smooth closed embedding `e : M → ℝ^{2n+1}` of an `n`-manifold with
injective differential can always be composed with a surjective *linear* map
`L : ℝ^{2n+1} → ℝ^{2n}` so that `L ∘ e` is again a proper injective immersion.

This is false already for `n = 1`: take `M` to be the disjoint union of three copies of the real
line, embedded in `ℝ³` as three pairwise skew lines whose directions form a basis.  The set of
secant directions of such a configuration is all of `ℝ³ \ {0}`, while the kernel of any
`L : ℝ³ → ℝ²` is nontrivial; hence `L ∘ e` identifies two distinct points.
-/

namespace WhitneyProjectionCounterexample

abbrev E1 : Type := EuclideanSpace ℝ (Fin 1)
abbrev E2 : Type := EuclideanSpace ℝ (Fin 2)
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The affine parametrisation `t ↦ c + t • u` of a line in `ℝ³`. -/
noncomputable def line (c u : E3) : E1 → E3 := fun t => c + (t 0) • u

lemma line_sub (c u : E3) (t s : E1) : line c u t - line c u s = (t 0 - s 0) • u := by
  simp [line, sub_smul]

lemma isometry_line (c u : E3) (hu : ‖u‖ = 1) : Isometry (line c u) := by
  refine Isometry.of_dist_eq fun t s => ?_
  rw [dist_eq_norm, dist_eq_norm, line_sub, norm_smul, hu, mul_one, EuclideanSpace.norm_eq]
  simp [Real.sqrt_sq_eq_abs]

lemma isClosedEmbedding_line (c u : E3) (hu : ‖u‖ = 1) : IsClosedEmbedding (line c u) :=
  (isometry_line c u hu).isClosedEmbedding

lemma injective_line (c u : E3) (hu : ‖u‖ = 1) : Injective (line c u) :=
  (isometry_line c u hu).injective

lemma contDiff_line (c u : E3) : ContDiff ℝ ∞ (line c u) := by
  have h : ContDiff ℝ ∞ (fun t : E1 => (t 0) • u) :=
    (((EuclideanSpace.proj (0 : Fin 1) : E1 →L[ℝ] ℝ)).smulRight u).contDiff
  exact contDiff_const.add h

lemma contMDiff_line (c u : E3) : ContMDiff (𝓡 1) (𝓡 3) ∞ (line c u) :=
  contMDiff_iff_contDiff.2 (contDiff_line c u)

lemma fderiv_line (c u : E3) (t : E1) :
    fderiv ℝ (line c u) t = ((EuclideanSpace.proj (0 : Fin 1) : E1 →L[ℝ] ℝ)).smulRight u := by
  have h : line c u = fun t : E1 =>
      c + ((EuclideanSpace.proj (0 : Fin 1) : E1 →L[ℝ] ℝ).smulRight u) t := rfl
  rw [h, fderiv_const_add, ContinuousLinearMap.fderiv]

lemma injective_fderiv_line (u : E3) (hu : u ≠ 0) :
    Injective (fun a : E1 => ((EuclideanSpace.proj (0 : Fin 1) : E1 →L[ℝ] ℝ).smulRight u) a) := by
  intro a b hab
  simp only [ContinuousLinearMap.smulRight_apply, EuclideanSpace.proj, PiLp.proj_apply] at hab
  have h : (a 0 - b 0) • u = 0 := by rw [sub_smul, hab, sub_self]
  rcases smul_eq_zero.1 h with h' | h'
  · have h2 : a 0 = b 0 := by linarith [sub_eq_zero.1 h']
    ext i
    fin_cases i
    simpa using h2
  · exact absurd h' hu

lemma injective_mfderiv_line (c u : E3) (hu : u ≠ 0) (t : E1) :
    Injective (mfderiv (𝓡 1) (𝓡 3) (line c u) t) := by
  rw [mfderiv_eq_fderiv, fderiv_line]
  exact injective_fderiv_line u hu

/-! ### The three lines -/

/-- Direction of the first line. -/
noncomputable def d0 : E3 := EuclideanSpace.single 0 1
/-- Direction of the second line. -/
noncomputable def d1 : E3 := EuclideanSpace.single 1 1
/-- Direction of the third line. -/
noncomputable def d2 : E3 := EuclideanSpace.single 2 1
/-- Base point of the first line. -/
noncomputable def b0 : E3 := 0
/-- Base point of the second line. -/
noncomputable def b1 : E3 := EuclideanSpace.single 2 1
/-- Base point of the third line. -/
noncomputable def b2 : E3 := EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1

lemma norm_d0 : ‖d0‖ = 1 := by simp [d0]
lemma norm_d1 : ‖d1‖ = 1 := by simp [d1]
lemma norm_d2 : ‖d2‖ = 1 := by simp [d2]

lemma d0_ne_zero : d0 ≠ 0 := by
  intro h; have h2 : ‖d0‖ = 1 := norm_d0; rw [h] at h2; simp at h2
lemma d1_ne_zero : d1 ≠ 0 := by
  intro h; have h2 : ‖d1‖ = 1 := norm_d1; rw [h] at h2; simp at h2
lemma d2_ne_zero : d2 ≠ 0 := by
  intro h; have h2 : ‖d2‖ = 1 := norm_d2; rw [h] at h2; simp at h2

lemma line0_coord (t : E1) :
    (line b0 d0 t) 0 = t 0 ∧ (line b0 d0 t) 1 = 0 ∧ (line b0 d0 t) 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [line, b0, d0, EuclideanSpace.single_apply]

lemma line1_coord (t : E1) :
    (line b1 d1 t) 0 = 0 ∧ (line b1 d1 t) 1 = t 0 ∧ (line b1 d1 t) 2 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [line, b1, d1, EuclideanSpace.single_apply]

lemma line2_coord (t : E1) :
    (line b2 d2 t) 0 = 1 ∧ (line b2 d2 t) 1 = 1 ∧ (line b2 d2 t) 2 = t 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [line, b2, d2, EuclideanSpace.single_apply]

/-! ### The manifold and the embedding -/

/-- The counterexample manifold: the disjoint union of three copies of the real line. -/
abbrev Mfd : Type := E1 ⊕ E1 ⊕ E1

/-- The embedding of the three lines into `ℝ³`. -/
noncomputable def emb : Mfd → E3 :=
  Sum.elim (line b0 d0) (Sum.elim (line b1 d1) (line b2 d2))

lemma line0_ne_line1 (s t : E1) : line b0 d0 s ≠ line b1 d1 t := by
  intro h
  have h1 : (line b0 d0 s) 2 = (line b1 d1 t) 2 := by rw [h]
  rw [(line0_coord s).2.2, (line1_coord t).2.2] at h1
  norm_num at h1

lemma line0_ne_line2 (s t : E1) : line b0 d0 s ≠ line b2 d2 t := by
  intro h
  have h1 : (line b0 d0 s) 1 = (line b2 d2 t) 1 := by rw [h]
  rw [(line0_coord s).2.1, (line2_coord t).2.1] at h1
  norm_num at h1

lemma line1_ne_line2 (s t : E1) : line b1 d1 s ≠ line b2 d2 t := by
  intro h
  have h1 : (line b1 d1 s) 0 = (line b2 d2 t) 0 := by rw [h]
  rw [(line1_coord s).1, (line2_coord t).1] at h1
  norm_num at h1

lemma injective_emb : Injective emb := by
  rintro (s | s | s) (t | t | t) h <;>
    simp only [emb, Sum.elim_inl, Sum.elim_inr] at h
  · exact congrArg Sum.inl (injective_line _ _ norm_d0 h)
  · exact absurd h (line0_ne_line1 s t)
  · exact absurd h (line0_ne_line2 s t)
  · exact absurd h.symm (line0_ne_line1 t s)
  · exact congrArg (fun z => Sum.inr (Sum.inl z)) (injective_line _ _ norm_d1 h)
  · exact absurd h (line1_ne_line2 s t)
  · exact absurd h.symm (line0_ne_line2 t s)
  · exact absurd h.symm (line1_ne_line2 t s)
  · exact congrArg (fun z => Sum.inr (Sum.inr z)) (injective_line _ _ norm_d2 h)

lemma isClosedEmbedding_emb : IsClosedEmbedding emb := by
  refine IsClosedEmbedding.sumElim (isClosedEmbedding_line _ _ norm_d0) ?_ injective_emb
  refine IsClosedEmbedding.sumElim (isClosedEmbedding_line _ _ norm_d1)
    (isClosedEmbedding_line _ _ norm_d2) ?_
  intro s t h
  have := injective_emb (a₁ := Sum.inr s) (a₂ := Sum.inr t) (by simpa [emb] using h)
  simpa using this

lemma contMDiff_emb : ContMDiff (𝓡 1) (𝓡 3) ∞ emb :=
  ContMDiff.sumElim (contMDiff_line _ _) (ContMDiff.sumElim (contMDiff_line _ _)
    (contMDiff_line _ _))

/-- The differential of a map on a disjoint union, computed on the left summand. -/
lemma mfderiv_sum_inl {A : Type*} [TopologicalSpace A] [ChartedSpace E1 A]
    [IsManifold (𝓡 1) ∞ A] {B : Type*} [TopologicalSpace B] [ChartedSpace E1 B]
    [IsManifold (𝓡 1) ∞ B] {f : A ⊕ B → E3} (hf : ContMDiff (𝓡 1) (𝓡 3) ∞ f) (x : A) :
    mfderiv (𝓡 1) (𝓡 3) (f ∘ Sum.inl) x = mfderiv (𝓡 1) (𝓡 3) f (Sum.inl x) := by
  have h1 : HasMFDerivAt (𝓡 1) (𝓡 3) f (Sum.inl x) (mfderiv (𝓡 1) (𝓡 3) f (Sum.inl x)) :=
    ((hf (Sum.inl x)).mdifferentiableAt (by simp)).hasMFDerivAt
  have h2 : HasMFDerivAt (𝓡 1) (𝓡 1) (Sum.inl : A → A ⊕ B) x
      (ContinuousLinearMap.id ℝ (TangentSpace (𝓡 1) x)) := hasMFDerivAt_inl (p := Sum.inl x)
  exact (h1.comp x h2).mfderiv

/-- The differential of a map on a disjoint union, computed on the right summand. -/
lemma mfderiv_sum_inr {A : Type*} [TopologicalSpace A] [ChartedSpace E1 A]
    [IsManifold (𝓡 1) ∞ A] {B : Type*} [TopologicalSpace B] [ChartedSpace E1 B]
    [IsManifold (𝓡 1) ∞ B] {f : A ⊕ B → E3} (hf : ContMDiff (𝓡 1) (𝓡 3) ∞ f) (x : B) :
    mfderiv (𝓡 1) (𝓡 3) (f ∘ Sum.inr) x = mfderiv (𝓡 1) (𝓡 3) f (Sum.inr x) := by
  have h1 : HasMFDerivAt (𝓡 1) (𝓡 3) f (Sum.inr x) (mfderiv (𝓡 1) (𝓡 3) f (Sum.inr x)) :=
    ((hf (Sum.inr x)).mdifferentiableAt (by simp)).hasMFDerivAt
  have h2 : HasMFDerivAt (𝓡 1) (𝓡 1) (Sum.inr : B → A ⊕ B) x
      (ContinuousLinearMap.id ℝ (TangentSpace (𝓡 1) x)) := hasMFDerivAt_inr (p := Sum.inr x)
  exact (h1.comp x h2).mfderiv

lemma injective_mfderiv_emb (x : Mfd) :
    Injective (mfderiv (𝓡 1) (𝓡 3) emb x) := by
  rcases x with s | s | s
  · rw [← mfderiv_sum_inl contMDiff_emb s]
    exact injective_mfderiv_line _ _ d0_ne_zero s
  · rw [← mfderiv_sum_inr contMDiff_emb (Sum.inl s)]
    have h : (emb ∘ Sum.inr) ∘ Sum.inl = line b1 d1 := rfl
    rw [← mfderiv_sum_inl (f := emb ∘ Sum.inr)
      (ContMDiff.sumElim (contMDiff_line _ _) (contMDiff_line _ _)) s, h]
    exact injective_mfderiv_line _ _ d1_ne_zero s
  · rw [← mfderiv_sum_inr contMDiff_emb (Sum.inr s)]
    have h : (emb ∘ Sum.inr) ∘ Sum.inr = line b2 d2 := rfl
    rw [← mfderiv_sum_inr (f := emb ∘ Sum.inr)
      (ContMDiff.sumElim (contMDiff_line _ _) (contMDiff_line _ _)) s, h]
    exact injective_mfderiv_line _ _ d2_ne_zero s

/-! ### Every direction is a secant direction -/

lemma exists_secant (v : E3) (hv : v ≠ 0) :
    ∃ p q : Mfd, p ≠ q ∧ ∃ lam : ℝ, emb q - emb p = lam • v := by
  have hex : ∃ i : Fin 3, v i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hv (by ext i; simpa using hc i)
  obtain ⟨i, hi⟩ := hex
  fin_cases i
  · -- v 0 ≠ 0 : use the second and third lines
    refine ⟨(Sum.inr (Sum.inl (EuclideanSpace.single 0 (1 - v 1 / v 0)))),
      (Sum.inr (Sum.inr (EuclideanSpace.single 0 (1 + v 2 / v 0)))), by simp, 1 / v 0, ?_⟩
    have hi : v 0 ≠ 0 := by simpa using hi
    ext j
    fin_cases j <;>
      simp [emb, line, b1, b2, d1, d2, EuclideanSpace.single_apply, PiLp.sub_apply,
        PiLp.smul_apply, PiLp.add_apply] <;> field_simp
  · -- v 1 ≠ 0 : use the first and third lines
    refine ⟨(Sum.inl (EuclideanSpace.single 0 (1 - v 0 / v 1))),
      (Sum.inr (Sum.inr (EuclideanSpace.single 0 (v 2 / v 1)))), by simp, 1 / v 1, ?_⟩
    have hi : v 1 ≠ 0 := by simpa using hi
    ext j
    fin_cases j <;>
      simp [emb, line, b0, b2, d0, d2, EuclideanSpace.single_apply, PiLp.sub_apply,
        PiLp.smul_apply, PiLp.add_apply] <;> field_simp
  · -- v 2 ≠ 0 : use the first and second lines
    refine ⟨(Sum.inl (EuclideanSpace.single 0 (-(v 0) / v 2))),
      (Sum.inr (Sum.inl (EuclideanSpace.single 0 (v 1 / v 2)))), by simp, 1 / v 2, ?_⟩
    have hi : v 2 ≠ 0 := by simpa using hi
    ext j
    fin_cases j <;>
      simp [emb, line, b0, b1, d0, d1, EuclideanSpace.single_apply, PiLp.sub_apply,
        PiLp.smul_apply, PiLp.add_apply] <;> field_simp

lemma not_injective_comp (L : E3 →L[ℝ] E2) : ¬ Injective (L ∘ (emb : Mfd → E3)) := by
  intro hinj
  -- `L` has nontrivial kernel by dimension count
  have hnotinj : ¬ Injective (L : E3 →ₗ[ℝ] E2) := by
    intro h
    have := LinearMap.finrank_le_finrank_of_injective (f := (L : E3 →ₗ[ℝ] E2)) h
    simp at this
  obtain ⟨v, hv0, hv⟩ : ∃ v : E3, v ≠ 0 ∧ L v = 0 := by
    rw [← LinearMap.ker_eq_bot] at hnotinj
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hnotinj
    exact ⟨v, hv0, hv⟩
  obtain ⟨p, q, hpq, lam, hlam⟩ := exists_secant v hv0
  apply hpq
  refine (hinj ?_).symm
  have : L (emb q) - L (emb p) = 0 := by
    rw [← map_sub, hlam, map_smul, hv, smul_zero]
  simpa [Function.comp, sub_eq_zero] using this

end WhitneyProjectionCounterexample

open WhitneyProjectionCounterexample in
theorem solution : ¬ ∀ (n : ℕ), 1 ≤ n →
    ∀ {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
      [IsManifold (𝓡 n) ∞ M] [T2Space M] [SecondCountableTopology M]
      (e : M → EuclideanSpace ℝ (Fin (2 * n + 1))),
      ContMDiff (𝓡 n) (𝓡 (2 * n + 1)) ∞ e → IsClosedEmbedding e →
      (∀ x, Injective (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) e x)) →
    ∃ (L : EuclideanSpace ℝ (Fin (2 * n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n))),
      Function.Surjective L ∧
      let f := L ∘ e
      ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f ∧ Injective f ∧ IsProperMap f ∧
      ∀ x, Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) f x) := by
  intro h
  obtain ⟨L, -, -, hinj, -⟩ :=
    h 1 le_rfl (M := Mfd) emb contMDiff_emb isClosedEmbedding_emb injective_mfderiv_emb
  exact not_injective_comp L hinj
