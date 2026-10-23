-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P75.commonAnnihilator
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:26:07.952466+00:00
-- url     : https://prove2.me/submissions/73de9cba-c06d-4d68-92d6-54fb277e2ab8

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P75
noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

namespace X6P75

open QAlgorithms.Papers.Independent.Information100.P75

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

instance lcs : LocallyConvexSpace ℝ (Matrix ι ι ℂ) :=
  inferInstanceAs (LocallyConvexSpace ℝ (ι → ι → ℂ))

/-- matrix representing a linear functional through the trace pairing -/
def rep (φ : Matrix ι ι ℂ →ₗ[ℂ] ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => φ (Matrix.single j i 1)

lemma rep_spec (φ : Matrix ι ι ℂ →ₗ[ℂ] ℂ) (X : Matrix ι ι ℂ) :
    φ X = (rep φ * X).trace := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum, Matrix.trace, Matrix.diag, Matrix.mul_apply, rep, Matrix.of_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : Matrix.single j i (X j i) = X j i • Matrix.single j i (1 : ℂ) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this, map_smul, smul_eq_mul, mul_comm]

lemma rep_spec' (φ : Matrix ι ι ℂ →ₗ[ℂ] ℂ) (X : Matrix ι ι ℂ) :
    φ X = (X * rep φ).trace := by
  rw [rep_spec, Matrix.trace_mul_comm]

lemma psd_decomp (A : Matrix ι ι ℂ) (hA : A.PosSemidef) :
    ∃ B : Matrix ι ι ℂ, A = Bᴴ * B := by
  open scoped MatrixOrder in
  have h0 : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  open scoped MatrixOrder in
  have hB : (CFC.sqrt A).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  open scoped MatrixOrder in
  have hAB : A = (CFC.sqrt A)ᴴ * CFC.sqrt A := by
    rw [hB.isHermitian.eq, CFC.sqrt_mul_sqrt_self A h0]
  exact ⟨_, hAB⟩

lemma entry_bound (A : Matrix ι ι ℂ) (hA : A.PosSemidef) (i j : ι) :
    ‖A i j‖ ≤ 2 * (A.trace).re := by
  obtain ⟨B, rfl⟩ := psd_decomp A hA
  have hij : (Bᴴ * B) i j = ∑ k, star (B k i) * B k j := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  have htr : ((Bᴴ * B).trace).re = ∑ l, ∑ k, ‖B k l‖ ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.re_sum]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
    norm_cast
  rw [hij, htr, Finset.sum_comm]
  calc ‖∑ k, star (B k i) * B k j‖ ≤ ∑ k, ‖star (B k i) * B k j‖ := norm_sum_le _ _
    _ ≤ ∑ k, (‖B k i‖ ^ 2 + ‖B k j‖ ^ 2) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, norm_star]
        nlinarith [sq_nonneg (‖B k i‖ - ‖B k j‖), norm_nonneg (B k i), norm_nonneg (B k j)]
    _ ≤ ∑ k, (∑ l, ‖B k l‖ ^ 2 + ∑ l, ‖B k l‖ ^ 2) := by
        refine Finset.sum_le_sum fun k _ => add_le_add ?_ ?_
        · exact Finset.single_le_sum (f := fun l => ‖B k l‖ ^ 2)
            (fun l _ => sq_nonneg _) (Finset.mem_univ i)
        · exact Finset.single_le_sum (f := fun l => ‖B k l‖ ^ 2)
            (fun l _ => sq_nonneg _) (Finset.mem_univ j)
    _ = 2 * ∑ k, ∑ l, ‖B k l‖ ^ 2 := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; ring

lemma omega_convex (a : ℝ) : Convex ℝ (omega (ι := ι) a) := by
  rintro R1 ⟨ha0, hapi, P1, Q1, hP1, hQ1, htr1, rfl⟩ R2 ⟨-, -, P2, Q2, hP2, hQ2, htr2, rfl⟩
    s t hs ht hst
  refine ⟨ha0, hapi, s • P1 + t • P2, s • Q1 + t • Q2, (hP1.smul hs).add (hP2.smul ht),
    (hQ1.smul hs).add (hQ2.smul ht), ?_, ?_⟩
  · simp only [Matrix.trace_add, Matrix.trace_smul, Complex.real_smul]
    have : (s : ℂ) + t = 1 := by exact_mod_cast hst
    linear_combination (s : ℂ) * htr1 + (t : ℂ) * htr2 + this
  · simp only [blend, smul_add]
    rw [smul_comm (phase (a / 2)) s P1, smul_comm (phase (a / 2)) t P2,
      smul_comm (phase (-a / 2)) s Q1, smul_comm (phase (-a / 2)) t Q2]
    abel

lemma isClosed_psd : IsClosed {P : Matrix ι ι ℂ | P.PosSemidef} := by
  have : {P : Matrix ι ι ℂ | P.PosSemidef} =
      {P | Pᴴ = P} ∩ ⋂ x : ι → ℂ, {P | 0 ≤ star x ⬝ᵥ (P *ᵥ x)} := by
    ext P
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
      Matrix.posSemidef_iff_dotProduct_mulVec]
    rfl
  rw [this]
  refine IsClosed.inter (isClosed_eq continuous_id.matrix_conjTranspose continuous_id)
    (isClosed_iInter fun x => isClosed_le continuous_const ?_)
  exact continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)

lemma omega_compact (a : ℝ) : IsCompact (omega (ι := ι) a) := by
  by_cases h : 0 ≤ a ∧ a < Real.pi
  · let K : Set (Matrix ι ι ℂ × Matrix ι ι ℂ) :=
      {p | p.1.PosSemidef ∧ p.2.PosSemidef ∧ p.1.trace + p.2.trace = 1}
    have hom : omega (ι := ι) a = (fun p : Matrix ι ι ℂ × Matrix ι ι ℂ => blend a p.1 p.2) '' K := by
      ext R
      simp only [omega, Set.mem_setOf_eq, Set.mem_image, K, Prod.exists]
      constructor
      · rintro ⟨-, -, P, Q, hP, hQ, htr, rfl⟩
        exact ⟨P, Q, ⟨hP, hQ, htr⟩, rfl⟩
      · rintro ⟨P, Q, ⟨hP, hQ, htr⟩, rfl⟩
        exact ⟨h.1, h.2, P, Q, hP, hQ, htr, rfl⟩
    rw [hom]
    let Bs : Set (Matrix ι ι ℂ) :=
      Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) 2
    have hBs : IsCompact Bs :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
    have hKc : IsClosed K := by
      refine (isClosed_psd.preimage continuous_fst).inter
        ((isClosed_psd.preimage continuous_snd).inter (isClosed_eq ?_ continuous_const))
      exact continuous_fst.matrix_trace.add continuous_snd.matrix_trace
    have hbd : ∀ P Q : Matrix ι ι ℂ, P.PosSemidef → Q.PosSemidef →
        P.trace + Q.trace = 1 → P ∈ Bs := by
      intro P Q hP hQ htr
      simp only [Bs, Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall,
        dist_zero_right]
      intro i _ j _
      rw [Metric.mem_closedBall, dist_zero_right]
      have h1 := entry_bound P hP i j
      have h2 : 0 ≤ (Q.trace).re := (Complex.nonneg_iff.mp hQ.trace_nonneg).1
      have h3 : (P.trace).re + (Q.trace).re = 1 := by
        have := congrArg Complex.re htr; simpa using this
      linarith
    have hKs : K ⊆ Bs ×ˢ Bs := by
      rintro ⟨P, Q⟩ ⟨hP, hQ, htr⟩
      exact ⟨hbd P Q hP hQ htr, hbd Q P hQ hP (by rw [add_comm]; exact htr)⟩
    refine IsCompact.image ((hBs.prod hBs).of_isClosed_subset hKc hKs) ?_
    simp only [blend]
    fun_prop
  · convert isCompact_empty
    ext R
    simp only [omega, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h1, h2, -⟩
    exact h ⟨h1, h2⟩

theorem main (M : Submodule ℂ (Mat ι)) (a : ℝ) :
    (∃ R ∈ omega (ι := ι) a, ∀ X ∈ M, (R * X).trace = 0) ↔
    (∀ X ∈ M, ∃ R ∈ omega (ι := ι) a, (R * X).trace = 0) := by
  constructor
  · rintro ⟨R, hR, h⟩ X hX
    exact ⟨R, hR, h X hX⟩
  intro H
  by_contra hcon
  -- the annihilator subspace
  let N : Submodule ℂ (Mat ι) :=
    { carrier := {R | ∀ X ∈ M, (R * X).trace = 0}
      add_mem' := by
        intro R S hR hS X hX
        rw [Matrix.add_mul, Matrix.trace_add, hR X hX, hS X hX, add_zero]
      zero_mem' := by intro X _; simp
      smul_mem' := by
        intro c R hR X hX
        rw [Matrix.smul_mul, Matrix.trace_smul, hR X hX, smul_zero] }
  have hNmem : ∀ R, R ∈ N ↔ ∀ X ∈ M, (R * X).trace = 0 := fun R => Iff.rfl
  have hNclosed : IsClosed (N : Set (Mat ι)) := by
    have : (N : Set (Mat ι)) = ⋂ X ∈ M, {R : Mat ι | (R * X).trace = 0} := by
      ext R; simp [hNmem]
    rw [this]
    refine isClosed_biInter fun X _ => isClosed_eq ?_ continuous_const
    exact (continuous_id.matrix_mul continuous_const).matrix_trace
  have hNconvex : Convex ℝ (N : Set (Mat ι)) := (N.restrictScalars ℝ).convex
  have hdisj : Disjoint (omega (ι := ι) a) (N : Set (Mat ι)) := by
    rw [Set.disjoint_left]
    intro R hR hRN
    exact hcon ⟨R, hR, (hNmem R).1 hRN⟩
  obtain ⟨f, u, v, hfu, huv, hfv⟩ :=
    RCLike.geometric_hahn_banach_compact_closed (𝕜 := ℂ) (omega_convex a) (omega_compact a)
      hNconvex hNclosed hdisj
  -- f vanishes on N
  have hfN : ∀ n ∈ N, f n = 0 := by
    have hv0 : v < 0 := by simpa using hfv 0 N.zero_mem
    have hre : ∀ n ∈ N, (f n).re = 0 := by
      intro n hn
      by_contra hne
      have key : ∀ t : ℝ, v < t * (f n).re := by
        intro t
        have := hfv ((t : ℂ) • n) (N.smul_mem _ hn)
        simpa [map_smul] using this
      rcases lt_or_gt_of_ne hne with h | h
      · have := key ((v - 1) / (f n).re)
        rw [div_mul_cancel₀ _ hne] at this; linarith
      · have := key ((v - 1) / (f n).re)
        rw [div_mul_cancel₀ _ hne] at this; linarith
    intro n hn
    apply Complex.ext
    · exact hre n hn
    · have := hre (Complex.I • n) (N.smul_mem _ hn)
      simpa [map_smul] using this
  -- representing matrix
  set X0 := rep (f : Mat ι →L[ℂ] ℂ).toLinearMap with hX0
  have hX0M : X0 ∈ M := by
    rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff M X0]
    intro φ hφ
    rw [Submodule.mem_dualAnnihilator] at hφ
    have hRφ : rep φ ∈ N := by
      intro X hX
      rw [← rep_spec]; exact hφ X hX
    have h1 := hfN _ hRφ
    have h2 : f (rep φ) = (rep φ * X0).trace := rep_spec' (f : Mat ι →L[ℂ] ℂ).toLinearMap _
    rw [rep_spec φ X0, ← h2, h1]
  obtain ⟨R, hR, hRX⟩ := H X0 hX0M
  have h3 : f R = (R * X0).trace := rep_spec' (f : Mat ι →L[ℂ] ℂ).toLinearMap _
  have h4 := hfu R hR
  have hv0 : v < 0 := by simpa using hfv 0 N.zero_mem
  rw [h3, hRX] at h4
  simp at h4
  linarith

end X6P75

open QAlgorithms.Papers.Independent.Information100.P75 in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Submodule ℂ (Mat ι)) (a : ℝ) (ha : 0 ≤ a) (hap : a < Real.pi) :
    (∃ R ∈ omega (ι := ι) a, ∀ X ∈ M, (R * X).trace = 0) ↔
    (∀ X ∈ M, ∃ R ∈ omega (ι := ι) a, (R * X).trace = 0) :=
  X6P75.main M a
