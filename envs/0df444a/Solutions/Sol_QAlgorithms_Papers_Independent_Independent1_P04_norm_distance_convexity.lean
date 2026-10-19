-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P04.norm_distance_convexity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:33:57.909573+00:00
-- url     : https://prove2.me/submissions/606cf7c9-ebd1-46fb-870b-7c505bcf8ef3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BasisCoherence
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P04_Model
set_option autoImplicit false

/-! Quantifying Coherence, arXiv:1311.0275v3. Fixed bases and arbitrary finite dimensions.
Local predicates apply to density matrices only; invalid matrices carry no coherence guarantees. -/

noncomputable section

open scoped Matrix ComplexOrder

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Independent1 QAlgorithms.Papers.Independent.Independent1.P04
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- PDF p.3 following (7): every genuine matrix norm yields an attained convex candidate. -/
theorem gk_cand_eq {d : ℕ} (D : CoherenceMatrix d → CoherenceMatrix d → ℝ)
    (rho delta : CoherenceMatrix d) (hdelta : IncoherentState delta)
    (hmin : ∀ sigma, IncoherentState sigma → D rho delta ≤ D rho sigma) :
    distanceCandidate D rho = D rho delta := by
  apply le_antisymm
  · apply csInf_le
    · refine ⟨D rho delta, ?_⟩
      rintro v ⟨s, hs, rfl⟩
      exact hmin s hs
    · exact ⟨_, hdelta, rfl⟩
  · refine le_csInf ⟨D rho delta, delta, hdelta, rfl⟩ ?_
    rintro v ⟨s, hs, rfl⟩
    exact hmin s hs

theorem gk_cand_le {d : ℕ} (D : CoherenceMatrix d → CoherenceMatrix d → ℝ)
    (rho delta : CoherenceMatrix d) (hdelta : IncoherentState delta)
    (hb : ∀ sigma, IncoherentState sigma → 0 ≤ D rho sigma) :
    distanceCandidate D rho ≤ D rho delta := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro v ⟨s, hs, rfl⟩
    exact hb s hs
  · exact ⟨_, hdelta, rfl⟩

theorem gk_mix_density {d a : ℕ} (p : Fin a → ℝ) (rho : Fin a → CoherenceMatrix d)
    (hp : Learning.IsDistribution p) (hr : ∀ i, IsDensityMatrix (rho i)) :
    IsDensityMatrix (ensembleMixture p rho) := by
  refine ⟨?_, ?_⟩
  · unfold ensembleMixture
    exact Matrix.posSemidef_sum _ (fun i _ =>
      (hr i).1.smul (by exact_mod_cast hp.1 i))
  · unfold ensembleMixture
    rw [Matrix.trace_sum]
    simp_rw [Matrix.trace_smul, (hr _).2, smul_eq_mul, mul_one]
    exact_mod_cast hp.2

theorem gk_mix_inc {d a : ℕ} (p : Fin a → ℝ) (rho : Fin a → CoherenceMatrix d)
    (hp : Learning.IsDistribution p) (hr : ∀ i, IncoherentState (rho i)) :
    IncoherentState (ensembleMixture p rho) := by
  refine ⟨gk_mix_density p rho hp (fun i => (hr i).1), ?_⟩
  intro i j hij
  unfold ensembleMixture
  rw [Matrix.sum_apply]
  exact Finset.sum_eq_zero (fun k _ => by simp [(hr k).2 i j hij])

theorem gk_jc (D : (d : ℕ) → CoherenceMatrix d → CoherenceMatrix d → ℝ)
    (hD : DistanceMinimumDomain D) (hattain : DistanceAttainment D)
    (hconvex : DistanceJointConvex D) :
    CoherenceConvex (fun d => distanceCandidate (D d)) ∧
    ∀ d, 0 < d → ∀ a (p : Fin a → ℝ) (rho : Fin a → CoherenceMatrix d),
      Learning.IsDistribution p → (∀ i, IsDensityMatrix (rho i)) →
      ∃ sigma : Fin a → CoherenceMatrix d,
        (∀ i, IncoherentState (sigma i) ∧
          distanceCandidate (D d) (rho i) = D d (rho i) (sigma i)) ∧
        distanceCandidate (D d) (ensembleMixture p rho) ≤
          D d (ensembleMixture p rho) (ensembleMixture p sigma) ∧
        D d (ensembleMixture p rho) (ensembleMixture p sigma) ≤
          (∑ i, p i * D d (rho i) (sigma i)) ∧
        (∑ i, p i * D d (rho i) (sigma i)) =
          ∑ i, p i * distanceCandidate (D d) (rho i) := by
  have key : ∀ d, 0 < d → ∀ a (p : Fin a → ℝ) (rho : Fin a → CoherenceMatrix d),
      Learning.IsDistribution p → (∀ i, IsDensityMatrix (rho i)) →
      ∃ sigma : Fin a → CoherenceMatrix d,
        (∀ i, IncoherentState (sigma i) ∧
          distanceCandidate (D d) (rho i) = D d (rho i) (sigma i)) ∧
        distanceCandidate (D d) (ensembleMixture p rho) ≤
          D d (ensembleMixture p rho) (ensembleMixture p sigma) ∧
        D d (ensembleMixture p rho) (ensembleMixture p sigma) ≤
          (∑ i, p i * D d (rho i) (sigma i)) ∧
        (∑ i, p i * D d (rho i) (sigma i)) =
          ∑ i, p i * distanceCandidate (D d) (rho i) := by
    intro d hd a p rho hp hr
    have := fun i => hattain d hd (rho i) (hr i)
    choose sigma hs hmin using this
    have heq : ∀ i, distanceCandidate (D d) (rho i) = D d (rho i) (sigma i) :=
      fun i => gk_cand_eq _ _ _ (hs i) (hmin i)
    have hmr := gk_mix_density p rho hp hr
    refine ⟨sigma, fun i => ⟨hs i, heq i⟩, ?_, ?_, ?_⟩
    · exact gk_cand_le _ _ _ (gk_mix_inc p sigma hp hs)
        (fun s hs' => hD d hd _ _ hmr hs'.1)
    · exact hconvex d hd a p rho sigma hp hr (fun i => (hs i).1)
    · simp_rw [heq]
  refine ⟨?_, key⟩
  intro d hd a p rho hp hr
  obtain ⟨sigma, h1, h2, h3, h4⟩ := key d hd a p rho hp hr
  show distanceCandidate (D d) (ensembleMixture p rho) ≤
    ∑ i, p i * distanceCandidate (D d) (rho i)
  linarith

theorem gk_N_neg {d : ℕ} (N : CoherenceMatrixNorm d) (X : CoherenceMatrix d) :
    N.value (-X) = N.value X := by
  have := N.homogeneous (-1) X
  rw [neg_one_smul] at this
  rw [this]; simp

theorem gk_N_sum {d : ℕ} (N : CoherenceMatrixNorm d) {ι : Type*} (s : Finset ι)
    (f : ι → CoherenceMatrix d) : N.value (∑ i ∈ s, f i) ≤ ∑ i ∈ s, N.value (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [(N.definite 0).2 rfl]
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    exact (N.triangle _ _).trans (by linarith)

theorem gk_N_diag {d : ℕ} (N : CoherenceMatrixNorm d) (v : Fin d → ℝ) :
    N.value (Matrix.diagonal (fun i => (v i : ℂ))) ≤
      ∑ i, |v i| * N.value (Matrix.single i i 1) := by
  have e : Matrix.diagonal (fun i => (v i : ℂ)) = ∑ i, (v i : ℂ) • Matrix.single i i 1 := by
    ext a b
    rw [Matrix.sum_apply]
    by_cases h : a = b
    · subst h; simp [Matrix.single_apply]
    · rw [Matrix.diagonal_apply_ne _ h]
      symm; apply Finset.sum_eq_zero; intro c _
      simp only [Matrix.smul_apply, Matrix.single_apply]
      split_ifs with hc
      · exact absurd (hc.1.symm.trans hc.2) h
      · simp
  rw [e]
  refine (gk_N_sum N _ _).trans (le_of_eq ?_)
  apply Finset.sum_congr rfl
  intro i _
  rw [N.homogeneous, Complex.norm_real, Real.norm_eq_abs]

theorem gk_attain {d : ℕ} (hd : 0 < d) (N : CoherenceMatrixNorm d) (rho : CoherenceMatrix d) :
    AttainedIncoherentMinimum (fun X Y => N.value (X - Y)) rho := by
  set g : (Fin d → ℝ) → ℝ := fun p => N.value (rho - Matrix.diagonal (fun i => (p i : ℂ)))
  set K : ℝ := ∑ i, N.value (Matrix.single i i (1 : ℂ))
  have hK0 : 0 ≤ K := Finset.sum_nonneg (fun i _ => N.nonnegative _)
  have hlip : ∀ p q, g p ≤ g q + K * dist p q := by
    intro p q
    have e : rho - Matrix.diagonal (fun i => (p i : ℂ)) =
        (rho - Matrix.diagonal (fun i => (q i : ℂ))) +
          Matrix.diagonal (fun i => ((q i - p i : ℝ) : ℂ)) := by
      ext a b
      by_cases h : a = b
      · subst h; simp; try ring
      · simp [Matrix.diagonal_apply_ne _ h]
    have h1 : g p ≤ g q + N.value (Matrix.diagonal (fun i => ((q i - p i : ℝ) : ℂ))) := by
      show N.value _ ≤ _
      rw [e]; exact N.triangle _ _
    have h2 := gk_N_diag N (fun i => q i - p i)
    have h3 : ∑ i, |q i - p i| * N.value (Matrix.single i i (1:ℂ)) ≤ K * dist p q := by
      have : K * dist p q = ∑ i, N.value (Matrix.single i i (1:ℂ)) * dist p q := by
        simp only [K, Finset.sum_mul]
      rw [this]
      apply Finset.sum_le_sum
      intro i _
      rw [mul_comm (N.value _)]
      apply mul_le_mul_of_nonneg_right _ (N.nonnegative _)
      rw [← Real.dist_eq, dist_comm]
      exact dist_le_pi_dist p q i
    linarith
  have hcont : Continuous g := by
    apply LipschitzWith.continuous (K := K.toNNReal)
    apply LipschitzWith.of_dist_le_mul
    intro p q
    rw [Real.coe_toNNReal _ hK0]
    rw [Real.dist_eq, abs_le]
    have := hlip p q
    have := hlip q p
    rw [dist_comm q p] at this
    constructor <;> linarith
  have hne : (stdSimplex ℝ (Fin d)).Nonempty := ⟨fun i => if i = ⟨0, hd⟩ then 1 else 0, by
    refine ⟨fun i => by dsimp only; split_ifs <;> norm_num, ?_⟩
    simp⟩
  obtain ⟨p, hp, hmin⟩ := (isCompact_stdSimplex ℝ (Fin d)).exists_isMinOn hne hcont.continuousOn
  have hinc : ∀ q ∈ stdSimplex ℝ (Fin d),
      IncoherentState (Matrix.diagonal (fun i => (q i : ℂ))) := by
    intro q hq
    refine ⟨⟨Matrix.PosSemidef.diagonal (fun i => by simp only [Pi.zero_apply]; exact_mod_cast hq.1 i), ?_⟩, ?_⟩
    · rw [Matrix.trace_diagonal]; exact_mod_cast hq.2
    · intro i j h; simp [Matrix.diagonal_apply_ne _ h]
  refine ⟨_, hinc p hp, fun sigma hs => ?_⟩
  have hsd : sigma = Matrix.diagonal (fun i => (((sigma i i).re : ℝ) : ℂ)) := by
    ext a b
    by_cases h : a = b
    · subst h
      have := hs.1.1.diag_nonneg (i := a)
      rw [Complex.nonneg_iff] at this
      simp only [Matrix.diagonal_apply_eq]
      exact Complex.ext (by simp) (by simp [this.2.symm])
    · rw [hs.2 a b h, Matrix.diagonal_apply_ne _ h]
  have hq : (fun i => (sigma i i).re) ∈ stdSimplex ℝ (Fin d) := by
    refine ⟨fun i => ?_, ?_⟩
    · have := hs.1.1.diag_nonneg (i := i)
      exact (Complex.nonneg_iff.1 this).1
    · have := congrArg Complex.re hs.1.2
      simpa [Matrix.trace, Complex.re_sum] using this
  have := hmin hq
  simp only [Set.mem_setOf_eq] at this
  show g p ≤ N.value (rho - sigma)
  rw [hsd]; exact this

theorem solution (N : (d : ℕ) → CoherenceMatrixNorm d) :
    (∀ d, 0 < d → ∀ rho, IsDensityMatrix rho →
      AttainedCandidateSpec (fun X Y => (N d).value (X-Y)) rho) ∧
    CoherenceConvex (fun d => distanceCandidate (fun X Y => (N d).value (X-Y))) := by
  have hatt : ∀ d, 0 < d → ∀ rho, IsDensityMatrix rho →
      AttainedIncoherentMinimum (fun X Y => (N d).value (X-Y)) rho :=
    fun d hd rho _ => gk_attain hd (N d) rho
  refine ⟨?_, ?_⟩
  · intro d hd rho hrho
    obtain ⟨delta, hdelta, hmin⟩ := hatt d hd rho hrho
    have he := gk_cand_eq (fun X Y => (N d).value (X-Y)) rho delta hdelta hmin
    exact ⟨delta, hdelta, he, fun s hs => he ▸ hmin s hs⟩
  · have hD : DistanceMinimumDomain (fun d X Y => (N d).value (X-Y)) :=
      fun d _ _ _ _ _ => (N d).nonnegative _
    have hJ : DistanceJointConvex (fun d X Y => (N d).value (X-Y)) := by
      intro d hd a p rho sigma hp _ _
      have e : ensembleMixture p rho - ensembleMixture p sigma =
          ∑ i, (p i : ℂ) • (rho i - sigma i) := by
        unfold ensembleMixture
        rw [← Finset.sum_sub_distrib]
        simp [smul_sub]
      show (N d).value (ensembleMixture p rho - ensembleMixture p sigma) ≤ _
      rw [e]
      refine (gk_N_sum _ _ _).trans (le_of_eq ?_)
      apply Finset.sum_congr rfl
      intro i _
      rw [(N d).homogeneous, Complex.norm_real, Real.norm_of_nonneg (hp.1 i)]
    exact (gk_jc _ hD hatt hJ).1

