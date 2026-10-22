-- Prove2me | solution 1 for RobustRegLasso.Sparsity.theorem_5_prime_first_display
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:29:20.26901+00:00
-- url     : https://prove2.me/submissions/e7b4012c-9c01-4d6c-8798-ef386cce3a61

import Mathlib
import Definitions.Def_RobustRegLasso_Sparsity_Basic

set_option autoImplicit false
open RobustRegLasso.Sparsity

theorem rrs_matVec_congr {n m : ℕ} (a a' δ δ' : Fin m → EuclideanSpace ℝ (Fin n)) (x : Fin m → ℝ)
    (h : ∀ i, x i = 0 ∨ a i + δ i = a' i + δ' i) :
    RobustRegLasso.FeatureWise.matVec (a + δ) x = RobustRegLasso.FeatureWise.matVec (a' + δ') x := by
  unfold RobustRegLasso.FeatureWise.matVec
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases h i with h0 | h1
  · simp [h0]
  · simpa using congrArg (fun v => x i • v) h1

theorem rrs_residual_congr {n m : ℕ} (a a' δ δ' : Fin m → EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (x : Fin m → ℝ)
    (h : ∀ i, x i = 0 ∨ a i + δ i = a' i + δ' i) :
    RobustRegLasso.Sparsity.residual a δ b x = RobustRegLasso.Sparsity.residual a' δ' b x := by
  unfold RobustRegLasso.Sparsity.residual
  rw [rrs_matVec_congr a a' δ δ' x h]

theorem rrs_le {n m : ℕ} (a a' : Fin m → EuclideanSpace ℝ (Fin n)) (b : EuclideanSpace ℝ (Fin n))
    (V W : Set (Fin m → EuclideanSpace ℝ (Fin n))) (x y : Fin m → ℝ)
    (h : ∀ δ ∈ V, ∃ δ' ∈ W, RobustRegLasso.Sparsity.residual a δ b x ≤ RobustRegLasso.Sparsity.residual a' δ' b y) :
    robustObjective a b V x ≤ robustObjective a' b W y := by
  unfold robustObjective
  refine iSup₂_le fun δ hδ => ?_
  obtain ⟨δ', hδ', hle⟩ := h δ hδ
  exact (EReal.coe_le_coe_iff.mpr hle).trans
    (le_iSup₂ (f := fun δ' (_ : δ' ∈ W) => ((RobustRegLasso.Sparsity.residual a' δ' b y : ℝ) : EReal)) δ' hδ')

theorem rrs_swap {n m : ℕ} (a a' : Fin m → EuclideanSpace ℝ (Fin n)) (b : EuclideanSpace ℝ (Fin n))
    (V : Set (Fin m → EuclideanSpace ℝ (Fin n))) (I : Finset (Fin m)) (x : Fin m → ℝ)
    (hx : ∀ j, j ∉ I → x j = 0) (ha : ∀ i, i ∈ I → a' i = a i) :
    robustObjective a b V x = robustObjective a' b V x := by
  apply le_antisymm
  · refine rrs_le a a' b V V x x fun δ hδ => ⟨δ, hδ, le_of_eq ?_⟩
    refine rrs_residual_congr a a' δ δ b x fun i => ?_
    by_cases hi : i ∈ I
    · right; rw [ha i hi]
    · left; exact hx i hi
  · refine rrs_le a' a b V V x x fun δ hδ => ⟨δ, hδ, le_of_eq ?_⟩
    refine rrs_residual_congr a' a δ δ b x fun i => ?_
    by_cases hi : i ∈ I
    · right; rw [ha i hi]
    · left; exact hx i hi

theorem rrs_enlarge {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : EuclideanSpace ℝ (Fin n))
    (c l : Fin m → ℝ) (hc : ∀ i, 0 ≤ c i) (I : Finset (Fin m)) (hl : ∀ j, j ∉ I → 0 ≤ l j) (x : Fin m → ℝ)
    (hx : ∀ j, j ∉ I → x j = 0) :
    robustObjective a b (enlargedSet c l I) x =
      robustObjective a b (RobustRegLasso.FeatureWise.uncertaintySet c) x := by
  apply le_antisymm
  · refine rrs_le a a b _ _ x x fun δ hδ => ⟨restrict I δ, ?_, le_of_eq ?_⟩
    · intro i
      by_cases hi : i ∈ I
      · simpa [restrict, hi] using hδ.1 i hi
      · simpa [restrict, hi] using hc i
    · refine rrs_residual_congr a a δ (restrict I δ) b x fun i => ?_
      by_cases hi : i ∈ I
      · right; simp [restrict, hi]
      · left; exact hx i hi
  · refine rrs_le a a b _ _ x x fun δ hδ => ⟨δ, ?_, le_refl _⟩
    refine ⟨fun i _ => hδ i, fun j hj => ?_⟩
    linarith [hδ j, hl j hj]

theorem rrs_incl {n m : ℕ} (a aTilde : Fin m → EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (c l : Fin m → ℝ) (I : Finset (Fin m))
    (hl : ∀ j, j ∉ I → ‖a j - aTilde j‖ ≤ l j) (hI : ∀ i, i ∈ I → a i = aTilde i) :
    {M | ∃ δ ∈ (RobustRegLasso.FeatureWise.uncertaintySet c : Set (Fin m → EuclideanSpace ℝ (Fin n))), M = a + δ} ⊆
      {M | ∃ δ ∈ (enlargedSet c l I : Set (Fin m → EuclideanSpace ℝ (Fin n))), M = aTilde + δ} ∧
    ∀ x' : Fin m → ℝ, robustObjective a b (RobustRegLasso.FeatureWise.uncertaintySet c) x' ≤
      robustObjective aTilde b (enlargedSet c l I) x' := by
  have key : ∀ δ ∈ (RobustRegLasso.FeatureWise.uncertaintySet c : Set (Fin m → EuclideanSpace ℝ (Fin n))),
      a + δ - aTilde ∈ (enlargedSet c l I : Set (Fin m → EuclideanSpace ℝ (Fin n))) := by
    intro δ hδ
    refine ⟨fun i hi => ?_, fun j hj => ?_⟩
    · have : (a + δ - aTilde) i = δ i := by simp [hI i hi]
      rw [this]; exact hδ i
    · have : (a + δ - aTilde) j = δ j + (a j - aTilde j) := by simp; abel
      rw [this]
      calc ‖δ j + (a j - aTilde j)‖ ≤ ‖δ j‖ + ‖a j - aTilde j‖ := norm_add_le _ _
        _ ≤ c j + l j := add_le_add (hδ j) (hl j hj)
  refine ⟨?_, fun x' => ?_⟩
  · rintro M ⟨δ, hδ, rfl⟩
    exact ⟨a + δ - aTilde, key δ hδ, by abel⟩
  · refine rrs_le a aTilde b _ _ x' x' fun δ hδ => ⟨a + δ - aTilde, key δ hδ, le_of_eq ?_⟩
    refine rrs_residual_congr a aTilde δ _ b x' fun i => Or.inr ?_
    simp

theorem rrs_first {n m : ℕ} (a aTilde : Fin m → EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (c l : Fin m → ℝ) (hc : ∀ i, 0 ≤ c i)
    (I : Finset (Fin m)) (xStar : Fin m → ℝ) (hx : ∀ j, j ∉ I → xStar j = 0)
    (hl : ∀ j, j ∉ I → ‖aTilde j - a j‖ ≤ l j) (hI : ∀ i, i ∈ I → aTilde i = a i) :
    robustObjective a b (enlargedSet c l I) xStar = robustObjective a b (RobustRegLasso.FeatureWise.uncertaintySet c) xStar ∧
    robustObjective a b (RobustRegLasso.FeatureWise.uncertaintySet c) xStar =
      robustObjective aTilde b (RobustRegLasso.FeatureWise.uncertaintySet c) xStar ∧
    robustObjective aTilde b (enlargedSet c l I) xStar =
      robustObjective a b (RobustRegLasso.FeatureWise.uncertaintySet c) xStar := by
  have hl0 : ∀ j, j ∉ I → 0 ≤ l j := fun j hj => le_trans (norm_nonneg _) (hl j hj)
  have hswap : ∀ V : Set (Fin m → EuclideanSpace ℝ (Fin n)),
      robustObjective a b V xStar = robustObjective aTilde b V xStar :=
    fun V => rrs_swap a aTilde b V I xStar hx hI
  refine ⟨rrs_enlarge a b c l hc I hl0 xStar hx, hswap _, ?_⟩
  exact (hswap _).symm.trans (rrs_enlarge a b c l hc I hl0 xStar hx)

theorem rrs_prime {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (c l : Fin m → ℝ) (hc : ∀ i, 0 ≤ c i)
    (xStar : Fin m → ℝ) (hopt : IsRobustSolution a b (RobustRegLasso.FeatureWise.uncertaintySet c) xStar)
    (I : Finset (Fin m)) (hx : ∀ j, j ∉ I → xStar j = 0) :
    ∀ aTilde : Fin m → EuclideanSpace ℝ (Fin n),
      (∀ j, j ∉ I → ‖aTilde j - a j‖ ≤ l j) → (∀ i, i ∈ I → aTilde i = a i) →
      IsRobustSolution aTilde b (enlargedSet c l I) xStar := by
  intro aTilde hl hI y
  have h3 := (rrs_first a aTilde b c l hc I xStar hx hl hI).2.2
  have hinc := (rrs_incl a aTilde b c l I (fun j hj => by rw [norm_sub_rev]; exact hl j hj)
    (fun i hi => (hI i hi).symm)).2 y
  rw [h3]
  exact (hopt y).trans hinc

theorem rrs_sparse {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (c : Fin m → ℝ) (hc : ∀ i, 0 ≤ c i) (I : Finset (Fin m))
    (h : ∃ δTilde ∈ (RobustRegLasso.FeatureWise.uncertaintySet c : Set (Fin m → EuclideanSpace ℝ (Fin n))),
      (∀ i, i ∈ I → δTilde i = 0) ∧
      HasSolutionSupportedOn (a + δTilde) b (restrictedSet c I) I) :
    HasSolutionSupportedOn a b (RobustRegLasso.FeatureWise.uncertaintySet c) I := by
  obtain ⟨δT, hδT, hδT0, x, hxopt, hxsupp⟩ := h
  refine ⟨x, fun y => ?_, hxsupp⟩
  -- (1) value at x
  have h1 : robustObjective a b (RobustRegLasso.FeatureWise.uncertaintySet c) x ≤
      robustObjective (a + δT) b (restrictedSet c I) x := by
    refine rrs_le a (a + δT) b _ _ x x fun δ hδ => ⟨restrict I δ, ⟨δ, hδ, rfl⟩, le_of_eq ?_⟩
    refine rrs_residual_congr a (a + δT) δ (restrict I δ) b x fun i => ?_
    by_cases hi : i ∈ I
    · right; simp [restrict, hi, hδT0 i hi]
    · left; exact hxsupp i hi
  -- (2) value everywhere
  have h2 : robustObjective (a + δT) b (restrictedSet c I) y ≤
      robustObjective a b (RobustRegLasso.FeatureWise.uncertaintySet c) y := by
    refine rrs_le (a + δT) a b _ _ y y fun δ' hδ' => ?_
    obtain ⟨δ, hδ, rfl⟩ := hδ'
    refine ⟨δT + restrict I δ, ?_, le_of_eq ?_⟩
    · intro i
      by_cases hi : i ∈ I
      · simpa [restrict, hi, hδT0 i hi] using hδ i
      · simpa [restrict, hi] using hδT i
    · refine rrs_residual_congr (a + δT) a (restrict I δ) (δT + restrict I δ) b y fun i => Or.inr ?_
      simp [add_assoc]
  exact h1.trans ((hxopt y).trans h2)

theorem solution {n m : ℕ} (a aTilde : Fin m → EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (c l : Fin m → ℝ) (hc : ∀ i, 0 ≤ c i)
    (I : Finset (Fin m)) (xStar : Fin m → ℝ) (hx : ∀ j, j ∉ I → xStar j = 0)
    (hl : ∀ j, j ∉ I → ‖aTilde j - a j‖ ≤ l j) (hI : ∀ i, i ∈ I → aTilde i = a i) :
    robustObjective a b (enlargedSet c l I) xStar = robustObjective a b (RobustRegLasso.FeatureWise.uncertaintySet c) xStar ∧
    robustObjective a b (RobustRegLasso.FeatureWise.uncertaintySet c) xStar =
      robustObjective aTilde b (RobustRegLasso.FeatureWise.uncertaintySet c) xStar ∧
    robustObjective aTilde b (enlargedSet c l I) xStar =
      robustObjective a b (RobustRegLasso.FeatureWise.uncertaintySet c) xStar := rrs_first a aTilde b c l hc I xStar hx hl hI
