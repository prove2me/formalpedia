-- Prove2me | solution 4 for SionMinimax.KKM.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T07:31:16.590513+00:00
-- url     : https://prove2.me/submissions/2c7ed556-022e-4510-8cf0-119cf4aa3ee4

import Mathlib
import Theorems.Thm_Brouwer_exists_fixedPoint_closedBall_contDiff

-- carved verbatim out of submission 818ed08f-1f44-45cc-90a9-3239f8bb6e07, lines 1019-1029

section
open Metric Set MeasureTheory

theorem L3_brouwer_ball_scalar_approx {d : ℕ} (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : ContinuousOn φ (closedBall 0 1)) (η : ℝ) (hη : 0 < η) :
    ∃ G : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ 1 G ∧
      ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, |G x - φ x| < η := by
  set B : Set (EuclideanSpace ℝ (Fin d)) := closedBall 0 1 with hB
  have : CompactSpace B := isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)
  let A : Subalgebra ℝ C(B, ℝ) :=
    { carrier := {g | ∃ G : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ 1 G ∧ ∀ x : B, g x = G x}
      mul_mem' := by
        rintro a b ⟨Ga, hGa, ha⟩ ⟨Gb, hGb, hb⟩
        exact ⟨fun x => Ga x * Gb x, hGa.mul hGb, fun x => by simp [ha, hb]⟩
      add_mem' := by
        rintro a b ⟨Ga, hGa, ha⟩ ⟨Gb, hGb, hb⟩
        exact ⟨fun x => Ga x + Gb x, hGa.add hGb, fun x => by simp [ha, hb]⟩
      algebraMap_mem' := fun r => ⟨fun _ => r, contDiff_const, fun x => by simp⟩ }
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    have : ∃ i, (x : EuclideanSpace ℝ (Fin d)) i ≠ (y : EuclideanSpace ℝ (Fin d)) i := by
      by_contra h
      push Not at h
      apply hxy
      apply Subtype.ext
      ext i
      exact h i
    obtain ⟨i, hi⟩ := this
    refine ⟨fun z : B => (z : EuclideanSpace ℝ (Fin d)) i, ?_, hi⟩
    refine ⟨⟨fun z : B => (z : EuclideanSpace ℝ (Fin d)) i, by fun_prop⟩, ?_, rfl⟩
    exact ⟨fun z => z i, (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).contDiff,
      fun z => rfl⟩
  obtain ⟨g, hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints A hsep
    (fun x : B => φ x) hφ.domRestrict η hη
  obtain ⟨G, hG, hgG⟩ := g.2
  refine ⟨G, hG, fun x hx => ?_⟩
  have := hg ⟨x, hx⟩
  rw [Real.norm_eq_abs] at this
  simpa [hgG] using this

theorem L3_brouwer_ball_vec_approx {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hf : ContinuousOn f (closedBall 0 1)) (δ : ℝ) (hδ : 0 < δ) :
    ∃ G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d), ContDiff ℝ 1 G ∧
      ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, ‖G x - f x‖ < δ := by
  set η : ℝ := δ / (d + 1) with hη_def
  have hd1 : (0 : ℝ) < d + 1 := by positivity
  have hη : 0 < η := div_pos hδ hd1
  have hcoord : ∀ i : Fin d, ∃ Gi : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ 1 Gi ∧
      ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, |Gi x - f x i| < η := by
    intro i
    refine L3_brouwer_ball_scalar_approx (fun x => f x i) ?_ η hη
    exact (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).continuous.comp_continuousOn hf
  choose Gi hGi hGiapprox using hcoord
  refine ⟨fun x => (EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => Gi i x), ?_, ?_⟩
  · exact (EuclideanSpace.equiv (Fin d) ℝ).symm.contDiff.comp (contDiff_pi.2 fun i => hGi i)
  · intro x hx
    set v := (EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => Gi i x) - f x with hv
    have hvi : ∀ i, v i = Gi i x - f x i := by
      intro i
      simp [hv]
    have hsq : ‖v‖ ^ 2 ≤ d * η ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      calc ∑ i, (v i) ^ 2 ≤ ∑ _i : Fin d, η ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            rw [hvi i]
            have := hGiapprox i x hx
            rw [← sq_abs]
            have h0 : 0 ≤ |Gi i x - f x i| := abs_nonneg _
            nlinarith
        _ = d * η ^ 2 := by simp
    have hlt : ‖v‖ ^ 2 < δ ^ 2 := by
      have hδη : δ = (d + 1) * η := by rw [hη_def]; field_simp
      rw [hδη]
      have : (d : ℝ) * η ^ 2 < ((d : ℝ) + 1) ^ 2 * η ^ 2 := by
        have hdd : (d : ℝ) < ((d : ℝ) + 1) ^ 2 := by nlinarith
        have := pow_pos hη 2
        nlinarith
      nlinarith
    have hn : 0 ≤ ‖v‖ := norm_nonneg _
    nlinarith

theorem L3_brouwer_ball {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hf : ContinuousOn f (closedBall 0 1)) (hmaps : MapsTo f (closedBall 0 1) (closedBall 0 1)) :
    ∃ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, f x = x := by
  by_contra hno
  push Not at hno
  -- Step 1: minimal displacement
  have hcpt : IsCompact (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) := isCompact_closedBall 0 1
  have hne : (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1).Nonempty :=
    ⟨0, mem_closedBall_self zero_le_one⟩
  have hcont : ContinuousOn (fun x => ‖f x - x‖) (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    (hf.sub continuousOn_id).norm
  obtain ⟨x₀, hx₀, hmin⟩ := hcpt.exists_isMinOn hne hcont
  set ε : ℝ := ‖f x₀ - x₀‖ with hε_def
  have hε : 0 < ε := norm_pos_iff.2 (sub_ne_zero.2 (hno x₀ hx₀))
  have hεle : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, ε ≤ ‖f x - x‖ :=
    fun x hx => hmin hx
  -- Step 2: smooth approximation
  set η : ℝ := ε / 2 with hη_def
  have hη : 0 < η := half_pos hε
  obtain ⟨G, hG, hGapprox⟩ := L3_brouwer_ball_vec_approx f hf η hη
  -- Step 3: rescale
  set c : ℝ := 1 + η with hc_def
  have hc : 0 < c := by positivity
  set g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun x => c⁻¹ • G x with hg_def
  have hgC1 : ContDiff ℝ 1 g := hG.const_smul c⁻¹
  have hGnorm : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, ‖G x‖ ≤ c := by
    intro x hx
    have h1 : ‖f x‖ ≤ 1 := by simpa using hmaps hx
    have h2 := hGapprox x hx
    calc ‖G x‖ = ‖(G x - f x) + f x‖ := by rw [sub_add_cancel]
      _ ≤ ‖G x - f x‖ + ‖f x‖ := norm_add_le _ _
      _ ≤ c := by rw [hc_def]; linarith
  have hgmaps : MapsTo g (closedBall 0 1) (closedBall 0 1) := by
    intro x hx
    rw [mem_closedBall_zero_iff, hg_def]
    simp only
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hc)]
    calc c⁻¹ * ‖G x‖ ≤ c⁻¹ * c := by
          exact mul_le_mul_of_nonneg_left (hGnorm x hx) (inv_pos.2 hc).le
      _ = 1 := inv_mul_cancel₀ hc.ne'
  have hgf : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, ‖g x - f x‖ < ε := by
    intro x hx
    have h1 : ‖f x‖ ≤ 1 := by simpa using hmaps hx
    have h2 := hGapprox x hx
    have hkey : c • (g x - f x) = (G x - f x) - η • f x := by
      rw [hg_def]
      simp only
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hc.ne', one_smul, hc_def, add_smul, one_smul]
      abel
    have hnorm : c * ‖g x - f x‖ ≤ ‖G x - f x‖ + η * ‖f x‖ := by
      have := congrArg norm hkey
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc] at this
      rw [this]
      calc ‖(G x - f x) - η • f x‖ ≤ ‖G x - f x‖ + ‖η • f x‖ := norm_sub_le _ _
        _ = ‖G x - f x‖ + η * ‖f x‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
    have hc1 : 1 ≤ c := by rw [hc_def]; linarith
    have hn0 : 0 ≤ ‖g x - f x‖ := norm_nonneg _
    have : η * ‖f x‖ ≤ η := by nlinarith
    nlinarith
  obtain ⟨x, hx, hfix⟩ := Brouwer.exists_fixedPoint_closedBall_contDiff g hgC1 hgmaps
  have h1 := hεle x hx
  have h2 := hgf x hx
  rw [hfix, norm_sub_rev] at h2
  linarith

theorem L4_retraction {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {K : Set F} (hne : K.Nonempty) (hc : IsComplete K) (hconv : Convex ℝ K) :
    ∃ p : F → F, Continuous p ∧ (∀ x, p x ∈ K) ∧ (∀ x ∈ K, p x = x) := by
  choose p hpK hpeq using exists_norm_eq_iInf_of_complete_convex hne hc hconv
  have hin : ∀ x, ∀ w ∈ K, inner ℝ (x - p x) (w - p x) ≤ 0 := fun x =>
    (norm_eq_iInf_iff_real_inner_le_zero hconv (hpK x)).1 (hpeq x)
  refine ⟨p, ?_, hpK, ?_⟩
  · have hlip : LipschitzWith 1 p := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      simp only [NNReal.coe_one, one_mul, dist_eq_norm]
      have h1 := hin x (p y) (hpK y)
      have h2 := hin y (p x) (hpK x)
      have key : ‖p x - p y‖ ^ 2 ≤ inner ℝ (x - y) (p x - p y) := by
        have e : inner ℝ (x - y) (p x - p y) - ‖p x - p y‖ ^ 2 =
            -inner ℝ (x - p x) (p y - p x) - inner ℝ (y - p y) (p x - p y) := by
          rw [← real_inner_self_eq_norm_sq]
          simp only [inner_sub_left, inner_sub_right, real_inner_comm]
          ring
        linarith
      have hcs := real_inner_le_norm (x - y) (p x - p y)
      rcases eq_or_lt_of_le (norm_nonneg (p x - p y)) with h | h
      · rw [← h]; exact norm_nonneg _
      · nlinarith
    exact hlip.continuous
  · intro x hx
    have h0 : ‖x - p x‖ ^ 2 ≤ 0 := by
      rw [← real_inner_self_eq_norm_sq]; exact hin x x hx
    have h1 : ‖x - p x‖ = 0 := by nlinarith [norm_nonneg (x - p x)]
    exact (norm_sub_eq_zero_iff.1 h1).symm

theorem L4_brouwer_euclid {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))} (hKconv : Convex ℝ K)
    (hKcpt : IsCompact K) (hKne : K.Nonempty)
    (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hf : ContinuousOn f K)
    (hfK : MapsTo f K K) : ∃ x ∈ K, f x = x := by
  obtain ⟨p, hpc, hpK, hpid⟩ := L4_retraction hKne hKcpt.isComplete hKconv
  obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hKcpt.isBounded
  set R : ℝ := max R₀ 1 with hR
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hKR : K ⊆ closedBall 0 R := hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  let g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun z => R⁻¹ • f (p (R • z))
  have hgc : ContinuousOn g (closedBall 0 1) := by
    have hc : ContinuousOn (fun z => f (p (R • z))) univ :=
      hf.comp (hpc.comp (continuous_const_smul R)).continuousOn (fun z _ => hpK _)
    exact (hc.mono (subset_univ _)).const_smul R⁻¹
  have hgm : MapsTo g (closedBall 0 1) (closedBall 0 1) := by
    intro z _
    have h1 := hKR (hfK (hpK (R • z)))
    rw [mem_closedBall_zero_iff] at h1 ⊢
    simp only [g, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hRpos]
    rw [inv_mul_le_iff₀ hRpos]
    linarith
  obtain ⟨z, -, hz⟩ := L3_brouwer_ball g hgc hgm
  have hx : f (p (R • z)) = R • z := by
    have := congrArg (fun v => R • v) hz
    simpa [g, smul_smul, mul_inv_cancel₀ hRpos.ne'] using this
  have hxK : R • z ∈ K := hx ▸ hfK (hpK _)
  refine ⟨R • z, hxK, ?_⟩
  rw [hpid _ hxK] at hx
  exact hx

theorem brouwer_fixed {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {K : Set E}
    (hKconv : Convex ℝ K) (hKcpt : IsCompact K) (hKne : K.Nonempty)
    (f : E → E) (hf : ContinuousOn f K) (hfK : Set.MapsTo f K K) :
    ∃ x ∈ K, f x = x := by
  classical
  let φ : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  have hconv' : Convex ℝ (φ '' K) :=
    hKconv.linear_image (φ : E →ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
  have hcont : ContinuousOn (φ ∘ f ∘ φ.symm) (φ '' K) := by
    refine φ.continuous.comp_continuousOn (hf.comp φ.symm.continuous.continuousOn ?_)
    rintro _ ⟨y, hy, rfl⟩
    simpa using hy
  have hmaps : MapsTo (φ ∘ f ∘ φ.symm) (φ '' K) (φ '' K) := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨f y, hfK hy, by simp⟩
  obtain ⟨x, ⟨y, hyK, rfl⟩, hx⟩ :=
    L4_brouwer_euclid hconv' (hKcpt.image φ.continuous) (hKne.image φ) _ hcont hmaps
  refine ⟨y, hyK, ?_⟩
  apply φ.injective
  simpa using hx

end

section

open Fin.NatCast in
theorem simplex_core (n : ℕ) (A : Fin (n+1) → Set (Fin (n+1) → ℝ)) (hA : ∀ i, IsOpen (A i))
    (hcov : ∀ x ∈ stdSimplex ℝ (Fin (n+1)), ∃ i, x ∈ A i)
    (hC : ∀ i, Convex ℝ (stdSimplex ℝ (Fin (n+1)) \ A i))
    (hv : ∀ i j, i ≠ j → (Pi.single i 1 : Fin (n+1) → ℝ) ∉ A j) :
    ∃ x ∈ stdSimplex ℝ (Fin (n+1)), ∀ i, x ∈ A i := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨i, hi⟩ := hcov _ (single_mem_stdSimplex ℝ (0 : Fin 1))
    exact ⟨_, single_mem_stdSimplex ℝ (0 : Fin 1), fun j => by
      have hj : j = i := Fin.ext (by have := j.2; have := i.2; omega)
      rw [hj]; exact hi⟩
  have : Nontrivial (Fin (n+1)) := Fin.nontrivial_iff_two_le.2 (by omega)
  -- distance functions
  have hne : ∀ i, ((A i)ᶜ).Nonempty := by
    intro i
    obtain ⟨j, hj⟩ := exists_ne i
    exact ⟨_, hv j i hj⟩
  let φ : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ := fun i x => Metric.infDist x (A i)ᶜ
  have hφc : ∀ i, Continuous (φ i) := fun i => Metric.continuous_infDist_pt _
  have hφpos : ∀ i x, 0 < φ i x ↔ x ∈ A i := by
    intro i x
    have := (hA i).isClosed_compl.notMem_iff_infDist_pos (hne i) (x := x)
    simp only [Set.mem_compl_iff, not_not] at this
    exact this.symm
  have hφnn : ∀ i x, 0 ≤ φ i x := fun i x => Metric.infDist_nonneg
  let S : (Fin (n+1) → ℝ) → ℝ := fun x => ∑ i, φ i x
  have hSpos : ∀ x ∈ stdSimplex ℝ (Fin (n+1)), 0 < S x := by
    intro x hx
    obtain ⟨i, hi⟩ := hcov x hx
    exact lt_of_lt_of_le ((hφpos i x).2 hi)
      (Finset.single_le_sum (fun j _ => hφnn j x) (Finset.mem_univ i))
  let sh : Equiv.Perm (Fin (n+1)) := Equiv.subRight (1 : Fin (n+1))
  let T : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) := fun x i => φ (sh i) x / S x
  have hT : ∀ x ∈ stdSimplex ℝ (Fin (n+1)), T x ∈ stdSimplex ℝ (Fin (n+1)) := by
    intro x hx
    refine ⟨fun i => div_nonneg (hφnn _ _) (hSpos x hx).le, ?_⟩
    simp only [T]
    rw [← Finset.sum_div]
    have : ∑ i, φ (sh i) x = S x := Equiv.sum_comp sh (fun j => φ j x)
    rw [this, div_self (hSpos x hx).ne']
  have hTc : ContinuousOn T (stdSimplex ℝ (Fin (n+1))) := by
    refine continuousOn_pi.2 fun i => ?_
    refine ContinuousOn.div (hφc _).continuousOn ?_ (fun x hx => (hSpos x hx).ne')
    exact (continuous_finsetSum _ fun j _ => hφc j).continuousOn
  obtain ⟨x, hx, hfix⟩ := brouwer_fixed (convex_stdSimplex ℝ (Fin (n+1)))
    (isCompact_stdSimplex ℝ (Fin (n+1))) ⟨_, single_mem_stdSimplex ℝ (0 : Fin (n+1))⟩ T hTc hT
  -- face inclusion
  have hface : ∀ j, x j = 0 → x ∉ A j := by
    intro j hj hxA
    have hmem : x ∈ stdSimplex ℝ (Fin (n+1)) \ A j := by
      have hsum : ∑ k ∈ Finset.univ.erase j, x k = 1 := by
        rw [Finset.sum_erase _ hj]; exact hx.2
      have := (hC j).sum_mem (t := Finset.univ.erase j) (w := x) (z := fun k => (Pi.single k 1 : Fin (n+1) → ℝ))
        (fun k _ => hx.1 k) hsum (fun k hk => ⟨single_mem_stdSimplex ℝ k, hv k j (Finset.ne_of_mem_erase hk)⟩)
      convert this using 1
      funext m
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ j)]
      simp [Pi.single_apply, hj]
    exact hmem.2 hxA
  -- supports
  have hxi : ∀ i, x i = φ (sh i) x / S x := fun i => (congrFun hfix i).symm
  have hJ : ∀ j, x ∈ A j → x ∈ A (sh j) := by
    intro j hj
    have h1 : x j ≠ 0 := fun h => hface j h hj
    have h2 : 0 < x j := lt_of_le_of_ne (hx.1 j) (Ne.symm h1)
    rw [hxi j] at h2
    have := (div_pos_iff_of_pos_right (hSpos x hx)).1 h2
    exact (hφpos _ _).1 this
  have hall : ∀ k : ℕ, ∀ j, x ∈ A j → x ∈ A (j - (k : Fin (n+1))) := by
    intro k
    induction k with
    | zero => intro j hj; simpa using hj
    | succ k ih =>
      intro j hj
      have := hJ _ (ih j hj)
      have e : sh (j - (k : Fin (n+1))) = j - ((k+1 : ℕ) : Fin (n+1)) := by
        simp [sh, Equiv.subRight_apply, Nat.cast_succ, sub_sub]
      rw [e] at this; exact this
  obtain ⟨i0, hi0⟩ := hcov x hx
  refine ⟨x, hx, fun i => ?_⟩
  have := hall (i0 - i).val i0 hi0
  rwa [Fin.cast_val_eq_self, sub_sub_cancel] at this

theorem t31_strong {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (n : ℕ) (a : Fin (n + 1) → E)
    (A : Fin (n + 1) → Set E)
    (hA : ∀ i, IsOpen (A i))
    (hcov : convexHull ℝ (Set.range a) ⊆ ⋃ i, A i)
    (hconv : ∀ i, Convex ℝ (convexHull ℝ (Set.range a) \ A i))
    (hv : ∀ i j, i ≠ j → a i ∉ A j) :
    ∃ z ∈ convexHull ℝ (Set.range a), ∀ i, z ∈ A i := by
  classical
  let ψ : (Fin (n+1) → ℝ) →ₗ[ℝ] E := Fintype.linearCombination ℝ a
  have hψ : ∀ x, ψ x = ∑ i, x i • a i := fun x => by
    simp [ψ, Fintype.linearCombination_apply]
  have hψc : Continuous ψ := by
    have : (ψ : (Fin (n+1) → ℝ) → E) = fun x => ∑ i, x i • a i := funext hψ
    rw [this]
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
  have hψS : ∀ x ∈ stdSimplex ℝ (Fin (n+1)), ψ x ∈ convexHull ℝ (Set.range a) := by
    intro x hx
    rw [hψ]
    exact (convex_convexHull ℝ _).sum_mem (fun i _ => hx.1 i) hx.2
      (fun i _ => subset_convexHull ℝ _ (Set.mem_range_self i))
  obtain ⟨x, hx, hxA⟩ := simplex_core n (fun i => ψ ⁻¹' A i) (fun i => (hA i).preimage hψc)
    (fun x hx => by
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov (hψS x hx))
      exact ⟨i, hi⟩)
    (fun i => by
      have : stdSimplex ℝ (Fin (n+1)) \ ψ ⁻¹' A i
          = stdSimplex ℝ (Fin (n+1)) ∩ (ψ ⁻¹' (convexHull ℝ (Set.range a) \ A i)) := by
        ext x
        simp only [Set.mem_diff, Set.mem_inter_iff, Set.mem_preimage]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, hψS x h1, h2⟩
        · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
      rw [this]
      exact (convex_stdSimplex ℝ (Fin (n+1))).inter ((hconv i).linear_preimage ψ))
    (fun i j hij => by
      have : ψ (Pi.single i 1) = a i := by
        rw [hψ]
        simp [Pi.single_apply]
      simp only [Set.mem_preimage, this]
      exact hv i j hij)
  exact ⟨ψ x, hψS x hx, fun i => hxA i⟩

theorem usc_open {E : Type*} [TopologicalSpace E] (M : Set E) (g : E → ℝ) (c : ℝ)
    (hu : UpperSemicontinuousOn g M) :
    ∃ V : Set E, IsOpen V ∧ ∀ z ∈ M, (z ∈ V ↔ g z < c) := by
  classical
  have h : ∀ z : E, ∃ U : Set E, IsOpen U ∧ (z ∈ M → g z < c → z ∈ U ∧ ∀ x ∈ U, x ∈ M → g x < c) := by
    intro z
    by_cases hz : z ∈ M ∧ g z < c
    · have := hu z hz.1 c hz.2
      obtain ⟨U, hU, hzU, hsub⟩ := mem_nhdsWithin.1 this
      exact ⟨U, hU, fun _ _ => ⟨hzU, fun x hx hxM => hsub ⟨hx, hxM⟩⟩⟩
    · exact ⟨∅, isOpen_empty, fun h1 h2 => (hz ⟨h1, h2⟩).elim⟩
  choose U hUo hU using h
  refine ⟨⋃ z ∈ {z | z ∈ M ∧ g z < c}, U z, isOpen_biUnion fun z _ => hUo z, fun z hz => ?_⟩
  constructor
  · intro hzV
    obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.1 hzV
    exact (hU w hw.1 hw.2).2 z hzw hz
  · intro hlt
    exact Set.mem_iUnion₂.2 ⟨z, ⟨hz, hlt⟩, (hU z hz hlt).1⟩

theorem l33_core {E ι : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (M : Set E) (hM : Convex ℝ M) (hne : M.Nonempty)
    (Y : Finset ι) (f : E → ι → ℝ) (c : ℝ)
    (hq : ∀ y ∈ Y, QuasiconcaveOn ℝ M (fun μ => f μ y))
    (hu : ∀ y ∈ Y, UpperSemicontinuousOn (fun μ => f μ y) M)
    (hP : ∀ μ ∈ M, ∃ y ∈ Y, f μ y < c)
    (hmin : ∀ Y' : Finset ι, Y' ⊂ Y → ¬ ∀ μ ∈ M, ∃ y ∈ Y', f μ y < c) :
    ∃ μ₀ ∈ M, ∀ y ∈ Y, f μ₀ y < c := by
  classical
  obtain ⟨m0, hm0⟩ := hne
  have hYne : Y.Nonempty := by
    obtain ⟨y, hy, _⟩ := hP m0 hm0
    exact ⟨y, hy⟩
  obtain ⟨n, hn⟩ : ∃ n, Y.card = n + 1 := ⟨Y.card - 1, by have := hYne.card_pos; omega⟩
  let e : Y ≃ Fin (n+1) := Finset.equivFinOfCardEq hn
  let y : Fin (n+1) → ι := fun i => (e.symm i : ι)
  have hyY : ∀ i, y i ∈ Y := fun i => (e.symm i).2
  have hyinj : Function.Injective y := by
    intro i j hij
    exact e.symm.injective (Subtype.ext hij)
  have hyall : ∀ y' ∈ Y, ∃ i, y i = y' := fun y' hy' => ⟨e ⟨y', hy'⟩, by simp [y]⟩
  have hex : ∀ i, ∃ μ ∈ M, ∀ y' ∈ Y.erase (y i), c ≤ f μ y' := by
    intro i
    have := hmin (Y.erase (y i)) (Finset.erase_ssubset (hyY i))
    push_neg at this
    exact this
  choose μ hμM hμ using hex
  have hμi : ∀ i, f (μ i) (y i) < c := by
    intro i
    obtain ⟨y', hy', hlt⟩ := hP (μ i) (hμM i)
    by_cases h : y' = y i
    · rw [← h]; exact hlt
    · exact absurd hlt (not_lt.2 (hμ i y' (Finset.mem_erase.2 ⟨h, hy'⟩)))
  have hμj : ∀ i j, i ≠ j → c ≤ f (μ i) (y j) := by
    intro i j hij
    exact hμ i (y j) (Finset.mem_erase.2 ⟨fun h => hij (hyinj h).symm, hyY j⟩)
  have hV : ∀ i, ∃ V : Set E, IsOpen V ∧ ∀ z ∈ M, (z ∈ V ↔ f z (y i) < c) :=
    fun i => usc_open M _ c (hu (y i) (hyY i))
  choose V hVo hVM using hV
  have hhull : convexHull ℝ (Set.range μ) ⊆ M :=
    convexHull_min (by rintro _ ⟨i, rfl⟩; exact hμM i) hM
  obtain ⟨z, hzh, hz⟩ := t31_strong n μ V hVo
    (by
      intro z hz
      obtain ⟨y', hy', hlt⟩ := hP z (hhull hz)
      obtain ⟨i, rfl⟩ := hyall y' hy'
      exact Set.mem_iUnion.2 ⟨i, (hVM i z (hhull hz)).2 hlt⟩)
    (fun i => by
      have : convexHull ℝ (Set.range μ) \ V i
          = convexHull ℝ (Set.range μ) ∩ {z ∈ M | c ≤ f z (y i)} := by
        ext z
        simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_setOf_eq]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h1, hhull h1, ?_⟩
          by_contra h
          exact h2 ((hVM i z (hhull h1)).2 (not_le.1 h))
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h1, fun h => absurd ((hVM i z h2).1 h) (not_lt.2 h3)⟩
      rw [this]
      exact (convex_convexHull ℝ _).inter (hq (y i) (hyY i) c))
    (fun i j hij hmem => by
      have := (hVM j (μ i) (hμM i)).1 hmem
      exact absurd (hμj i j hij) (not_le.2 this))
  refine ⟨z, hhull hzh, fun y' hy' => ?_⟩
  obtain ⟨i, rfl⟩ := hyall y' hy'
  exact (hVM i z (hhull hzh)).1 (hz i)

theorem solution {E ι : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (M : Set E) (hM : Convex ℝ M) (hne : M.Nonempty)
    (Y : Finset ι) (f : E → ι → ℝ) (c : ℝ)
    (hq : ∀ y ∈ Y, QuasiconcaveOn ℝ M (fun μ => f μ y))
    (hu : ∀ y ∈ Y, UpperSemicontinuousOn (fun μ => f μ y) M)
    (hP : ∀ μ ∈ M, ∃ y ∈ Y, f μ y < c)
    (hmin : ∀ Y' : Finset ι, Y' ⊂ Y → ¬ ∀ μ ∈ M, ∃ y ∈ Y', f μ y < c) :
    ∃ μ₀ ∈ M, ∀ y ∈ Y, f μ₀ y < c := by
  exact l33_core M hM hne Y f c hq hu hP hmin

end
