-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P43.multiplicativeDomainBimodule
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T16:27:49.687975+00:00
-- url     : https://prove2.me/submissions/76b7c723-2b5d-4d6d-889c-6ed5e2fcd12a

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P43
noncomputable section

open MeasureTheory Filter

open scoped ENNReal BigOperators

open QAlgorithms.Papers.Independent.Next46.P43

open QAlgorithms.Papers.Independent.Dependency50.P33
  (IsTraceClass IsDensity State tensorApply productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (homogeneousEntropy generalizedRelativeEntropy traceFirst traceSecond)

section
attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus IsStarNormal.instNonUnitalContinuousFunctionalCalculus
set_option linter.unusedSectionVars false
variable {N : Type*} [CStarAlgebra N] [PartialOrder N] [StarOrderedRing N]

theorem g62c_entry_nonneg (X : CStarMatrix (Fin 2) (Fin 2) N) (hX : 0 ≤ X) (i : Fin 2) :
    0 ≤ X i i := by
  rw [StarOrderedRing.nonneg_iff] at hX
  induction hX using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨Y, rfl⟩ := hx
    show 0 ≤ (star Y * Y) i i
    rw [CStarMatrix.mul_apply]
    refine Finset.sum_nonneg (fun k _ => ?_)
    rw [CStarMatrix.star_apply]
    exact star_mul_self_nonneg _
  | zero => exact le_rfl
  | add x y _ _ hx hy => rw [CStarMatrix.add_apply]; exact add_nonneg hx hy

def g62c_m (a b c d : N) : CStarMatrix (Fin 2) (Fin 2) N := CStarMatrix.ofMatrix !![a, b; c, d]

@[simp] theorem g62c_m00 (a b c d : N) : g62c_m a b c d 0 0 = a := rfl
@[simp] theorem g62c_m01 (a b c d : N) : g62c_m a b c d 0 1 = b := rfl
@[simp] theorem g62c_m10 (a b c d : N) : g62c_m a b c d 1 0 = c := rfl
@[simp] theorem g62c_m11 (a b c d : N) : g62c_m a b c d 1 1 = d := rfl

theorem g62c_m_eq (X : CStarMatrix (Fin 2) (Fin 2) N) :
    X = g62c_m (X 0 0) (X 0 1) (X 1 0) (X 1 1) := by
  apply CStarMatrix.ext; intro i j; fin_cases i <;> fin_cases j <;> rfl

theorem g62c_m_mul (a b c d a' b' c' d' : N) :
    g62c_m a b c d * g62c_m a' b' c' d' =
      g62c_m (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  apply CStarMatrix.ext; intro i j
  fin_cases i <;> fin_cases j <;> simp [CStarMatrix.mul_apply, Fin.sum_univ_two, g62c_m]

theorem g62c_m_star (a b c d : N) :
    star (g62c_m a b c d) = g62c_m (star a) (star c) (star b) (star d) := by
  apply CStarMatrix.ext; intro i j
  fin_cases i <;> fin_cases j <;> simp [CStarMatrix.star_apply, g62c_m]

theorem g62c_m_map {M : Type*} (f : N → M) (a b c d : N) :
    (g62c_m a b c d).map f = g62c_m (f a) (f b) (f c) (f d) := by
  apply CStarMatrix.ext; intro i j
  fin_cases i <;> fin_cases j <;> rfl
end

section
set_option linter.unusedSectionVars false
variable {N M : Type*} [CStarAlgebra N] [CStarAlgebra M]
    [PartialOrder N] [PartialOrder M] [StarOrderedRing N] [StarOrderedRing M]

theorem g62c_diag_nonneg (x : N) (hx : 0 ≤ x) : 0 ≤ g62c_m x 0 0 0 := by
  rw [StarOrderedRing.nonneg_iff] at hx
  induction hx using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    have : g62c_m (star s * s) 0 0 0 = star (g62c_m s 0 0 0) * g62c_m s 0 0 0 := by
      rw [g62c_m_star, g62c_m_mul]; simp
    rw [this]; exact star_mul_self_nonneg _
  | zero =>
    have : g62c_m (0 : N) 0 0 0 = 0 := by
      apply CStarMatrix.ext; intro i j; fin_cases i <;> fin_cases j <;> rfl
    rw [this]
  | add x y _ _ hx hy =>
    have : g62c_m (x + y) 0 0 0 = g62c_m x 0 0 0 + g62c_m y 0 0 0 := by
      apply CStarMatrix.ext; intro i j; fin_cases i <;> fin_cases j <;> simp [g62c_m]
    rw [this]; exact add_nonneg hx hy

theorem g62c_pos (σ : N →ₗ[ℂ] M) (hσ : IsCStarCoarseGraining σ) (x : N) (hx : 0 ≤ x) :
    0 ≤ σ x := by
  have h := hσ.2 _ (g62c_diag_nonneg x hx)
  rw [g62c_m_map] at h
  simpa using g62c_entry_nonneg _ h 0

theorem g62c_star (σ : N →ₗ[ℂ] M) (hσ : IsCStarCoarseGraining σ) (a : N) :
    σ (star a) = star (σ a) := by
  have hB : star (g62c_m a 1 0 0) * g62c_m a 1 0 0 = g62c_m (star a * a) (star a) a 1 := by
    rw [g62c_m_star, g62c_m_mul]; simp
  have h := hσ.2 _ (star_mul_self_nonneg (g62c_m a 1 0 0))
  rw [hB, g62c_m_map] at h
  have hsa := (IsSelfAdjoint.of_nonneg h).star_eq
  have := congrArg (fun X : CStarMatrix (Fin 2) (Fin 2) M => X 0 1) hsa
  simp only [g62c_m_star, g62c_m01] at this
  exact this.symm

theorem g62c_schwarz (σ : N →ₗ[ℂ] M) (hσ : IsCStarCoarseGraining σ) (a : N) :
    0 ≤ σ (star a * a) - star (σ a) * σ a := by
  have hB : star (g62c_m a 1 0 0) * g62c_m a 1 0 0 = g62c_m (star a * a) (star a) a 1 := by
    rw [g62c_m_star, g62c_m_mul]; simp
  have h := hσ.2 _ (star_mul_self_nonneg (g62c_m a 1 0 0))
  rw [hB, g62c_m_map, g62c_star σ hσ, hσ.1] at h
  have h2 := star_left_conjugate_nonneg h (g62c_m 1 0 (-σ a) 0)
  rw [g62c_m_star, g62c_m_mul, g62c_m_mul] at h2
  have h3 := g62c_entry_nonneg _ h2 0
  simp only [g62c_m00] at h3
  convert h3 using 1
  simp only [star_one, star_zero, star_neg]
  noncomm_ring

theorem g62c_zero_of (S Db : M) (h : ∀ t : ℝ, 0 ≤ t • S + t ^ 2 • Db) : S = 0 := by
  have hc : Continuous (fun t : ℝ => S + t • Db) := by fun_prop
  have hpos : ∀ t : ℝ, 0 < t → 0 ≤ S + t • Db := by
    intro t ht
    have := smul_nonneg (inv_nonneg.2 ht.le) (h t)
    convert this using 1
    rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ ht.ne', one_smul, pow_two,
      ← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul]
  have hneg : ∀ t : ℝ, 0 < t → 0 ≤ -S + t • Db := by
    intro t ht
    have := smul_nonneg (inv_nonneg.2 ht.le) (h (-t))
    convert this using 1
    rw [smul_add, smul_smul, smul_smul, neg_sq, pow_two, ← mul_assoc, inv_mul_cancel₀ ht.ne',
      one_mul, mul_neg, inv_mul_cancel₀ ht.ne', neg_smul, one_smul]
  have hcl : IsClosed {x : M | 0 ≤ x} := isClosed_Ici
  have l1 : 0 ≤ S := by
    have ht : Filter.Tendsto (fun t : ℝ => S + t • Db) (nhdsWithin 0 (Set.Ioi 0)) (nhds S) := by
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
      simpa using this
    exact hcl.mem_of_tendsto ht (eventually_nhdsWithin_of_forall (fun t ht => hpos t ht))
  have l2 : 0 ≤ -S := by
    have hc' : Continuous (fun t : ℝ => -S + t • Db) := by fun_prop
    have ht : Filter.Tendsto (fun t : ℝ => -S + t • Db) (nhdsWithin 0 (Set.Ioi 0)) (nhds (-S)) := by
      have := (hc'.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
      simpa using this
    exact hcl.mem_of_tendsto ht (eventually_nhdsWithin_of_forall (fun t ht => hneg t ht))
  exact le_antisymm (neg_nonneg.1 l2) l1

theorem g62c_expand (σ : N →ₗ[ℂ] M) (hσ : IsCStarCoarseGraining σ) (a b : N) (c : ℂ) :
    σ (star (a + c • b) * (a + c • b)) - star (σ (a + c • b)) * σ (a + c • b) =
      (σ (star a * a) - star (σ a) * σ a)
      + c • (σ (star a * b) - star (σ a) * σ b)
      + star c • (σ (star b * a) - star (σ b) * σ a)
      + (star c * c) • (σ (star b * b) - star (σ b) * σ b) := by
  simp only [star_add, star_smul, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, map_add,
    map_smul, smul_add, smul_sub, smul_smul]
  rw [mul_comm c (star c)]
  abel

theorem g62c_left (σ : N →ₗ[ℂ] M) (hσ : IsCStarCoarseGraining σ) (a : N)
    (ha : σ (star a * a) = star (σ a) * σ a) (b : N) :
    σ (star a * b) = star (σ a) * σ b := by
  have hDa : σ (star a * a) - star (σ a) * σ a = 0 := sub_eq_zero.2 ha
  have key : ∀ b' : N, (σ (star a * b') - star (σ a) * σ b') +
      star (σ (star a * b') - star (σ a) * σ b') = 0 := by
    intro b'
    apply g62c_zero_of _ (σ (star b' * b') - star (σ b') * σ b')
    intro t
    have h := g62c_schwarz σ hσ (a + (t : ℂ) • b')
    rw [g62c_expand σ hσ, hDa] at h
    have hs : star (σ (star a * b') - star (σ a) * σ b') =
        σ (star b' * a) - star (σ b') * σ a := by
      rw [star_sub, ← g62c_star σ hσ, star_mul, star_star, star_mul, star_star]
    convert h using 1
    rw [hs, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← pow_two]
    simp only [zero_add, smul_add, Complex.coe_smul]
  set E := σ (star a * b) - star (σ a) * σ b with hE
  have h1 := key b
  have h2 := key (Complex.I • b)
  have hEI : σ (star a * (Complex.I • b)) - star (σ a) * σ (Complex.I • b) = Complex.I • E := by
    rw [hE, mul_smul_comm, map_smul, map_smul, mul_smul_comm, smul_sub]
  rw [hEI, star_smul, Complex.star_def, Complex.conj_I] at h2
  rw [← hE] at h1
  have h4 := congrArg (fun x => Complex.I • x) h2
  simp only [smul_add, smul_smul, Complex.I_mul_I, smul_zero] at h4
  have h5 : star E - E = 0 := by
    rw [sub_eq_add_neg]
    have h6 : (-1 : ℂ) • E + (Complex.I * -Complex.I) • star E = 0 := h4
    rw [mul_neg, Complex.I_mul_I, neg_neg, one_smul, neg_one_smul] at h6
    rw [add_comm]; exact h6
  rw [sub_eq_zero] at h5
  rw [h5, ← two_smul ℂ E] at h1
  have : E = 0 := (smul_eq_zero.1 h1).resolve_left two_ne_zero
  exact sub_eq_zero.1 this
end

section
set_option linter.unusedSectionVars false
variable {N M : Type*} [CStarAlgebra N] [CStarAlgebra M]
    [PartialOrder N] [PartialOrder M] [StarOrderedRing N] [StarOrderedRing M]

theorem g62c_iff (σ : N →ₗ[ℂ] M) (hσ : IsCStarCoarseGraining σ) (a : N) :
    a ∈ MultiplicativeDomain σ ↔ ∀ b, σ (a * b) = σ a * σ b ∧ σ (b * a) = σ b * σ a := by
  constructor
  · rintro ⟨h1, h2⟩ b
    have hl : ∀ c, σ (a * c) = σ a * σ c := by
      intro c
      have h2' : σ (star (star a) * star a) = star (σ (star a)) * σ (star a) := by
        rw [star_star, g62c_star σ hσ, star_star]; exact h2
      have := g62c_left σ hσ (star a) h2' c
      rwa [star_star, g62c_star σ hσ, star_star] at this
    refine ⟨hl b, ?_⟩
    have := g62c_left σ hσ a h1 (star b)
    have e : b * a = star (star a * star b) := by rw [star_mul, star_star, star_star]
    rw [e, g62c_star σ hσ, this, star_mul, star_star, g62c_star σ hσ, star_star]
  · intro h
    refine ⟨?_, ?_⟩
    · rw [(h (star a)).2, g62c_star σ hσ]
    · rw [(h (star a)).1, g62c_star σ hσ]
end

theorem solution
    {N M : Type*} [CStarAlgebra N] [CStarAlgebra M]
    [PartialOrder N] [PartialOrder M] [StarOrderedRing N] [StarOrderedRing M]
    (sigma : N →ₗ[ℂ] M) (hSigma : IsCStarCoarseGraining sigma) :
    ∃ D : StarSubalgebra ℂ N, (D : Set N) = MultiplicativeDomain sigma ∧
      IsClosed (D : Set N) ∧
      ∀ a ∈ D, ∀ b : N,
        sigma (a * b) = sigma a * sigma b ∧
        sigma (b * a) = sigma b * sigma a := by
  have hI := g62c_iff sigma hSigma
  let D : StarSubalgebra ℂ N :=
    { carrier := MultiplicativeDomain sigma
      mul_mem' := by
        intro a c ha hc
        rw [hI] at ha hc ⊢
        intro b
        refine ⟨?_, ?_⟩
        · rw [mul_assoc, (ha _).1, (hc _).1, (ha c).1, mul_assoc]
        · rw [← mul_assoc, (hc _).2, (ha _).2, (hc a).2, mul_assoc]
      add_mem' := by
        intro a c ha hc
        rw [hI] at ha hc ⊢
        intro b
        simp only [add_mul, mul_add, map_add, (ha b).1, (hc b).1, (ha b).2, (hc b).2, true_and]
      algebraMap_mem' := by
        intro r
        rw [hI]
        intro b
        simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, mul_smul_comm,
          mul_one, map_smul, hSigma.1, and_self]
      star_mem' := by
        intro a ha
        rw [hI] at ha ⊢
        intro b
        refine ⟨?_, ?_⟩
        · have e : star a * b = star (star b * a) := by rw [star_mul, star_star]
          rw [e, g62c_star sigma hSigma, (ha _).2, star_mul, g62c_star sigma hSigma,
            g62c_star sigma hSigma, star_star]
        · have e : b * star a = star (a * star b) := by rw [star_mul, star_star]
          rw [e, g62c_star sigma hSigma, (ha _).1, star_mul, g62c_star sigma hSigma,
            g62c_star sigma hSigma, star_star] }
  have hcont : Continuous sigma := by
    let P : N →ₚ[ℂ] M := PositiveLinearMap.mk₀ sigma (g62c_pos sigma hSigma)
    exact map_continuous P
  refine ⟨D, rfl, ?_, fun a ha b => (hI a).1 ha b⟩
  have : (D : Set N) = ⋂ b : N, ({a | sigma (a * b) = sigma a * sigma b} ∩
      {a | sigma (b * a) = sigma b * sigma a}) := by
    ext a
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]
    exact hI a
  rw [this]
  refine isClosed_iInter (fun b => IsClosed.inter ?_ ?_)
  · exact isClosed_eq (hcont.comp (continuous_mul_right b))
      (hcont.mul continuous_const)
  · exact isClosed_eq (hcont.comp (continuous_mul_left b))
      (continuous_const.mul hcont)
