-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P17.regularisedMaximum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T07:24:57.527377+00:00
-- url     : https://prove2.me/submissions/2d9faa7e-076c-45c3-b3f2-b0e21858f7f5

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P17
noncomputable section

open MeasureTheory

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

open QAlgorithms QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Support50 QAlgorithms.Papers.Independent.Support50.P17

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the exact frozen support predicate and signed, unnormalised entropy.

open QAlgorithms.Papers.Independent.Dependency50.P21 (IsSupported relativeEntropy)

lemma rm_real1 {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    (x + 1) * Real.log (x + 1) ≤ 2 * Real.log 2 * x := by
  have := Real.convexOn_mul_log.2 (show (1:ℝ) ∈ Set.Ici (0:ℝ) by norm_num)
    (show (2:ℝ) ∈ Set.Ici (0:ℝ) by norm_num) (show 0 ≤ 1 - x by linarith) h0
    (by ring : (1 - x) + x = 1)
  simp only [smul_eq_mul, Real.log_one, mul_zero] at this
  have e : (1 - x) * 1 + x * 2 = x + 1 := by ring
  rw [e] at this
  linarith

lemma rm_real2 {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    x * Real.log 2 ≤ Real.log (x + 1) := by
  have := strictConcaveOn_log_Ioi.concaveOn.2 (show (1:ℝ) ∈ Set.Ioi (0:ℝ) by norm_num)
    (show (2:ℝ) ∈ Set.Ioi (0:ℝ) by norm_num) (show 0 ≤ 1 - x by linarith) h0
    (by ring : (1 - x) + x = 1)
  simp only [smul_eq_mul, Real.log_one, mul_zero] at this
  have e : (1 - x) * 1 + x * 2 = x + 1 := by ring
  rw [e] at this
  linarith

lemma rm_trace_mul_cfc {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) (M : Matrix n n ℂ) :
    (M * cfc f A).trace = ∑ i, (f (hA.eigenvalues i) : ℂ) *
      ((star (hA.eigenvectorUnitary : Matrix n n ℂ)) * M * hA.eigenvectorUnitary) i i := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ)
  set D : Matrix n n ℂ := Matrix.diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues)
  have key : (M * (U * D * star U)).trace = ((star U * M * U) * D).trace := by
    rw [show M * (U * D * star U) = (M * U * D) * star U by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [key]
  simp only [D, Matrix.trace, Matrix.diag, Matrix.mul_diagonal, Function.comp_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]
  rfl

lemma rm_cfc_shift {I : Type*} [Fintype I] [DecidableEq I] (rho : Matrix I I ℂ) (hr : rho.PosSemidef)
    (g : ℝ → ℝ) (hg : ContinuousOn g (Set.Ici 1)) :
    cfc g (rho + 1) = cfc (fun x => g (x + 1)) rho := by
  have hsub : (fun x : ℝ => x + 1) '' spectrum ℝ rho ⊆ Set.Ici 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have : 0 ≤ x := by
      obtain ⟨i, rfl⟩ := hr.1.spectrum_real_eq_range_eigenvalues ▸ hx
      exact hr.eigenvalues_nonneg i
    simp; linarith
  have e : cfc (fun x : ℝ => x + 1) rho = rho + 1 := by
    rw [show (fun x : ℝ => x + 1) = (fun x => id x + 1) from rfl,
      cfc_add_const (1 : ℝ) id rho (by fun_prop) hr.1.isSelfAdjoint, cfc_id ℝ rho hr.1.isSelfAdjoint]
    simp
  rw [cfc_comp' g (fun x => x + 1) rho (hg.mono hsub) (by fun_prop) hr.1.isSelfAdjoint, e]

lemma rm_trace_cfc {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, (f (hA.eigenvalues i) : ℂ) := by
  have := rm_trace_mul_cfc hA f 1
  rw [Matrix.one_mul] at this
  rw [this]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

lemma rm_sum_eig {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : IsDensityMatrix A) : ∑ i, hA.1.1.eigenvalues i = 1 := by
  have h := hA.1.1.trace_eq_sum_eigenvalues
  have := congrArg Complex.re (h.symm.trans hA.2)
  simpa [Complex.re_sum] using this

lemma rm_eig_le_one {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : IsDensityMatrix A) (i : n) : hA.1.1.eigenvalues i ≤ 1 := by
  rw [← rm_sum_eig hA]
  exact Finset.single_le_sum (fun j _ => hA.1.eigenvalues_nonneg j) (Finset.mem_univ i)

lemma rm_eig01 {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : IsDensityMatrix A) (hrk : A.rank = 1) (i : n) :
    hA.1.1.eigenvalues i = 0 ∨ hA.1.1.eigenvalues i = 1 := by
  have hc := hA.1.1.rank_eq_card_non_zero_eigs
  rw [hrk] at hc
  obtain ⟨⟨i0, hi0⟩, huniq⟩ := Fintype.card_eq_one_iff.mp hc.symm
  have hz : ∀ j, j ≠ i0 → hA.1.1.eigenvalues j = 0 := fun j hj => by
    by_contra h
    exact hj (congrArg Subtype.val (huniq ⟨j, h⟩))
  have h1 : hA.1.1.eigenvalues i0 = 1 := by
    rw [← rm_sum_eig hA, Finset.sum_eq_single i0 (fun j _ hj => hz j hj) (by simp)]
  by_cases h : i = i0
  · subst h; exact Or.inr h1
  · exact Or.inl (hz i h)

lemma rm_supp {n : Type*} [Fintype n] [DecidableEq n] (rho sigma : Matrix n n ℂ)
    (hs : sigma.PosSemidef) : IsSupported rho (sigma + 1) := by
  show LinearMap.ker _ ≤ LinearMap.ker _
  intro v hv
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  have h1 : sigma *ᵥ v = -v := by
    rw [Matrix.add_mulVec, Matrix.one_mulVec] at hv
    exact eq_neg_of_add_eq_zero_left hv
  have h2 := hs.dotProduct_mulVec_nonneg v
  rw [h1, dotProduct_neg] at h2
  have h3 : star v ⬝ᵥ v = 0 := le_antisymm (neg_nonneg.mp h2) (dotProduct_star_self_nonneg v)
  have : v = 0 := dotProduct_star_self_eq_zero.mp h3
  rw [this, Matrix.mulVec_zero]

lemma rm_value {I : Type*} [Fintype I] [DecidableEq I] (rho sigma : Matrix I I ℂ)
    (hr : rho.PosSemidef) (hs : sigma.PosSemidef) :
    (cfc (fun x : ℝ => x * Real.log x) (rho + 1) - (rho + 1) * cfc Real.log (sigma + 1)).trace.re =
      ∑ i, (hr.1.eigenvalues i + 1) * Real.log (hr.1.eigenvalues i + 1)
      - ∑ j, Real.log (hs.1.eigenvalues j + 1) *
          ((star (hs.1.eigenvectorUnitary : Matrix I I ℂ) * rho *
            (hs.1.eigenvectorUnitary : Matrix I I ℂ)) j j).re
      - ∑ j, Real.log (hs.1.eigenvalues j + 1) := by
  rw [rm_cfc_shift rho hr _ Real.continuous_mul_log.continuousOn,
    rm_cfc_shift sigma hs Real.log (Real.continuousOn_log.mono
      (fun x (hx : 1 ≤ x) => show x ≠ 0 from ne_of_gt (lt_of_lt_of_le one_pos hx))),
    Matrix.add_mul, Matrix.one_mul, Matrix.trace_sub, Matrix.trace_add, rm_trace_cfc hr.1,
    rm_trace_mul_cfc hs.1, rm_trace_cfc hs.1]
  simp only [Complex.sub_re, Complex.add_re, Complex.re_sum, Complex.re_ofReal_mul,
    Complex.ofReal_re]
  ring

theorem rm_main {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho sigma : Matrix I I ℂ) (hr : IsDensityMatrix rho) (hs : IsDensityMatrix sigma) :
    relativeEntropy (rho + 1) (sigma + 1) ≤ (Real.log 2 : EReal) ∧
      (rho.rank = 1 → sigma.rank = 1 → rho * sigma = 0 →
        relativeEntropy (rho + 1) (sigma + 1) = (Real.log 2 : EReal)) := by
  have hE := rm_value rho sigma hr.1 hs.1
  set V : Matrix I I ℂ := (hs.1.1.eigenvectorUnitary : Matrix I I ℂ)
  have hRE : relativeEntropy (rho + 1) (sigma + 1) =
      ((cfc (fun x : ℝ => x * Real.log x) (rho + 1) -
        (rho + 1) * cfc Real.log (sigma + 1)).trace.re : EReal) := by
    rw [relativeEntropy, if_pos (rm_supp _ _ hs.1)]
  rw [hE] at hRE
  rw [hRE]
  have hl0 := fun i => hr.1.eigenvalues_nonneg i
  have hl1 := rm_eig_le_one hr
  have hm0 := fun i => hs.1.eigenvalues_nonneg i
  have hm1 := rm_eig_le_one hs
  have hW : ∀ j, 0 ≤ ((star V * rho * V) j j).re := fun j =>
    (Complex.nonneg_iff.mp ((hr.1.conjTranspose_mul_mul_same V).diag_nonneg (i := j))).1
  have hT1 : ∑ i, (hr.1.1.eigenvalues i + 1) * Real.log (hr.1.1.eigenvalues i + 1)
      ≤ 2 * Real.log 2 := by
    calc _ ≤ ∑ i, 2 * Real.log 2 * hr.1.1.eigenvalues i :=
          Finset.sum_le_sum fun i _ => rm_real1 (hl0 i) (hl1 i)
      _ = 2 * Real.log 2 := by rw [← Finset.mul_sum, rm_sum_eig hr, mul_one]
  have hT2 : 0 ≤ ∑ j, Real.log (hs.1.1.eigenvalues j + 1) * ((star V * rho * V) j j).re :=
    Finset.sum_nonneg fun j _ => mul_nonneg (Real.log_nonneg (by linarith [hm0 j])) (hW j)
  have hT3 : Real.log 2 ≤ ∑ j, Real.log (hs.1.1.eigenvalues j + 1) := by
    calc Real.log 2 = ∑ j, hs.1.1.eigenvalues j * Real.log 2 := by
          rw [← Finset.sum_mul, rm_sum_eig hs, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun j _ => rm_real2 (hm0 j) (hm1 j)
  refine ⟨EReal.coe_le_coe_iff.mpr (by linarith), fun hrk hsk hmul => ?_⟩
  congr 1
  have e1 : ∑ i, (hr.1.1.eigenvalues i + 1) * Real.log (hr.1.1.eigenvalues i + 1)
      = 2 * Real.log 2 := by
    calc _ = ∑ i, 2 * Real.log 2 * hr.1.1.eigenvalues i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rcases rm_eig01 hr hrk i with h | h <;> rw [h] <;> norm_num
      _ = 2 * Real.log 2 := by rw [← Finset.mul_sum, rm_sum_eig hr, mul_one]
  have e3 : ∑ j, Real.log (hs.1.1.eigenvalues j + 1) = Real.log 2 := by
    calc _ = ∑ j, Real.log 2 * hs.1.1.eigenvalues j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rcases rm_eig01 hs hsk j with h | h <;> rw [h] <;> norm_num
      _ = Real.log 2 := by rw [← Finset.mul_sum, rm_sum_eig hs, mul_one]
  have e2 : ∑ j, Real.log (hs.1.1.eigenvalues j + 1) * ((star V * rho * V) j j).re = 0 := by
    have h0 := rm_trace_mul_cfc hs.1.1 id rho
    rw [cfc_id ℝ sigma hs.1.1.isSelfAdjoint, hmul, Matrix.trace_zero] at h0
    have h0' := congrArg Complex.re h0
    simp only [Complex.zero_re, Complex.re_sum, Complex.re_ofReal_mul, id] at h0'
    calc _ = ∑ j, Real.log 2 * (hs.1.1.eigenvalues j * ((star V * rho * V) j j).re) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rcases rm_eig01 hs hsk j with h | h <;> rw [h] <;> norm_num
      _ = 0 := by rw [← Finset.mul_sum, ← h0', mul_zero]
  rw [e1, e2, e3]
  ring

lemma rm_diag {d : ℕ} (a : Fin d) :
    IsDensityMatrix (Matrix.diagonal (fun k : Fin d => if k = a then (1:ℂ) else 0)) ∧
    (Matrix.diagonal (fun k : Fin d => if k = a then (1:ℂ) else 0)).rank = 1 := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Matrix.posSemidef_diagonal_iff]
    intro i; split_ifs <;> norm_num
  · simp [Matrix.trace_diagonal]
  · rw [Matrix.rank_diagonal]
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨a, by simp⟩, fun ⟨x, hx⟩ => ?_⟩
    have : x = a := by by_contra h; simp [h] at hx
    subst this; rfl

theorem rm_second : ∀ d : ℕ, 2 ≤ d → ∃ rho sigma : Matrix (Fin d) (Fin d) ℂ,
      IsDensityMatrix rho ∧ IsDensityMatrix sigma ∧
      rho.rank = 1 ∧ sigma.rank = 1 ∧ rho * sigma = 0 ∧
      relativeEntropy (rho + 1) (sigma + 1) = (Real.log 2 : EReal) := by
  intro d hd
  have h0 : 0 < d := by omega
  have h1 : 1 < d := by omega
  obtain ⟨hr, hrk⟩ := rm_diag (⟨0, h0⟩ : Fin d)
  obtain ⟨hs, hsk⟩ := rm_diag (⟨1, h1⟩ : Fin d)
  have hmul : Matrix.diagonal (fun k : Fin d => if k = ⟨0, h0⟩ then (1:ℂ) else 0) *
      Matrix.diagonal (fun k : Fin d => if k = ⟨1, h1⟩ then (1:ℂ) else 0) = 0 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_zero]
    congr 1
    funext k
    by_cases ha : k = ⟨0, h0⟩
    · have hb : k ≠ ⟨1, h1⟩ := by rw [ha]; simp [Fin.ext_iff]
      simp [hb]
    · simp [ha]
  have : Nonempty (Fin d) := ⟨⟨0, h0⟩⟩
  exact ⟨_, _, hr, hs, hrk, hsk, hmul, (rm_main _ _ hr hs).2 hrk hsk hmul⟩

/-- PDF p.2, Section I: the global log 2 maximum and equality for orthogonal pure
states. Such witnesses exist in every dimension d≥2; dimension one retains the bound. -/
theorem solution :
    (∀ {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
      (rho sigma : Matrix I I ℂ), IsDensityMatrix rho → IsDensityMatrix sigma →
      relativeEntropy (rho + 1) (sigma + 1) ≤ (Real.log 2 : EReal) ∧
        (rho.rank = 1 → sigma.rank = 1 → rho * sigma = 0 →
          relativeEntropy (rho + 1) (sigma + 1) = (Real.log 2 : EReal))) ∧
    (∀ d : ℕ, 2 ≤ d → ∃ rho sigma : Matrix (Fin d) (Fin d) ℂ,
      IsDensityMatrix rho ∧ IsDensityMatrix sigma ∧
      rho.rank = 1 ∧ sigma.rank = 1 ∧ rho * sigma = 0 ∧
      relativeEntropy (rho + 1) (sigma + 1) = (Real.log 2 : EReal)) := ⟨fun rho sigma hr hs => rm_main rho sigma hr hs, rm_second⟩


end
