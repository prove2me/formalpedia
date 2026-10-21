-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P46.fourierCodeGeometry
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T17:16:23.024124+00:00
-- url     : https://prove2.me/submissions/c62f7887-fc05-4469-93a6-79f9662234a6

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P46
noncomputable section

open QAlgorithms.Papers.Independent.Next46.P46

open QAlgorithms

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.decEq Classical.propDecidable

-- The repair request explicitly authorizes imports from the pinned accepted papers.

open QAlgorithms.Papers.Independent.Information100.P21 (Vec Op)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

open QAlgorithms.Papers.Independent.Frontier30.P12
  (coherentInfo quantumMutualInfo mutualAE marginalAE triCopies EntProtocol RectangularKrausData)

open QAlgorithms.Papers.Independent.Dependency50.P19 (channelSource)

open QAlgorithms.Papers.Independent.Dependency50.P48 (IsDilation)

lemma g62j_coef_eq (s : ℕ) (t j : Fin s) :
    fourierCoefficient s t j = ((Real.sqrt (s : ℝ))⁻¹ : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I / s) ^ ((j : ℕ) * (t : ℕ)) := by
  rw [fourierCoefficient, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

lemma g62j_dft (s : ℕ) (hs : 0 < s) (t t' : Fin s) :
    ∑ j : Fin s, (starRingEnd ℂ) (fourierCoefficient s t j) * fourierCoefficient s t' j =
      if t = t' then 1 else 0 := by
  set ζ := Complex.exp (2 * Real.pi * Complex.I / s) with hζ
  have hprim : IsPrimitiveRoot ζ s := Complex.isPrimitiveRoot_exp s (by omega)
  have hnorm : ‖ζ‖ = 1 := hprim.norm'_eq_one (by omega)
  have hconj : ∀ n : ℕ, (starRingEnd ℂ) (ζ ^ n) = ζ ^ (n * (s - 1)) := by
    intro n
    have h1 : ζ ^ n * (starRingEnd ℂ) (ζ ^ n) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow, hnorm]; simp
    have h2 : ζ ^ n * ζ ^ (n * (s - 1)) = 1 := by
      rw [← pow_add, show n + n * (s - 1) = s * n by
        rcases s with _ | s
        · omega
        · simp [Nat.succ_sub_one]; ring, pow_mul, hprim.pow_eq_one, one_pow]
    have hne : ζ ^ n ≠ 0 := pow_ne_zero _ (by rw [hζ]; exact Complex.exp_ne_zero _)
    have := h1.trans h2.symm
    exact mul_left_cancel₀ hne this
  have hsq : (Real.sqrt (s : ℝ) : ℂ) ^ 2 = s := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; simp
  have hs0 : (Real.sqrt (s : ℝ) : ℂ) ≠ 0 := by
    simp; omega
  simp_rw [g62j_coef_eq, ← hζ, map_mul, map_inv₀, Complex.conj_ofReal, hconj]
  have hterm : ∀ j : Fin s, (Real.sqrt (s : ℝ) : ℂ)⁻¹ * ζ ^ ((j : ℕ) * (t : ℕ) * (s - 1)) *
      ((Real.sqrt (s : ℝ) : ℂ)⁻¹ * ζ ^ ((j : ℕ) * (t' : ℕ))) =
      (s : ℂ)⁻¹ * (ζ ^ ((t : ℕ) * (s - 1) + t')) ^ (j : ℕ) := by
    intro j
    rw [← hsq, ← pow_mul, show ((t : ℕ) * (s - 1) + t') * (j : ℕ) = (j : ℕ) * t * (s - 1) + j * t' by ring,
      pow_add]
    ring
  simp_rw [hterm, ← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun j => (ζ ^ ((t : ℕ) * (s - 1) + t')) ^ j)]
  split_ifs with htt
  · subst htt
    have : ζ ^ ((t : ℕ) * (s - 1) + t) = 1 := by
      rw [show (t : ℕ) * (s - 1) + t = s * t by
        rcases s with _ | s
        · omega
        · simp [Nat.succ_sub_one]; ring, pow_mul, hprim.pow_eq_one, one_pow]
    have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    rw [this]; simp [hsc]
  · have hne : ζ ^ ((t : ℕ) * (s - 1) + t') ≠ 1 := by
      intro h
      rw [hprim.pow_eq_one_iff_dvd] at h
      obtain ⟨k, hk⟩ := h
      have ht := t.isLt
      have ht' := t'.isLt
      apply htt
      apply Fin.ext
      -- t*(s-1) + t' = s*k ; mod s: t' ≡ t
      have h3 : (t : ℕ) * (s - 1) + t' + t = s * (k + 1) - s + t := by
        rw [hk]; rcases k with _ | k <;> simp [Nat.mul_succ] <;> omega
      have h4 : (t : ℕ) * (s - 1) + t = s * t := by
        rcases s with _ | s
        · omega
        · simp [Nat.succ_sub_one]; ring
      have h5 : s * t + t' = s * k + t := by omega
      have hk1 : k = (t : ℕ) ∨ k + 1 = t ∨ k = t + 1 := by
        rcases lt_trichotomy k t with h | h | h
        · right; left
          by_contra hc
          have : k + 2 ≤ t := by omega
          nlinarith
        · left; exact h
        · right; right
          by_contra hc
          have : t + 2 ≤ k := by omega
          nlinarith
      rcases hk1 with h | h | h
      · subst h; omega
      · rw [← h] at h5 ht; nlinarith
      · subst h; nlinarith
    rw [geom_sum_eq hne, show (ζ ^ ((t : ℕ) * (s - 1) + t')) ^ s = 1 by
      rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow]]
    simp

lemma g62j_inner_code {H : Type} [Fintype H] {m s : ℕ}
    (v : Fin m × Fin s → EuclideanSpace ℂ H) (hv : Orthonormal ℂ v) (mj mt : Fin m × Fin s) :
    inner ℂ (v mj) (fourierCode v mt) =
      if mj.1 = mt.1 then fourierCoefficient s mt.2 mj.2 else 0 := by
  rw [orthonormal_iff_ite] at hv
  simp only [fourierCode, inner_sum, inner_smul_right, hv]
  split_ifs with h
  · rw [Finset.sum_eq_single mj.2]
    · simp [Prod.ext_iff, h]
    · intro b _ hb
      simp [Prod.ext_iff, Ne.symm hb]
    · simp
  · apply Finset.sum_eq_zero
    intro j _
    simp [Prod.ext_iff, h]

lemma g62j_code_orth {H : Type} [Fintype H] {m s : ℕ} (hs : 0 < s)
    (v : Fin m × Fin s → EuclideanSpace ℂ H) (hv : Orthonormal ℂ v) :
    Orthonormal ℂ (fourierCode v) := by
  rw [orthonormal_iff_ite]
  intro mt mt'
  conv_lhs => rw [fourierCode]
  simp only [sum_inner, inner_smul_left, g62j_inner_code v hv]
  by_cases h : mt.1 = mt'.1
  · simp only [h, if_true]
    rw [g62j_dft s hs mt.2 mt'.2]
    by_cases h2 : mt.2 = mt'.2
    · simp [h2, Prod.ext_iff, h]
    · simp [h2, Prod.ext_iff]
  · simp [h, Prod.ext_iff]

lemma g62j_code_span {H : Type} [Fintype H] {m s : ℕ} (hs : 0 < s)
    (v : Fin m × Fin s → EuclideanSpace ℂ H) (hv : Orthonormal ℂ v) :
    Submodule.span ℂ (Set.range (fourierCode v)) = Submodule.span ℂ (Set.range v) := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_le]
    rintro _ ⟨mt, rfl⟩
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
  · rw [finrank_span_eq_card (g62j_code_orth hs v hv).linearIndependent,
      finrank_span_eq_card hv.linearIndependent]

/-- arXiv:quant-ph/0307053v1, PDF p.4: Fourier code geometry, with span coverage.
SOURCE CORRECTION: 'mutually unbiased' is blockwise: cross-message overlaps vanish;
for the same message the magnitude is 1/sqrt(S), not 1/sqrt(MS).
No reliability, decoupling, or every-l,t coding-performance assertion follows. -/
theorem solution {H X : Type} [Fintype H] [Nonempty H]
    {l m s : ℕ} (hl : 0 < l) (hm : 0 < m) (hs : 0 < s)
    (base : X → Vec H) (typical : Set X)
    (u : Fin l → Fin m × Fin s → X)
    (hcover : ∀ x, x ∈ typical ↔ ∃ a j, u a j = x)
    (hv : ∀ a, Orthonormal ℂ (fun j => base (u a j))) :
    (∀ a, Orthonormal ℂ (fourierCode (fun j => base (u a j))) ∧
      Submodule.span ℂ (Set.range (fourierCode (fun j => base (u a j)))) =
        Submodule.span ℂ (Set.range (fun j => base (u a j))) ∧
      ∀ mt mj : Fin m × Fin s,
        inner ℂ (base (u a mj)) (fourierCode (fun j => base (u a j)) mt) =
          if mj.1 = mt.1 then fourierCoefficient s mt.2 mj.2 else 0) ∧
    Submodule.span ℂ (⋃ a, Set.range (fourierCode (fun j => base (u a j)))) =
      Submodule.span ℂ (base '' typical) := by
  have hA : ∀ a, Orthonormal ℂ (fourierCode (fun j => base (u a j))) ∧
      Submodule.span ℂ (Set.range (fourierCode (fun j => base (u a j)))) =
        Submodule.span ℂ (Set.range (fun j => base (u a j))) ∧
      ∀ mt mj : Fin m × Fin s,
        inner ℂ (base (u a mj)) (fourierCode (fun j => base (u a j)) mt) =
          if mj.1 = mt.1 then fourierCoefficient s mt.2 mj.2 else 0 :=
    fun a => ⟨g62j_code_orth hs _ (hv a), g62j_code_span hs _ (hv a),
      fun mt mj => g62j_inner_code (fun j => base (u a j)) (hv a) mj mt⟩
  refine ⟨hA, ?_⟩
  rw [Submodule.span_iUnion]
  simp_rw [fun a => (hA a).2.1]
  rw [← Submodule.span_iUnion]
  congr 1
  ext y
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_image, hcover]
  constructor
  · rintro ⟨a, j, rfl⟩
    exact ⟨u a j, ⟨a, j, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨a, j, rfl⟩, rfl⟩
    exact ⟨a, j, rfl⟩



end
