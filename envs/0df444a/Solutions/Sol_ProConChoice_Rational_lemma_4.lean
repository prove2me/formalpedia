-- Prove2me | solution 1 for ProConChoice.Rational.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:45:33.935643+00:00
-- url     : https://prove2.me/submissions/3b42687d-2775-4d6a-9d8d-ad35191b7302

import Mathlib
set_option autoImplicit false

theorem solution {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (hA : A.IsTotallyUnimodular) (b : m → ℝ) (hb : ∀ i, ∃ z : ℤ, b i = z) :
    ∀ v ∈ Set.extremePoints ℝ {x : n → ℝ | A.mulVec x = b ∧ ∀ j, -1 ≤ x j ∧ x j ≤ 1},
      ∀ j, ∃ z : ℤ, v j = z := by
  classical
  intro v hv
  obtain ⟨⟨hAv, hbd⟩, hext⟩ := mem_extremePoints.mp hv
  set F : Finset n := Finset.univ.filter (fun j => -1 < v j ∧ v j < 1) with hF
  have hmemF : ∀ j, j ∈ F ↔ (-1 < v j ∧ v j < 1) := by intro j; simp [hF]
  -- coordinates outside F are ±1
  have hnotF : ∀ j, j ∉ F → ∃ z : ℤ, v j = z := by
    intro j hj
    rw [hmemF] at hj
    have h1 := (hbd j).1
    have h2 := (hbd j).2
    by_cases h : -1 < v j
    · have : 1 ≤ v j := by
        by_contra h'; exact hj ⟨h, by linarith⟩
      exact ⟨1, by push_cast; linarith⟩
    · exact ⟨-1, by push_cast; linarith⟩
  -- entries of A are integers
  have hAint : ∀ i j, ∃ z : ℤ, A i j = z := by
    intro i j
    obtain ⟨s, hs⟩ := hA.apply i j
    refine ⟨(s : ℤ), ?_⟩
    rw [← hs]
    cases s <;> simp
  -- columns of F are independent
  have hindep : ∀ c : n → ℝ, (∀ j, j ∉ F → c j = 0) → A.mulVec c = 0 → c = 0 := by
    intro c hc0 hAc
    by_contra hne
    set δ : n → ℝ := fun j => min (1 - v j) (v j + 1) with hδ
    have hδpos : ∀ j ∈ F, 0 < δ j := by
      intro j hj
      rw [hmemF] at hj
      simp only [hδ]
      exact lt_min (by linarith [hj.2]) (by linarith [hj.1])
    set ε : ℝ := 1 / (1 + ∑ j ∈ F, |c j| / δ j) with hε
    have hsum0 : 0 ≤ ∑ j ∈ F, |c j| / δ j :=
      Finset.sum_nonneg (fun j hj => div_nonneg (abs_nonneg _) (hδpos j hj).le)
    have hεpos : 0 < ε := by rw [hε]; positivity
    have hεc : ∀ j ∈ F, ε * |c j| ≤ δ j := by
      intro j hj
      have h1 : |c j| / δ j ≤ ∑ i ∈ F, |c i| / δ i :=
        Finset.single_le_sum (f := fun i => |c i| / δ i)
          (fun i hi => div_nonneg (abs_nonneg _) (hδpos i hi).le) hj
      have h2 : |c j| ≤ δ j * (1 + ∑ i ∈ F, |c i| / δ i) := by
        have := (div_le_iff₀ (hδpos j hj)).mp h1
        nlinarith [hδpos j hj]
      rw [hε, one_div, inv_mul_eq_div, div_le_iff₀ (by linarith)]
      linarith
    have hbd' : ∀ s : ℝ, (s = 1 ∨ s = -1) → ∀ j, -1 ≤ v j + s * (ε * c j) ∧ v j + s * (ε * c j) ≤ 1 := by
      intro s hs j
      by_cases hj : j ∈ F
      · have h1 := hεc j hj
        have h2 : δ j ≤ 1 - v j := min_le_left _ _
        have h3 : δ j ≤ v j + 1 := min_le_right _ _
        have h4 : |ε * c j| ≤ δ j := by rw [abs_mul, abs_of_pos hεpos]; exact h1
        have h5 := abs_le.mp h4
        rcases hs with rfl | rfl
        · constructor <;> nlinarith [h5.1, h5.2]
        · constructor <;> nlinarith [h5.1, h5.2]
      · rw [hc0 j hj]; simp
        exact hbd j
    have hQ : ∀ s : ℝ, (s = 1 ∨ s = -1) →
        (v + s • (ε • c)) ∈ {x : n → ℝ | A.mulVec x = b ∧ ∀ j, -1 ≤ x j ∧ x j ≤ 1} := by
      intro s hs
      refine ⟨?_, fun j => ?_⟩
      · rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hAc, hAv]; simp
      · simpa using hbd' s hs j
    have hseg : v ∈ openSegment ℝ (v + (1 : ℝ) • (ε • c)) (v + (-1 : ℝ) • (ε • c)) := by
      refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
      ext j; simp; ring
    obtain ⟨h1, _⟩ := hext _ (hQ 1 (Or.inl rfl)) _ (hQ (-1) (Or.inr rfl)) hseg
    apply hne
    have : ε • c = 0 := by
      have := congrArg (fun x => x - v) h1
      simpa using this
    rcases smul_eq_zero.mp this with h | h
    · exact absurd h hεpos.ne'
    · exact h
  -- rows restricted to F
  let ρ : m → (F → ℝ) := fun i t => A i t.1
  have hAFinj : ∀ y : F → ℝ, (∀ i, ∑ t : F, A i t.1 * y t = 0) → y = 0 := by
    intro y hy
    set c : n → ℝ := fun j => if h : j ∈ F then y ⟨j, h⟩ else 0 with hc
    have hc0 : ∀ j, j ∉ F → c j = 0 := by intro j hj; simp [hc, hj]
    have hAc : A.mulVec c = 0 := by
      funext i
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      have h1 : ∑ j, A i j * c j = ∑ j ∈ F, A i j * c j :=
        (Finset.sum_subset (Finset.subset_univ F) (by intro j _ hj; rw [hc0 j hj]; simp)).symm
      rw [h1, ← hy i, ← Finset.sum_coe_sort F]
      apply Finset.sum_congr rfl
      intro t _
      simp [hc, t.2]
    have h0 := hindep c hc0 hAc
    funext t
    have := congrFun h0 t.1
    simpa [hc, t.2] using this
  have hspan : Submodule.span ℝ (Set.range ρ) = ⊤ := by
    by_contra hne
    have hlt : Submodule.span ℝ (Set.range ρ) < ⊤ := lt_top_iff_ne_top.mpr hne
    obtain ⟨f, hf0, hfle⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
    set y : F → ℝ := fun t => f (fun j => if t = j then 1 else 0) with hy
    have hfx : ∀ x : F → ℝ, f x = ∑ t, x t * y t := by
      intro x
      rw [LinearMap.pi_apply_eq_sum_univ f x]
      simp [hy]
    have hy0 : y = 0 := by
      apply hAFinj y
      intro i
      have h1 : f (ρ i) = 0 := hfle (Submodule.subset_span ⟨i, rfl⟩)
      rw [hfx] at h1
      simpa [ρ] using h1
    apply hf0
    apply LinearMap.ext
    intro x
    rw [hfx x, hy0]; simp
  obtain ⟨κ, a, ha_inj, ha_span, ha_li⟩ := exists_linearIndependent' ℝ ρ
  rw [hspan] at ha_span
  let bs : Module.Basis κ ℝ (F → ℝ) := Module.Basis.mk ha_li ha_span.ge
  let e : κ ≃ F := bs.indexEquiv (Pi.basisFun ℝ F)
  let Msq : Matrix F F ℝ := Matrix.of fun p q => A (a (e.symm p)) q.1
  have hMli : LinearIndependent ℝ (fun p => Msq p) := ha_li.comp e.symm e.symm.injective
  have hMunit : IsUnit Msq := Matrix.linearIndependent_rows_iff_isUnit.mp hMli
  have hdet0 : Msq.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det Msq).mp hMunit).ne_zero
  have hdetTU : Msq.det ∈ Set.range (SignType.cast : SignType → ℝ) :=
    (Matrix.isTotallyUnimodular_iff_fintype A).mp hA F (fun p => a (e.symm p)) (fun q => q.1)
  have hdetsq : Msq.det * Msq.det = 1 := by
    obtain ⟨s, hs⟩ := hdetTU
    cases s with
    | zero => exact absurd hs.symm (by simpa using hdet0)
    | pos => simp at hs; rw [← hs]; norm_num
    | neg => simp at hs; rw [← hs]; norm_num
  choose ZA hZA using hAint
  let Zm : Matrix F F ℤ := Matrix.of fun p q => ZA (a (e.symm p)) q.1
  have hMZ : Msq = Zm.map (Int.cast : ℤ → ℝ) := by
    ext p q; simp [Msq, Zm, hZA]
  have hdetZ : Msq.det = ((Zm.det : ℤ) : ℝ) := by
    have := RingHom.map_det (Int.castRingHom ℝ) Zm
    rw [hMZ]
    simpa using this.symm
  have hadj : Msq.adjugate = (Zm.adjugate).map (Int.cast : ℤ → ℝ) := by
    have := RingHom.map_adjugate (Int.castRingHom ℝ) Zm
    rw [hMZ]
    simpa using this.symm
  -- right-hand side
  let Zv : n → ℤ := fun j => if h : j ∈ F then 0 else Classical.choose (hnotF j h)
  have hZv : ∀ j, j ∉ F → v j = (Zv j : ℝ) := by
    intro j hj
    simp only [Zv, dif_neg hj]
    exact Classical.choose_spec (hnotF j hj)
  set bp : m → ℝ := fun i => b i - ∑ j ∈ Fᶜ, A i j * v j with hbp
  have hbp_int : ∀ i, ∃ z : ℤ, bp i = z := by
    intro i
    obtain ⟨zb, hzb⟩ := hb i
    refine ⟨zb - ∑ j ∈ Fᶜ, ZA i j * Zv j, ?_⟩
    simp only [hbp]
    push_cast
    rw [hzb]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [hZA i j, hZv j (by simpa using hj)]
  have hAy : ∀ i, ∑ t : F, A i t.1 * v t.1 = bp i := by
    intro i
    have h1 : ∑ j, A i j * v j = b i := by
      have := congrFun hAv i
      simpa [Matrix.mulVec, dotProduct] using this
    have h2 : ∑ j ∈ F, A i j * v j + ∑ j ∈ Fᶜ, A i j * v j = ∑ j, A i j * v j :=
      Finset.sum_add_sum_compl F _
    have h3 : ∑ t : F, A i t.1 * v t.1 = ∑ j ∈ F, A i j * v j :=
      Finset.sum_coe_sort F (fun j => A i j * v j)
    rw [h3]; simp only [hbp]; linarith
  intro j
  by_cases hj : j ∈ F
  swap
  · exact hnotF j hj
  choose zbp hzbp using hbp_int
  set w : F → ℝ := fun p => bp (a (e.symm p)) with hw
  have hMy : Msq.mulVec (fun t : F => v t.1) = w := by
    funext p
    simp only [Matrix.mulVec, dotProduct, Msq, Matrix.of_apply, hw]
    exact hAy _
  have key : (Msq.adjugate).mulVec w = Msq.det • (fun t : F => v t.1) := by
    rw [← hMy, Matrix.mulVec_mulVec, Matrix.adjugate_mul]
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  have hvj : v j = Msq.det * ((Msq.adjugate).mulVec w ⟨j, hj⟩) := by
    have := congrFun key ⟨j, hj⟩
    rw [this]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, hdetsq, one_mul]
  refine ⟨Zm.det * ∑ p, Zm.adjugate ⟨j, hj⟩ p * zbp (a (e.symm p)), ?_⟩
  rw [hvj, hdetZ, hadj]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hw]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [hzbp]
