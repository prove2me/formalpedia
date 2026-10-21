-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P18.squeeze_projection_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @Imine
-- created : 2026-10-20T17:42:04.271736+00:00
-- url     : https://prove2.me/submissions/096ec850-cef6-4bfc-9f99-6b6693db3df9

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P18

noncomputable section

open Filter MeasureTheory

open scoped ENNReal Topology BigOperators ComplexOrder BoundedContinuousFunction Matrix

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Frontier18.P01
  (Channel homogeneousEntropy mutualInformation boundedConjugation traceFirst traceSecond)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff)

open QAlgorithms.Papers.Independent.Frontier30.P10 (HilbertPOVM)

open QAlgorithms.Papers.Independent.Claimed50.P35
  (ScaledWeylRepresentation InterleavedPhase physicalCommutationMatrix
   gaussianFunction weylTraceCharacteristic tracePair)

open QAlgorithms.Papers.Independent.Claimed50.P13
  (PositiveObservable zeroObservable feasibleStates informationSupremum
   operationalAssistedCapacity regularizedUnassistedCapacity)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex quantumCovariance)

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-- The interleaved symplectic form, abbreviated for readability. -/
private abbrev iDelta (s : ℕ) : Matrix (QuadratureIndex s) (QuadratureIndex s) ℝ :=
  QAlgorithms.Papers.Independent.Frontier30.P08.interleavedSymplecticForm s

private lemma delta_transpose (s : ℕ) : (iDelta s).transpose = -(iDelta s) := by
  ext i j
  obtain ⟨i1, i2⟩ := i
  obtain ⟨j1, j2⟩ := j
  simp only [iDelta, QAlgorithms.Papers.Independent.Frontier30.P08.interleavedSymplecticForm,
    Matrix.transpose_apply, Matrix.neg_apply]
  by_cases h : i1 = j1
  · subst h
    fin_cases i2 <;> fin_cases j2 <;> simp
  · have h' : j1 ≠ i1 := fun hh => h hh.symm
    simp [h, h']

private lemma delta_sq (s : ℕ) : iDelta s * iDelta s = -1 := by
  ext i j
  obtain ⟨i1, i2⟩ := i
  obtain ⟨j1, j2⟩ := j
  rw [Matrix.mul_apply, ← Finset.univ_product_univ, Finset.sum_product]
  by_cases h : i1 = j1
  · subst h
    rw [Finset.sum_eq_single i1]
    · fin_cases i2 <;> fin_cases j2 <;>
        simp [iDelta, QAlgorithms.Papers.Independent.Frontier30.P08.interleavedSymplecticForm,
          Fin.sum_univ_two, Matrix.neg_apply]
    · intro x _ hx
      have hx' : i1 ≠ x := fun hh => hx hh.symm
      rw [Finset.sum_eq_zero]
      intro a _
      simp [iDelta, QAlgorithms.Papers.Independent.Frontier30.P08.interleavedSymplecticForm, hx']
    · intro hh
      exact absurd (Finset.mem_univ i1) hh
  · have hzero : ∀ k : QuadratureIndex s,
        iDelta s (i1, i2) k * iDelta s k (j1, j2) = 0 := by
      intro k
      obtain ⟨x, a⟩ := k
      by_cases hx : i1 = x
      · have hxj : ¬ x = j1 := fun hh => h (hx.trans hh)
        simp [iDelta, QAlgorithms.Papers.Independent.Frontier30.P08.interleavedSymplecticForm,
          hx, hxj]
      · simp [iDelta, QAlgorithms.Papers.Independent.Frontier30.P08.interleavedSymplecticForm, hx]
    rw [Finset.sum_eq_zero]
    · simp [Matrix.neg_apply, h]
    · intro x _
      rw [Finset.sum_eq_zero]
      intro y _
      exact hzero (x, y)

private lemma squeeze_real {s : ℕ} (P Q R : Matrix (QuadratureIndex s) (QuadratureIndex s) ℝ)
    (hPsym : P.IsSymm) (hQsym : Q.IsSymm) (hRsym : R.IsSymm)
    (hPid : P * P = P) (hQid : Q * Q = Q) (hRid : R * R = R)
    (hPQ : P * Q = 0) (hPR : P * R = 0) (hQR : Q * R = 0)
    (hsum : P + Q + R = 1)
    (hQ : Q = -(iDelta s) * P * (iDelta s))
    (n : ℕ) (hn : 0 < n) :
    ∃ S : Matrix (QuadratureIndex s) (QuadratureIndex s) ℝ,
      S.IsSymm ∧ S * S = (1/(n:ℝ)) • P + (n:ℝ) • Q + R ∧ S * iDelta s * S = iDelta s := by
  have hQP : Q * P = 0 := by
    have h := congrArg Matrix.transpose hPQ
    simpa [Matrix.transpose_mul, hPsym.eq, hQsym.eq] using h
  have hRP : R * P = 0 := by
    have h := congrArg Matrix.transpose hPR
    simpa [Matrix.transpose_mul, hPsym.eq, hRsym.eq] using h
  have hRQ : R * Q = 0 := by
    have h := congrArg Matrix.transpose hQR
    simpa [Matrix.transpose_mul, hQsym.eq, hRsym.eq] using h
  have hΔ2 : iDelta s * iDelta s = -1 := delta_sq s
  have hQ' : Q = -(iDelta s * P * iDelta s) := by rw [hQ]; simp only [Matrix.neg_mul]
  have hQΔ : Q * iDelta s = iDelta s * P := by
    rw [hQ', Matrix.neg_mul]
    simp only [Matrix.mul_assoc]
    rw [hΔ2]
    simp
  have hΔQ : iDelta s * Q = P * iDelta s := by
    rw [hQ', Matrix.mul_neg]
    simp only [← Matrix.mul_assoc]
    rw [hΔ2]
    simp
  have hR : R = 1 - P - Q := by
    rw [← hsum]
    abel
  have hΔR : iDelta s * R = R * iDelta s := by
    have h1 : iDelta s * R = iDelta s - Q * iDelta s - iDelta s * Q := by
      rw [hR, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← hQΔ]
    have h2 : R * iDelta s = iDelta s - iDelta s * Q - Q * iDelta s := by
      rw [hR, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, ← hΔQ]
    rw [h1, h2]
    abel
  have hn' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  set a : ℝ := 1 / Real.sqrt (n : ℝ) with ha
  set b : ℝ := Real.sqrt (n : ℝ) with hb
  have hbpos : 0 < b := by rw [hb]; exact Real.sqrt_pos.mpr hn'
  have hbb : b * b = (n:ℝ) := by rw [hb]; exact Real.mul_self_sqrt (le_of_lt hn')
  have hab : a * b = 1 := by
    rw [ha]
    field_simp
  have hba : b * a = 1 := by rw [mul_comm, hab]
  have haa : a * a = 1 / (n:ℝ) := by
    have h : a * a = 1 / (b * b) := by
      rw [ha]
      field_simp
    rw [h, hbb]
  refine ⟨a • P + b • Q + R, ?_, ?_, ?_⟩
  · exact (hPsym.smul a).add (hQsym.smul b) |>.add hRsym
  · simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    simp [hPid, hQid, hRid, hPQ, hQP, hPR, hRP, hQR, hRQ, haa, hbb, smul_smul]
  · have h1 : (a • P + b • Q + R) * iDelta s =
        a • (iDelta s * Q) + b • (iDelta s * P) + iDelta s * R := by
      simp only [Matrix.add_mul, Matrix.smul_mul]
      rw [← hΔQ, ← hQΔ, ← hΔR]
    rw [h1]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    simp [Matrix.mul_assoc, hPid, hQid, hRid, hPQ, hQP, hPR, hRP, hQR, hRQ,
      smul_smul, hab, hba]
    rw [← Matrix.mul_add, ← Matrix.mul_add, hsum, Matrix.mul_one]

/-- The paper's block-diagonal squeezed covariance is a physical covariance.
`P`, `Q = -Delta P Delta` and `R` are the three mutually orthogonal projections
of the projection decomposition; `n` is the squeezing parameter. -/
theorem solution {s : ℕ}
    (P Q R : Matrix (QuadratureIndex s) (QuadratureIndex s) ℝ)
    (hPsym : P.IsSymm) (hQsym : Q.IsSymm) (hRsym : R.IsSymm)
    (hPid : P * P = P) (hQid : Q * Q = Q) (hRid : R * R = R)
    (hPQ : P * Q = 0) (hPR : P * R = 0) (hQR : Q * R = 0)
    (hsum : P + Q + R = 1)
    (hQ : Q = -(QAlgorithms.Papers.Independent.Frontier30.P08.interleavedSymplecticForm s) * P *
      (QAlgorithms.Papers.Independent.Frontier30.P08.interleavedSymplecticForm s))
    (n : ℕ) (hn : 0 < n) :
    (((1 / (n : ℝ)) • P + (n : ℝ) • Q + R).map (fun x : ℝ => (x : ℂ)) +
      Complex.I • (QAlgorithms.Papers.Independent.Frontier30.P08.interleavedSymplecticForm s).map
        (fun x : ℝ => (x : ℂ))).PosSemidef := by
  obtain ⟨S, hSsym, hS2, hSΔS⟩ :=
    squeeze_real P Q R hPsym hQsym hRsym hPid hQid hRid hPQ hPR hQR hsum hQ n hn
  set Sc : Matrix (QuadratureIndex s) (QuadratureIndex s) ℂ := S.map Complex.ofRealHom with hSc
  set Dc : Matrix (QuadratureIndex s) (QuadratureIndex s) ℂ :=
    (iDelta s).map Complex.ofRealHom with hDc
  have hScHerm : Scᴴ = Sc := by
    have h : S.IsHermitian := by simpa using hSsym
    have hh : (S.map Complex.ofRealHom).IsHermitian :=
      h.map Complex.ofRealHom (fun x => (Complex.conj_ofReal x).symm)
    simpa [hSc, Matrix.IsHermitian] using hh
  have hDcHerm : Dcᴴ = -Dc := by
    ext i j
    have h1 : (iDelta s) j i = -((iDelta s) i j) := by
      have h := congrFun (congrFun (delta_transpose s) i) j
      simpa [Matrix.transpose_apply] using h
    have h2 : star (Complex.ofRealHom ((iDelta s) i j)) = Complex.ofRealHom ((iDelta s) i j) :=
      Complex.conj_ofReal _
    rw [hDc]
    change star (Complex.ofRealHom ((iDelta s) j i)) = -Complex.ofRealHom ((iDelta s) i j)
    rw [h1, map_neg, star_neg, h2]
  have hDc2 : Dc * Dc = -1 := by
    rw [hDc, ← Matrix.map_mul, delta_sq s]
    ext i j
    change Complex.ofRealHom ((-1 : Matrix (QuadratureIndex s) (QuadratureIndex s) ℝ) i j)
      = (-1 : Matrix (QuadratureIndex s) (QuadratureIndex s) ℂ) i j
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  have hOnePlus : ((1 : Matrix (QuadratureIndex s) (QuadratureIndex s) ℂ) +
      Complex.I • Dc).PosSemidef := by
    have hII1 : Complex.I • Complex.I • (1 : Matrix (QuadratureIndex s) (QuadratureIndex s) ℂ)
        = -(1 : Matrix (QuadratureIndex s) (QuadratureIndex s) ℂ) := by
      rw [smul_smul (M := ℂ), Complex.I_mul_I, neg_smul, one_smul]
    have hX2 : ((1 : Matrix (QuadratureIndex s) (QuadratureIndex s) ℂ) + Complex.I • Dc) *
        ((1 : Matrix (QuadratureIndex s) (QuadratureIndex s) ℂ) + Complex.I • Dc)
        = (2:ℝ) • ((1 : Matrix (QuadratureIndex s) (QuadratureIndex s) ℂ) + Complex.I • Dc) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.one_mul,
        Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_neg, hDc2]
      rw [smul_smul (M := ℂ), Complex.I_mul_I]
      module
    have hHerm : ((1 : Matrix (QuadratureIndex s) (QuadratureIndex s) ℂ) +
        Complex.I • Dc)ᴴ = ((1 : Matrix (QuadratureIndex s) (QuadratureIndex s) ℂ) +
        Complex.I • Dc) := by
      simp [hDcHerm, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
        Matrix.conjTranspose_one]
    set Pplus : Matrix (QuadratureIndex s) (QuadratureIndex s) ℂ :=
      (1/2 : ℝ) • ((1 : Matrix (QuadratureIndex s) (QuadratureIndex s) ℂ) + Complex.I • Dc)
      with hPplus
    have hPplusHerm : Pplusᴴ = Pplus := by
      rw [hPplus, Matrix.conjTranspose_smul, hHerm]
      norm_num
    have hPplusIdem : Pplus * Pplus = Pplus := by
      rw [hPplus, Matrix.smul_mul, Matrix.mul_smul, smul_smul (M := ℝ), hX2,
        smul_smul (M := ℝ)]
      norm_num
    have hPplusPSD : Pplus.PosSemidef := by
      have h : Pplus = Pplusᴴ * Pplus := by rw [hPplusHerm, hPplusIdem]
      rw [h]
      exact Matrix.posSemidef_conjTranspose_mul_self Pplus
    have h2 : ((1 : Matrix (QuadratureIndex s) (QuadratureIndex s) ℂ) + Complex.I • Dc)
        = (2:ℝ) • Pplus := by
      rw [hPplus, smul_smul (M := ℝ)]
      norm_num
    rw [h2]
    exact hPplusPSD.smul (by norm_num : (0:ℝ) ≤ 2)
  have hScSq : Sc * Sc = ((1/(n:ℝ)) • P + (n:ℝ) • Q + R).map Complex.ofRealHom := by
    rw [hSc, ← Matrix.map_mul, hS2]
  have hScD : Sc * Dc * Sc = Dc := by
    rw [hSc, hDc, ← Matrix.map_mul, ← Matrix.map_mul, hSΔS]
  have hAeq : Scᴴ * ((1 : Matrix (QuadratureIndex s) (QuadratureIndex s) ℂ) +
      Complex.I • Dc) * Sc
      = (((1/(n:ℝ)) • P + (n:ℝ) • Q + R).map (fun x : ℝ => (x : ℂ)) +
      Complex.I • (iDelta s).map (fun x : ℝ => (x : ℂ))) := by
    rw [hScHerm, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.add_mul,
      Matrix.smul_mul, hScSq, hScD]
    rfl
  rw [← hAeq]
  exact hOnePlus.conjTranspose_mul_mul_same Sc

end
