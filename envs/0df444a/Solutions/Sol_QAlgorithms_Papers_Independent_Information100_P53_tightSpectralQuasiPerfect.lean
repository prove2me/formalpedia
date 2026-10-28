-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P53.tightSpectralQuasiPerfect
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T19:45:58.761196+00:00
-- url     : https://prove2.me/submissions/650f6932-533c-4be7-91aa-c8c72c837c9b

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53
noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder
open Finset
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P53

lemma p53ts_entry {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (hA : A.PosSemidef)
    (hd : ∀ a, (A a a).re ≤ 1) (a b : Fin N) : ‖A a b‖ ≤ 1 := by
  obtain ⟨m, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hA
  have hab : ∀ a b, A a b = ∑ k, v k a * star (v k b) := by
    intro a b; rw [hv]; simp [Matrix.sum_apply, Matrix.vecMulVec_apply]
  have hre : ∀ a, (A a a).re = ∑ k, ‖v k a‖ ^ 2 := by
    intro a
    rw [hab, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    norm_cast
  have h1 : ‖A a b‖ ≤ ∑ k, ‖v k a‖ * ‖v k b‖ := by
    rw [hab]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [norm_mul, Complex.star_def, Complex.norm_conj]
  have h2 : ∑ k, ‖v k a‖ * ‖v k b‖ ≤ ((A a a).re + (A b b).re) / 2 := by
    rw [hre, hre, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_le_sum fun k _ => ?_
    nlinarith [sq_nonneg (‖v k a‖ - ‖v k b‖)]
  linarith [hd a, hd b]

lemma p53ts_closed_psd {N : ℕ} : IsClosed {A : Matrix (Fin N) (Fin N) ℂ | A.PosSemidef} := by
  have : {A : Matrix (Fin N) (Fin N) ℂ | A.PosSemidef} =
      {A | Aᴴ = A} ∩ ⋂ x : Fin N → ℂ, {A | 0 ≤ star x ⬝ᵥ (A *ᵥ x)} := by
    ext A; simp [Matrix.posSemidef_iff_dotProduct_mulVec, Matrix.IsHermitian]
  rw [this]
  exact (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).inter
    (isClosed_iInter fun x => isClosed_le continuous_const
      (continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)))

lemma p53ts_box {N : ℕ} : IsCompact {A : Matrix (Fin N) (Fin N) ℂ | ∀ a b, ‖A a b‖ ≤ 1} := by
  have h : IsCompact (Set.univ.pi fun _ : Fin N => Set.univ.pi fun _ : Fin N =>
      Metric.closedBall (0:ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have e : {A : Matrix (Fin N) (Fin N) ℂ | ∀ a b, ‖A a b‖ ≤ 1} =
      (Set.univ.pi fun _ : Fin N => Set.univ.pi fun _ : Fin N => Metric.closedBall (0:ℂ) 1 :
        Set (Fin N → Fin N → ℂ)) := by
    ext A
    exact ⟨fun h a _ b _ => by simpa using h a b, fun h a b => by simpa using h a trivial b trivial⟩
  rw [e]; exact h

lemma p53ts_compact_density {N : ℕ} :
    IsCompact {μ : Matrix (Fin N) (Fin N) ℂ | IsDensityMatrix μ} := by
  refine p53ts_box.of_isClosed_subset ?_ ?_
  · have : {μ : Matrix (Fin N) (Fin N) ℂ | IsDensityMatrix μ} =
        {A | A.PosSemidef} ∩ {A | A.trace = 1} := rfl
    rw [this]
    exact p53ts_closed_psd.inter (isClosed_eq continuous_id.matrix_trace continuous_const)
  · intro μ hμ
    refine p53ts_entry μ hμ.1 fun a => ?_
    have h := congrArg Complex.re hμ.2
    rw [Matrix.trace, Complex.re_sum] at h
    simp only [Matrix.diag, Complex.one_re] at h
    rw [← h]
    exact Finset.single_le_sum (f := fun b => (μ b b).re)
      (fun b _ => (Complex.nonneg_iff.mp (hμ.1.diag_nonneg)).1) (Finset.mem_univ a)

lemma p53ts_compact_effect {N : ℕ} :
    IsCompact {E : Matrix (Fin N) (Fin N) ℂ | IsEffect E} := by
  refine p53ts_box.of_isClosed_subset ?_ ?_
  · have : {E : Matrix (Fin N) (Fin N) ℂ | IsEffect E} =
        {A | A.PosSemidef} ∩ (fun A => 1 - A) ⁻¹' {A | A.PosSemidef} := rfl
    rw [this]
    exact p53ts_closed_psd.inter (p53ts_closed_psd.preimage (continuous_const.sub continuous_id))
  · intro E hE
    refine p53ts_entry E hE.1 fun a => ?_
    have := (Complex.nonneg_iff.mp (hE.2.diag_nonneg (i := a))).1
    simp [Matrix.sub_apply, Matrix.one_apply] at this
    linarith
lemma p53ts_sum_psd {N : ℕ} {ι : Type*} (s : Finset ι) (A : ι → Matrix (Fin N) (Fin N) ℂ)
    (h : ∀ i, (A i).PosSemidef) : (∑ i ∈ s, A i).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Matrix.PosSemidef.zero
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact (h a).add ih

lemma p53ts_sqrt_psd {N : ℕ} (Y : Matrix (Fin N) (Fin N) ℂ) :
    (cfc Real.sqrt Y).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => Real.sqrt_nonneg t)

lemma p53ts_sqrt_mul_sqrt {N : ℕ} {Q : Matrix (Fin N) (Fin N) ℂ} (hQ : Q.PosSemidef) :
    cfc Real.sqrt Q * cfc Real.sqrt Q = Q := by
  have hnn : (0 : Matrix (Fin N) (Fin N) ℂ) ≤ Q := Matrix.nonneg_iff_posSemidef.mpr hQ
  rw [← cfc_mul Real.sqrt Real.sqrt Q]
  conv_rhs => rw [← cfc_id ℝ Q]
  apply cfc_congr
  intro t ht
  exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hnn ht)

lemma p53ts_tr_psd_mul {N : ℕ} {P Q : Matrix (Fin N) (Fin N) ℂ} (hP : P.PosSemidef)
    (hQ : Q.PosSemidef) : 0 ≤ (P * Q).trace.re := by
  have hR : (cfc Real.sqrt Q)ᴴ = cfc Real.sqrt Q := (p53ts_sqrt_psd Q).1.eq
  have h := (hP.conjTranspose_mul_mul_same (cfc Real.sqrt Q)).trace_nonneg
  rw [hR, Matrix.trace_mul_comm, ← Matrix.mul_assoc, p53ts_sqrt_mul_sqrt hQ,
    Matrix.trace_mul_comm] at h
  exact (Complex.nonneg_iff.mp h).1

lemma p53ts_unit {N : ℕ} (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (j : Fin N) :
    ∑ w, conj (b j w) * b j w = 1 := by
  have h := orthonormal_iff_ite.mp b.orthonormal j j
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  simp only [if_true] at h
  rw [← h]; simp [dotProduct, mul_comm]

lemma p53ts_psdP {N : ℕ} (v : EuclideanSpace ℂ (Fin N)) : (pureDensity v).PosSemidef := by
  have : pureDensity v = Matrix.vecMulVec (⇑v) (star ⇑v) := by
    ext x y; simp [pureDensity, Matrix.vecMulVec_apply]
  rw [this]; exact Matrix.posSemidef_vecMulVec_self_star _


lemma p53ts_povm_le {M N : ℕ} (D : Fin M → Matrix (Fin N) (Fin N) ℂ) (hD : IsPOVM D) (i : Fin M) :
    (1 - D i).PosSemidef := by
  have : 1 - D i = ∑ k ∈ Finset.univ.erase i, D k := by
    rw [← hD.2, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]; abel
  rw [this]; exact p53ts_sum_psd _ _ hD.1

lemma p53ts_ep_le {N : ℕ} {E ρ : Matrix (Fin N) (Fin N) ℂ} (hE : (1 - E).PosSemidef)
    (hρ : IsDensityMatrix ρ) : (E * ρ).trace.re ≤ 1 := by
  have := p53ts_tr_psd_mul hE hρ.1
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, hρ.2, Complex.sub_re, Complex.one_re] at this
  linarith

lemma p53ts_bdd {M N : ℕ} (p : Fin M → ℝ) (hp : IsPrior p)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) (hrho : ∀ i, IsDensityMatrix (rho i)) :
    BddAbove (Set.range fun D : {D : Fin M → Matrix (Fin N) (Fin N) ℂ // IsPOVM D} =>
      ∑ j, p j * effectProb (D.1 j) (rho j)) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨D, rfl⟩
  calc ∑ j, p j * effectProb (D.1 j) (rho j) ≤ ∑ j, p j * 1 :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
          (p53ts_ep_le (p53ts_povm_le D.1 D.2 j) (hrho j)) (hp.1 j)
    _ = 1 := by simp [hp.2]

lemma p53ts_le_opt {M N : ℕ} (p : Fin M → ℝ) (hp : IsPrior p)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) (hrho : ∀ i, IsDensityMatrix (rho i))
    (D : Fin M → Matrix (Fin N) (Fin N) ℂ) (hD : IsPOVM D) :
    ∑ j, p j * (D j * rho j).trace.re ≤ mixedOptSuccess p rho :=
  le_ciSup (f := fun D : {D : Fin M → Matrix (Fin N) (Fin N) ℂ // IsPOVM D} =>
      ∑ j, p j * effectProb (D.1 j) (rho j)) (p53ts_bdd p hp rho hrho) ⟨D, hD⟩

lemma p53ts_top {N : ℕ} (hN : 0 < N) (S : Matrix (Fin N) (Fin N) ℂ) (hS : S.PosSemidef) :
    ∃ (lam : ℝ) (v : EuclideanSpace ℂ (Fin N)), 0 ≤ lam ∧ ((lam : ℂ) • 1 - S).PosSemidef ∧
      IsDensityMatrix (pureDensity v) ∧ (S * pureDensity v).trace.re = lam := by
  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ hS.1.eigenvalues
    ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  set lam := hS.1.eigenvalues i0
  set U := hS.1.eigenvectorUnitary
  have hs := hS.1.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  have hUU : (U : Matrix (Fin N) (Fin N) ℂ) * star (U : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    Unitary.mul_star_self_of_mem U.2
  set v := hS.1.eigenvectorBasis i0
  refine ⟨lam, v, hS.eigenvalues_nonneg i0, ?_, ⟨p53ts_psdP v, ?_⟩, ?_⟩
  · have key : (lam : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - S =
        (U : Matrix (Fin N) (Fin N) ℂ) *
          Matrix.diagonal (fun i => ((lam - hS.1.eigenvalues i : ℝ) : ℂ)) * star (U : Matrix (Fin N) (Fin N) ℂ) := by
      have : Matrix.diagonal (fun i => ((lam - hS.1.eigenvalues i : ℝ) : ℂ)) =
          (lam : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - Matrix.diagonal (RCLike.ofReal ∘ hS.1.eigenvalues) := by
        ext a b
        by_cases h : a = b
        · subst h; simp [Matrix.diagonal_apply]
        · simp [Matrix.diagonal_apply, h]
      rw [this, Matrix.mul_sub, Matrix.sub_mul, ← hs, Matrix.mul_smul, Matrix.mul_one,
        Matrix.smul_mul, hUU]
    rw [key, Matrix.star_eq_conjTranspose]
    apply Matrix.PosSemidef.mul_mul_conjTranspose_same
    apply Matrix.PosSemidef.diagonal
    intro i
    simp only [Pi.zero_apply]
    exact Complex.zero_le_real.mpr (sub_nonneg.mpr (hi0 i (Finset.mem_univ i)))
  · have := p53ts_unit hS.1.eigenvectorBasis i0
    rw [Matrix.trace]
    simp only [Matrix.diag, pureDensity, Matrix.of_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  · have hv := hS.1.mulVec_eigenvectorBasis i0
    have : (S * pureDensity v).trace = star (⇑v) ⬝ᵥ (S *ᵥ ⇑v) := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pureDensity, Matrix.of_apply,
        dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      simp [Complex.star_def]; ring
    rw [this, hv]
    have hu := p53ts_unit hS.1.eigenvectorBasis i0
    simp only [dotProduct_smul, smul_eq_mul]
    have : star (⇑v) ⬝ᵥ ⇑v = 1 := by
      rw [← hu]; simp [dotProduct, Complex.star_def]; rfl
    rw [this]
    simp [lam]

lemma p53ts_bound_lam {M N : ℕ} (hM : 0 < M) (p : Fin M → ℝ) (hp : IsPrior p)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) (hrho : ∀ i, IsDensityMatrix (rho i))
    (E : Fin M → Matrix (Fin N) (Fin N) ℂ) (hE : ∀ i, IsEffect (E i)) (lam : ℝ) (hlam : 0 ≤ lam)
    (hS : ((lam : ℂ) • 1 - ∑ i, E i).PosSemidef) :
    ∑ i, p i * (E i * rho i).trace.re ≤ mixedOptSuccess p rho * lam := by
  rcases hlam.lt_or_eq with hpos | hzero
  · set S := ∑ i, E i
    let i0 : Fin M := ⟨0, hM⟩
    set D : Fin M → Matrix (Fin N) (Fin N) ℂ := fun i =>
      ((lam⁻¹ : ℝ) : ℂ) • E i + if i = i0 then 1 - ((lam⁻¹ : ℝ) : ℂ) • S else 0 with hDdef
    have hrest : (1 - ((lam⁻¹ : ℝ) : ℂ) • S).PosSemidef := by
      have : 1 - ((lam⁻¹ : ℝ) : ℂ) • S = ((lam⁻¹ : ℝ) : ℂ) • ((lam : ℂ) • 1 - S) := by
        rw [smul_sub, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hpos.ne', Complex.ofReal_one,
          one_smul]
      rw [this]
      exact hS.smul (Complex.zero_le_real.mpr (inv_nonneg.mpr hlam))
    have hD : IsPOVM D := by
      refine ⟨fun i => ?_, ?_⟩
      · refine ((hE i).1.smul (Complex.zero_le_real.mpr (inv_nonneg.mpr hlam))).add ?_
        split_ifs
        · exact hrest
        · exact Matrix.PosSemidef.zero
      · simp only [hDdef, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [← Finset.smul_sum]; abel
    have h1 := p53ts_le_opt p hp rho hrho D hD
    have h2 : lam⁻¹ * ∑ i, p i * (E i * rho i).trace.re ≤ ∑ j, p j * (D j * rho j).trace.re := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      simp only [hDdef, Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul,
        Complex.add_re, smul_eq_mul, Complex.re_ofReal_mul]
      have : 0 ≤ ((if i = i0 then 1 - ((lam⁻¹ : ℝ) : ℂ) • S else 0) * rho i).trace.re := by
        split_ifs
        · exact p53ts_tr_psd_mul hrest (hrho i).1
        · simp
      nlinarith [hp.1 i]
    have h3 : lam⁻¹ * ∑ i, p i * (E i * rho i).trace.re ≤ mixedOptSuccess p rho := h2.trans h1
    rw [inv_mul_le_iff₀ hpos] at h3
    linarith
  · subst hzero
    have hle : ∀ i, (E i * rho i).trace.re ≤ 0 := by
      intro i
      have h1 : (∑ j, E j - E i).PosSemidef := by
        have : ∑ j, E j - E i = ∑ j ∈ Finset.univ.erase i, E j := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]; abel
        rw [this]; exact p53ts_sum_psd _ _ fun j => (hE j).1
      have a1 := p53ts_tr_psd_mul h1 (hrho i).1
      have a2 := p53ts_tr_psd_mul hS (hrho i).1
      simp only [Complex.ofReal_zero, zero_smul, zero_sub, Matrix.neg_mul, Matrix.trace_neg,
        Complex.neg_re] at a2
      rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re] at a1
      linarith
    simp only [mul_zero]
    exact Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hp.1 i) (hle i)

lemma p53ts_affine {V : Type*} [AddCommGroup V] [Module ℝ V] (S : Set V) (hS : Convex ℝ S)
    (g : V → ℝ) (hg : ∀ x y : V, ∀ a b : ℝ, a + b = 1 → g (a • x + b • y) = a * g x + b * g y) :
    QuasiconvexOn ℝ S g ∧ QuasiconcaveOn ℝ S g := by
  have h1 : ConvexOn ℝ S g := ⟨hS, fun x _ y _ a b _ _ hab => by
    rw [hg x y a b hab]; simp [smul_eq_mul]⟩
  have h2 : ConcaveOn ℝ S g := ⟨hS, fun x _ y _ a b _ _ hab => by
    rw [hg x y a b hab]; simp [smul_eq_mul]⟩
  exact ⟨h1.quasiconvexOn, h2.quasiconcaveOn⟩

lemma p53ts_trre_lin {N : ℕ} (A x y : Matrix (Fin N) (Fin N) ℂ) (a b : ℝ) :
    (A * (a • x + b • y)).trace.re = a * (A * x).trace.re + b * (A * y).trace.re := by
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_smul, Complex.add_re, Complex.smul_re, Complex.smul_re, smul_eq_mul, smul_eq_mul]

lemma p53ts_trre_lin' {N : ℕ} (A x y : Matrix (Fin N) (Fin N) ℂ) (a b : ℝ) :
    ((a • x + b • y) * A).trace.re = a * (x * A).trace.re + b * (y * A).trace.re := by
  rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_smul, Complex.add_re, Complex.smul_re, Complex.smul_re, smul_eq_mul, smul_eq_mul]

lemma p53ts_cont {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) :
    Continuous fun x : Matrix (Fin N) (Fin N) ℂ => (A * x).trace.re :=
  Complex.continuous_re.comp ((continuous_const.matrix_mul continuous_id).matrix_trace)

lemma p53ts_cont' {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) :
    Continuous fun x : Matrix (Fin N) (Fin N) ℂ => (x * A).trace.re :=
  Complex.continuous_re.comp ((continuous_id.matrix_mul continuous_const).matrix_trace)

lemma p53ts_psd_comb {N : ℕ} {x y : Matrix (Fin N) (Fin N) ℂ} (hx : x.PosSemidef) (hy : y.PosSemidef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : (a • x + b • y).PosSemidef := by
  have ex : a • x = (a : ℂ) • x := (Complex.coe_smul a x).symm
  have ey : b • y = (b : ℂ) • y := (Complex.coe_smul b y).symm
  rw [ex, ey]
  exact (hx.smul (Complex.zero_le_real.mpr ha)).add (hy.smul (Complex.zero_le_real.mpr hb))

theorem p53ts_key {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (p : Fin M → ℝ) (hp : IsPrior p)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) (hrho : ∀ i, IsDensityMatrix (rho i)) :
    ∃ μ : Matrix (Fin N) (Fin N) ℂ, IsDensityMatrix μ ∧
      ∀ E : Fin M → Matrix (Fin N) (Fin N) ℂ, (∀ i, IsEffect (E i)) →
        ∑ i, p i * (E i * rho i).trace.re ≤ mixedOptSuccess p rho * ∑ i, (E i * μ).trace.re := by
  set s := mixedOptSuccess p rho with hs
  set X : Set (Matrix (Fin N) (Fin N) ℂ) := {μ | IsDensityMatrix μ} with hX
  set Y : Set (Fin M → Matrix (Fin N) (Fin N) ℂ) :=
    Set.univ.pi fun _ => {E | IsEffect E} with hY
  set f : Matrix (Fin N) (Fin N) ℂ → (Fin M → Matrix (Fin N) (Fin N) ℂ) → ℝ :=
    fun μ E => ∑ i, p i * (E i * rho i).trace.re - s * ∑ i, (E i * μ).trace.re with hf
  have cX : Convex ℝ X := by
    intro x hx y hy a b ha hb hab
    refine ⟨p53ts_psd_comb hx.1 hy.1 ha hb, ?_⟩
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hx.2, hy.2]
    rw [← Complex.coe_smul, ← Complex.coe_smul, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
      ← Complex.ofReal_add, hab, Complex.ofReal_one]
  have neX : X.Nonempty := by
    obtain ⟨_, v, -, -, hv, -⟩ := p53ts_top hN 0 Matrix.PosSemidef.zero
    exact ⟨_, hv⟩
  have kX : IsCompact X := p53ts_compact_density
  have cY : Convex ℝ Y := by
    refine convex_pi fun i _ => ?_
    intro x hx y hy a b ha hb hab
    refine ⟨p53ts_psd_comb hx.1 hy.1 ha hb, ?_⟩
    have : 1 - (a • x + b • y) = a • (1 - x) + b • (1 - y) := by
      have h1 : (1 : Matrix (Fin N) (Fin N) ℂ) = a • 1 + b • 1 := by rw [← add_smul, hab, one_smul]
      rw [smul_sub, smul_sub]
      conv_lhs => rw [h1]
      abel
    rw [this]
    exact p53ts_psd_comb hx.2 hy.2 ha hb
  have neY : Y.Nonempty := ⟨fun _ => 0, fun i _ => ⟨Matrix.PosSemidef.zero, by
    simpa using (Matrix.PosSemidef.one : (1 : Matrix (Fin N) (Fin N) ℂ).PosSemidef)⟩⟩
  have kY : IsCompact Y := isCompact_univ_pi fun _ => p53ts_compact_effect
  have contμ : ∀ E : Fin M → Matrix (Fin N) (Fin N) ℂ, Continuous fun μ => f μ E := by
    intro E
    exact continuous_const.sub (continuous_const.mul
      (continuous_finsetSum _ fun i _ => p53ts_cont (E i)))
  have contE : ∀ μ, Continuous fun E : Fin M → Matrix (Fin N) (Fin N) ℂ => f μ E := by
    intro μ
    exact (continuous_finsetSum _ fun i _ => continuous_const.mul
      ((p53ts_cont' (rho i)).comp (continuous_apply i))).sub
      (continuous_const.mul (continuous_finsetSum _ fun i _ =>
        (p53ts_cont' μ).comp (continuous_apply i)))
  have affμ : ∀ E, ∀ x y : Matrix (Fin N) (Fin N) ℂ, ∀ a b : ℝ, a + b = 1 →
      f (a • x + b • y) E = a * f x E + b * f y E := by
    intro E x y a b hab
    simp only [hf, p53ts_trre_lin, Finset.sum_add_distrib, ← Finset.mul_sum]
    linear_combination -(∑ i, p i * (E i * rho i).trace.re) * hab
  have affE : ∀ μ, ∀ x y : Fin M → Matrix (Fin N) (Fin N) ℂ, ∀ a b : ℝ, a + b = 1 →
      f μ (a • x + b • y) = a * f μ x + b * f μ y := by
    intro μ x y a b hab
    simp only [hf, Pi.add_apply, Pi.smul_apply, p53ts_trre_lin', mul_add, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    have e1 : ∀ i, p i * (a * (x i * rho i).trace.re) = a * (p i * (x i * rho i).trace.re) :=
      fun i => by ring
    have e2 : ∀ i, p i * (b * (y i * rho i).trace.re) = b * (p i * (y i * rho i).trace.re) :=
      fun i => by ring
    simp only [e1, e2, ← Finset.mul_sum]
    ring
  obtain ⟨μs, hμs, Es, hEs, hsad⟩ := Sion.exists_isSaddlePointOn (X := X) (Y := Y) (f := f)
    neX cX kX (fun E _ => (contμ E).continuousOn.lowerSemicontinuousOn)
    (fun E _ => (p53ts_affine X cX _ (affμ E)).1) cY neY kY
    (fun μ _ => (contE μ).continuousOn.upperSemicontinuousOn)
    (fun μ _ => (p53ts_affine Y cY _ (affE μ)).2)
  have hEs' : ∀ i, IsEffect (Es i) := fun i => hEs i (Set.mem_univ i)
  obtain ⟨lam, v, hlam, hlamS, hv, hvS⟩ :=
    p53ts_top hN (∑ i, Es i) (p53ts_sum_psd _ _ fun i => (hEs' i).1)
  have h0 : f (pureDensity v) Es ≤ 0 := by
    have hb := p53ts_bound_lam hM p hp rho hrho Es hEs' lam hlam hlamS
    simp only [hf]
    have : ∑ i, (Es i * pureDensity v).trace.re = lam := by
      rw [← hvS, ← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul]
    rw [this]; linarith
  refine ⟨μs, hμs, fun E hE => ?_⟩
  have := hsad (pureDensity v) hv E (fun i _ => hE i)
  simp only [hf] at this h0
  linarith

/-! ## block embeddings -/

def p53ts_V {M : ℕ} (N : ℕ) (i : Fin M) : Matrix (Fin M × Fin N) (Fin N) ℂ :=
  fun u b => if u = (i, b) then 1 else 0

lemma p53ts_VtV {M N : ℕ} (i j : Fin M) :
    (p53ts_V N i)ᴴ * p53ts_V N j = if i = j then 1 else 0 := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single (i, a)]
  · simp only [Matrix.conjTranspose_apply, p53ts_V, if_true, star_one, one_mul]
    by_cases h : i = j
    · subst h; by_cases hab : a = b
      · subst hab; simp
      · simp [Matrix.one_apply, Prod.ext_iff, hab]
    · simp [h, Prod.ext_iff]
  · intro x _ hx; simp [Matrix.conjTranspose_apply, p53ts_V, hx]
  · simp

lemma p53ts_conj_apply {M N : ℕ} (i j : Fin M) (A : Matrix (Fin N) (Fin N) ℂ)
    (u w : Fin M × Fin N) :
    (p53ts_V N i * A * (p53ts_V N j)ᴴ) u w = if u.1 = i ∧ w.1 = j then A u.2 w.2 else 0 := by
  obtain ⟨u1, u2⟩ := u
  obtain ⟨w1, w2⟩ := w
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, p53ts_V, Prod.ext_iff]
  by_cases h1 : u1 = i <;> by_cases h2 : w1 = j <;> simp [h1, h2, ite_and, eq_comm]

lemma p53ts_sumVV {M N : ℕ} : ∑ i : Fin M, p53ts_V N i * (1 : Matrix (Fin N) (Fin N) ℂ) * (p53ts_V N i)ᴴ = 1 := by
  ext u w
  rw [Matrix.sum_apply]
  simp only [p53ts_conj_apply, Matrix.one_apply]
  obtain ⟨u1, u2⟩ := u
  obtain ⟨w1, w2⟩ := w
  by_cases h : u1 = w1
  · subst h; simp [Prod.ext_iff]
  · simp [Prod.ext_iff, h]
    exact Finset.sum_eq_zero fun x _ => by
      rw [if_neg]; rintro ⟨h1, h2⟩; exact h (h1.trans h2.symm)

lemma p53ts_block {M N : ℕ} (p : Fin M → ℝ) (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) :
    blockEnsembleState p rho = ∑ i, p53ts_V N i * ((p i : ℂ) • rho i) * (p53ts_V N i)ᴴ := by
  ext u w
  rw [Matrix.sum_apply]
  simp only [p53ts_conj_apply, blockEnsembleState, Matrix.smul_apply, smul_eq_mul]
  by_cases h : u.1 = w.1
  · rw [if_pos h, Finset.sum_eq_single u.1]
    · simp [h]
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · rw [if_neg h]
    refine (Finset.sum_eq_zero fun i _ => ?_).symm
    split_ifs with h'
    · exact absurd (h'.1.trans h'.2.symm) h
    · rfl

lemma p53ts_comp {M N : ℕ} (μ : Matrix (Fin N) (Fin N) ℂ) :
    binaryComparisonState (M := M) μ =
      ∑ i : Fin M, p53ts_V N i * ((((1 / (M : ℝ) : ℝ)) : ℂ) • μ) * (p53ts_V N i)ᴴ := by
  ext u w
  rw [Matrix.sum_apply]
  simp only [p53ts_conj_apply, binaryComparisonState, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  by_cases h : u.1 = w.1
  · rw [Finset.sum_eq_single u.1]
    · simp [h]
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · simp only [h, if_false, mul_zero, zero_mul]
    refine (Finset.sum_eq_zero fun i _ => ?_).symm
    split_ifs with h'
    · exact absurd (h'.1.trans h'.2.symm) h
    · rfl

lemma p53ts_ep_blocks {M N : ℕ} (T : Matrix (Fin M × Fin N) (Fin M × Fin N) ℂ)
    (A : Fin M → Matrix (Fin N) (Fin N) ℂ) :
    effectProb T (∑ i, p53ts_V N i * A i * (p53ts_V N i)ᴴ) =
      ∑ i, ((p53ts_V N i)ᴴ * T * p53ts_V N i * A i).trace.re := by
  unfold effectProb
  rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc]

lemma p53ts_blk_eff {M N : ℕ} (T : Matrix (Fin M × Fin N) (Fin M × Fin N) ℂ) (hT : IsEffect T)
    (i : Fin M) : IsEffect ((p53ts_V N i)ᴴ * T * p53ts_V N i) := by
  refine ⟨hT.1.conjTranspose_mul_mul_same _, ?_⟩
  have : 1 - (p53ts_V N i)ᴴ * T * p53ts_V N i = (p53ts_V N i)ᴴ * (1 - T) * p53ts_V N i := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, p53ts_VtV, if_pos rfl]
  rw [this]; exact hT.2.conjTranspose_mul_mul_same _

lemma p53ts_TD {M N : ℕ} (D : Fin M → Matrix (Fin N) (Fin N) ℂ) (hD : IsPOVM D) :
    IsEffect (∑ i, p53ts_V N i * D i * (p53ts_V N i)ᴴ) ∧
      ∀ j, (p53ts_V N j)ᴴ * (∑ i, p53ts_V N i * D i * (p53ts_V N i)ᴴ) * p53ts_V N j = D j := by
  refine ⟨⟨?_, ?_⟩, fun j => ?_⟩
  · exact Matrix.posSemidef_sum _ fun i _ => (hD.1 i).mul_mul_conjTranspose_same _
  · have : 1 - ∑ i, p53ts_V N i * D i * (p53ts_V N i)ᴴ =
        ∑ i, p53ts_V N i * (1 - D i) * (p53ts_V N i)ᴴ := by
      conv_lhs => rw [← p53ts_sumVV (M := M) (N := N)]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.mul_sub, Matrix.sub_mul]
    rw [this]
    exact Matrix.posSemidef_sum _ fun i _ => (p53ts_povm_le D hD i).mul_mul_conjTranspose_same _
  · rw [Matrix.mul_sum, Matrix.sum_mul]
    simp_rw [← Matrix.mul_assoc, p53ts_VtV, Matrix.mul_assoc, p53ts_VtV]
    simp [ite_mul, mul_ite]

def p53ts_blk {M N : ℕ} (T : Matrix (Fin M × Fin N) (Fin M × Fin N) ℂ) (i : Fin M) :
    Matrix (Fin N) (Fin N) ℂ := (p53ts_V N i)ᴴ * T * p53ts_V N i

lemma p53ts_povm_ne {M N : ℕ} (hM : 0 < M) :
    Nonempty {D : Fin M → Matrix (Fin N) (Fin N) ℂ // IsPOVM D} := by
  let i0 : Fin M := ⟨0, hM⟩
  refine ⟨⟨fun j => if j = i0 then 1 else 0, ?_, ?_⟩⟩
  · intro j; dsimp only; split_ifs
    · exact Matrix.PosSemidef.one
    · exact Matrix.PosSemidef.zero
  · simp

lemma p53ts_opt_nonneg {M N : ℕ} (hM : 0 < M) (p : Fin M → ℝ) (hp : IsPrior p)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) (hrho : ∀ i, IsDensityMatrix (rho i)) :
    0 ≤ mixedOptSuccess p rho := by
  obtain ⟨D⟩ := p53ts_povm_ne (N := N) hM
  refine le_trans ?_ (p53ts_le_opt p hp rho hrho D.1 D.2)
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hp.1 j) (p53ts_tr_psd_mul (D.2.1 j) (hrho j).1)


open Matrix in
lemma p53ts_tr_sub_psd {A : Type*} [Fintype A] [DecidableEq A] (σ : Matrix A A ℂ)
    (hσ : σ.PosSemidef) : (σ.trace • (1 : Matrix A A ℂ) - σ).PosSemidef := by
  set U := hσ.1.eigenvectorUnitary
  have hs := hσ.1.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  set lam := hσ.1.eigenvalues
  have htr := hσ.1.trace_eq_sum_eigenvalues
  have hUU : (U : Matrix A A ℂ) * star (U : Matrix A A ℂ) = 1 := Unitary.mul_star_self_of_mem U.2
  have key : σ.trace • (1 : Matrix A A ℂ) - σ =
      (U : Matrix A A ℂ) * diagonal (fun i => ((∑ j, lam j - lam i : ℝ) : ℂ)) * star (U : Matrix A A ℂ) := by
    have : diagonal (fun i => ((∑ j, lam j - lam i : ℝ) : ℂ)) =
        σ.trace • (1 : Matrix A A ℂ) - diagonal (RCLike.ofReal ∘ lam) := by
      ext a b
      by_cases h : a = b
      · subst h; simp [htr, diagonal_apply]; rfl
      · simp [diagonal_apply, h]
    rw [this, Matrix.mul_sub, Matrix.sub_mul, ← hs, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      hUU]
  rw [key, Matrix.star_eq_conjTranspose]
  apply PosSemidef.mul_mul_conjTranspose_same
  apply PosSemidef.diagonal
  intro i
  simp only [Pi.zero_apply]
  apply Complex.zero_le_real.mpr
  have : lam i ≤ ∑ j, lam j :=
    Finset.single_le_sum (fun j _ => hσ.eigenvalues_nonneg j) (Finset.mem_univ i)
  linarith


lemma p53ts_tr_vv {N : ℕ} (x : Fin N → ℂ) (A : Matrix (Fin N) (Fin N) ℂ) :
    (Matrix.vecMulVec x (star x) * A).trace = star x ⬝ᵥ (A *ᵥ x) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply, dotProduct,
    Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

lemma p53ts_uprior {M : ℕ} (hM : 0 < M) : IsPrior (fun _ : Fin M => 1 / (M : ℝ)) := by
  refine ⟨fun _ => by positivity, ?_⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  field_simp

theorem p53ts_dual {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) (hrho : ∀ i, IsDensityMatrix (rho i)) :
    ∃ μ : Matrix (Fin N) (Fin N) ℂ, IsDensityMatrix μ ∧ ∀ i,
      (((mixedOptSuccess (fun _ : Fin M => 1 / (M : ℝ)) rho : ℝ) : ℂ) • μ -
        (((1 / (M : ℝ) : ℝ)) : ℂ) • rho i).PosSemidef := by
  obtain ⟨μ, hμ, hk⟩ := p53ts_key hM hN _ (p53ts_uprior hM) rho hrho
  refine ⟨μ, hμ, fun i => ?_⟩
  set s := mixedOptSuccess (fun _ : Fin M => 1 / (M : ℝ)) rho
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
      hμ.1.1.eq, (hrho i).1.1.eq]
    simp [Complex.star_def]
  · intro x
    set σ := Matrix.vecMulVec x (star x)
    have hσ : σ.PosSemidef := Matrix.posSemidef_vecMulVec_self_star x
    set r := σ.trace.re
    have hr : σ.trace = (r : ℂ) := by
      have h0 := hσ.trace_nonneg
      exact Complex.ext rfl (by simpa using ((Complex.nonneg_iff.mp h0).2).symm)
    have hr0 : 0 ≤ r := (Complex.nonneg_iff.mp hσ.trace_nonneg).1
    set c : ℝ := 1 / (r + 1)
    have hc : 0 < c := by positivity
    set E : Fin M → Matrix (Fin N) (Fin N) ℂ := fun j => if j = i then (c : ℂ) • σ else 0 with hE
    have hcσ : IsEffect ((c : ℂ) • σ) := by
      refine ⟨hσ.smul (Complex.zero_le_real.mpr hc.le), ?_⟩
      have : 1 - (c : ℂ) • σ = (c : ℂ) • (σ.trace • 1 - σ) + (c : ℂ) • 1 := by
        rw [hr, smul_sub, smul_smul, ← Complex.ofReal_mul]
        have : c * r = 1 - c := by simp only [c]; field_simp; ring
        rw [this, Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
        abel
      rw [this]
      exact ((p53ts_tr_sub_psd σ hσ).smul (Complex.zero_le_real.mpr hc.le)).add
        (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr hc.le))
    have hEe : ∀ j, IsEffect (E j) := by
      intro j; simp only [hE]; split_ifs
      · exact hcσ
      · exact ⟨Matrix.PosSemidef.zero, by simpa using
          (Matrix.PosSemidef.one : (1 : Matrix (Fin N) (Fin N) ℂ).PosSemidef)⟩
    have h := hk E hEe
    simp only [hE, ite_mul, zero_mul, Finset.mul_sum] at h
    simp only [apply_ite, Matrix.trace_zero, Complex.zero_re, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
      Complex.re_ofReal_mul, p53ts_tr_vv] at h
    have hq1 := (hμ.1.1).im_star_dotProduct_mulVec_self x
    have hq2 := ((hrho i).1.1).im_star_dotProduct_mulVec_self x
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul,
      dotProduct_smul, Complex.nonneg_iff]
    simp only [RCLike.im_to_complex] at hq1 hq2
    constructor
    · simp only [smul_eq_mul, Complex.sub_re, Complex.re_ofReal_mul]
      have hs0 : (1 / (M : ℝ)) * (c * (star x ⬝ᵥ rho i *ᵥ x).re) ≤
          s * (c * (star x ⬝ᵥ μ *ᵥ x).re) := by
        rw [← p53ts_tr_vv, ← p53ts_tr_vv]; exact h
      have : c * ((1 / (M : ℝ)) * (star x ⬝ᵥ rho i *ᵥ x).re) ≤ c * (s * (star x ⬝ᵥ μ *ᵥ x).re) := by
        linarith
      have := le_of_mul_le_mul_left this hc
      linarith
    · simp only [smul_eq_mul, Complex.sub_im, Complex.im_ofReal_mul, hq1, hq2]; simp

lemma p53ts_attain {M N : ℕ} (hM : 0 < M) (p : Fin M → ℝ) (hp : IsPrior p)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) (hrho : ∀ i, IsDensityMatrix (rho i)) :
    ∃ D : Fin M → Matrix (Fin N) (Fin N) ℂ, IsPOVM D ∧
      ∑ j, p j * (D j * rho j).trace.re = mixedOptSuccess p rho := by
  set P : Set (Fin M → Matrix (Fin N) (Fin N) ℂ) := {D | IsPOVM D} with hP
  have hcl : IsClosed P := by
    have : P = (⋂ i, (fun D : Fin M → Matrix (Fin N) (Fin N) ℂ => D i) ⁻¹'
        {A | A.PosSemidef}) ∩ {D | ∑ i, D i = 1} := by
      ext D; simp [hP, IsPOVM, Set.mem_iInter]
    rw [this]
    exact (isClosed_iInter fun i => p53ts_closed_psd.preimage (continuous_apply i)).inter
      (isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)
  have hK : IsCompact P := (isCompact_univ_pi fun _ => p53ts_compact_effect).of_isClosed_subset hcl
    (fun D hD i _ => ⟨hD.1 i, p53ts_povm_le D hD i⟩)
  obtain ⟨D0⟩ := p53ts_povm_ne (N := N) hM
  have hcont : Continuous fun D : Fin M → Matrix (Fin N) (Fin N) ℂ =>
      ∑ j, p j * (D j * rho j).trace.re :=
    continuous_finsetSum _ fun j _ => continuous_const.mul
      ((p53ts_cont' (rho j)).comp (continuous_apply j))
  obtain ⟨D, hD, hmax⟩ := hK.exists_isMaxOn ⟨D0.1, D0.2⟩ hcont.continuousOn
  refine ⟨D, hD, le_antisymm (p53ts_le_opt p hp rho hrho D hD) ?_⟩
  have := p53ts_povm_ne (N := N) hM
  unfold mixedOptSuccess
  exact ciSup_le fun E => isMaxOn_iff.mp hmax E.1 E.2

lemma p53ts_tr_zero {N : ℕ} {A B : Matrix (Fin N) (Fin N) ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) (h : (A * B).trace.re = 0) : A * B = 0 := by
  set a := cfc Real.sqrt A
  set b := cfc Real.sqrt B
  have ha : a * a = A := p53ts_sqrt_mul_sqrt hA
  have hb : b * b = B := p53ts_sqrt_mul_sqrt hB
  have haH : aᴴ = a := (p53ts_sqrt_psd A).1.eq
  have hbH : bᴴ = b := (p53ts_sqrt_psd B).1.eq
  have hC : (a * b)ᴴ * (a * b) = b * A * b := by
    rw [Matrix.conjTranspose_mul, haH, hbH, ← ha]; simp only [Matrix.mul_assoc]
  have htr : ((a * b)ᴴ * (a * b)).trace = (A * B).trace := by
    rw [hC, Matrix.trace_mul_comm (b * A) b, ← Matrix.mul_assoc, hb, Matrix.trace_mul_comm]
  have h0 : ((a * b)ᴴ * (a * b)).trace = 0 := by
    have hn := (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self (a * b)).trace_nonneg)
    apply Complex.ext
    · rw [htr, h]; simp
    · simpa using hn.2.symm
  have hz := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp h0
  rw [← ha, ← hb]
  calc a * a * (b * b) = a * (a * b) * b := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hz]; simp

lemma p53ts_pos_zero {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (hA : (-A).PosSemidef) :
    positiveProjector A = 0 := by
  unfold positiveProjector
  have hs : ∀ x ∈ spectrum ℝ A, x ≤ 0 := by
    intro x hx
    have h1 : -x ∈ spectrum ℝ (-A) := by
      rw [← spectrum.neg_eq]; exact Set.neg_mem_neg.mpr hx
    have := spectrum_nonneg_of_nonneg (Matrix.nonneg_iff_posSemidef.mpr hA) h1
    linarith
  rw [cfc_congr (g := (0 : ℝ → ℝ)) (fun x hx => by simp [not_lt.mpr (hs x hx)]), cfc_zero]

lemma p53ts_ker {N : ℕ} (A D : Matrix (Fin N) (Fin N) ℂ) (hA : A.IsHermitian) (hAD : A * D = 0) :
    kernelProjector A * D = D ∧ (kernelProjector A)ᴴ = kernelProjector A ∧
      kernelProjector A * kernelProjector A = kernelProjector A := by
  have hsa : IsSelfAdjoint A := hA
  have hfin : (spectrum ℝ A).Finite := Set.toFinite _
  set h : ℝ → ℝ := fun x => if x = 0 then 0 else x⁻¹
  have hg : (fun x : ℝ => if x = 0 then (1 : ℝ) else 0) = fun x => 1 - h x * x := by
    funext x; by_cases hx : x = 0
    · simp [h, hx]
    · simp [h, hx]
  have hK : kernelProjector A = 1 - cfc h A * A := by
    unfold kernelProjector
    rw [hg, cfc_sub (f := fun _ => (1 : ℝ)) (g := fun x => h x * x) (a := A)
      (hf := hfin.continuousOn _) (hg := hfin.continuousOn _), cfc_const_one (R := ℝ) (a := A),
      cfc_mul (f := h) (g := fun x => x) (a := A) (hf := hfin.continuousOn _)
        (hg := hfin.continuousOn _), cfc_id' ℝ A]
  refine ⟨?_, ?_, ?_⟩
  · rw [hK, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hAD, Matrix.mul_zero, sub_zero]
  · exact (cfc_predicate (R := ℝ) _ A : IsSelfAdjoint _)
  · unfold kernelProjector
    rw [← cfc_mul (a := A) (hf := hfin.continuousOn _) (hg := hfin.continuousOn _)]
    apply cfc_congr
    intro x _
    by_cases hx : x = 0 <;> simp [hx]

theorem p53ts_qp {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) (hrho : ∀ i, IsDensityMatrix (rho i)) :
    IsQuasiPerfect rho := by
  obtain ⟨μ, hμ, hdual⟩ := p53ts_dual hM hN rho hrho
  set u : Fin M → ℝ := fun _ => 1 / (M : ℝ) with hu
  set s := mixedOptSuccess u rho with hs
  obtain ⟨D, hD, hDopt⟩ := p53ts_attain hM u (p53ts_uprior hM) rho hrho
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  set Y : Fin M → Matrix (Fin N) (Fin N) ℂ :=
    fun i => (s : ℂ) • μ - (((1 / (M : ℝ) : ℝ)) : ℂ) • rho i with hY
  have hYpsd : ∀ i, (Y i).PosSemidef := hdual
  -- complementary slackness
  have hsum : ∑ i, (D i * Y i).trace.re = 0 := by
    simp only [hY, Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul,
      Complex.sub_re, smul_eq_mul, Complex.re_ofReal_mul, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, ← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, hD.2,
      Matrix.one_mul, hμ.2, Complex.one_re, mul_one]
    have : ∑ i, 1 / (M : ℝ) * (D i * rho i).trace.re = s := hDopt
    rw [this]; ring
  have hterm : ∀ i, (D i * Y i).trace.re = 0 := by
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ (D i * Y i).trace.re :=
      fun i _ => p53ts_tr_psd_mul (hD.1 i) (hYpsd i)
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum i (Finset.mem_univ i)
  have hYD : ∀ i, Y i * D i = 0 := by
    intro i
    have h := p53ts_tr_zero (hD.1 i) (hYpsd i) (hterm i)
    have := congrArg Matrix.conjTranspose h
    rwa [Matrix.conjTranspose_mul, (hYpsd i).1.eq, (hD.1 i).1.eq, Matrix.conjTranspose_zero] at this
  -- the quasi-perfect parameters
  set t : ℝ := M * s
  have hA : ∀ i, -(rho i - (t : ℂ) • μ) = (M : ℂ) • Y i := by
    intro i
    simp only [hY, smul_sub, smul_smul]
    have h1 : (M : ℂ) * (((1 / (M : ℝ) : ℝ)) : ℂ) = 1 := by
      push_cast; field_simp
    rw [h1, one_smul]
    simp only [t]; push_cast
    abel
  have hApsd : ∀ i, (-(rho i - (t : ℂ) • μ)).PosSemidef := by
    intro i; rw [hA]
    exact (hYpsd i).smul (by exact_mod_cast (Nat.cast_nonneg M : (0:ℝ) ≤ M))
  have hAH : ∀ i, (rho i - (t : ℂ) • μ).IsHermitian := by
    intro i
    have := (hApsd i).1
    simpa using this.neg
  have hAD : ∀ i, (rho i - (t : ℂ) • μ) * D i = 0 := by
    intro i
    have : rho i - (t : ℂ) • μ = -((M : ℂ) • Y i) := by rw [← hA, neg_neg]
    rw [this, Matrix.neg_mul, Matrix.smul_mul, hYD, smul_zero, neg_zero]
  have hpos : ∀ i, positiveProjector (rho i - (t : ℂ) • μ) = 0 :=
    fun i => p53ts_pos_zero _ (hApsd i)
  refine ⟨μ, t, hμ, fun i j _ => by rw [hpos i, hpos j, Matrix.zero_mul], ?_⟩
  simp only [hpos, zero_add]
  have : ∑ i, kernelProjector (rho i - (t : ℂ) • μ) - 1 =
      ∑ i, (kernelProjector (rho i - (t : ℂ) • μ) - D i) := by
    rw [Finset.sum_sub_distrib, hD.2]
  rw [this]
  refine Matrix.posSemidef_sum _ fun i _ => ?_
  obtain ⟨hKD, hKH, hKK⟩ := p53ts_ker _ (D i) (hAH i) (hAD i)
  set K := kernelProjector (rho i - (t : ℂ) • μ)
  have hDK : D i * K = D i := by
    have := congrArg Matrix.conjTranspose hKD
    rwa [Matrix.conjTranspose_mul, hKH, (hD.1 i).1.eq] at this
  have : K - D i = K * (1 - D i) * Kᴴ := by
    rw [hKH, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hKK, Matrix.mul_assoc, hDK, hKD]
  rw [this]
  exact (p53ts_povm_le D hD i).mul_mul_conjTranspose_same K

end

theorem solution {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (p : Fin M → ℝ) (hp : QAlgorithms.Papers.Independent.Information100.P53.IsPrior p)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) (hrho : ∀ i, QAlgorithms.IsDensityMatrix (rho i))
    (s : ∀ i, QAlgorithms.Papers.Independent.Information100.P53.SpectralData (rho i))
    (I : Finset (Fin M × Fin N))
    (hI : QAlgorithms.Papers.Independent.Information100.P53.IsTopSelection N
      (QAlgorithms.Papers.Independent.Information100.P53.spectralWeight p s) I)
    (htight : QAlgorithms.mixedOptSuccess p rho =
      ∑ z ∈ I, QAlgorithms.Papers.Independent.Information100.P53.spectralWeight p s z) :
    QAlgorithms.Papers.Independent.Information100.P53.IsQuasiPerfect rho :=
  p53ts_qp hM hN rho hrho

