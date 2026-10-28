-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P53.binaryTestingCharacterization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T19:45:29.638389+00:00
-- url     : https://prove2.me/submissions/6f84361e-5db2-4255-9bfc-0de007d3b7c9

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53
noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder
open Finset
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P53

lemma p53bt_entry {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (hA : A.PosSemidef)
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

lemma p53bt_closed_psd {N : ℕ} : IsClosed {A : Matrix (Fin N) (Fin N) ℂ | A.PosSemidef} := by
  have : {A : Matrix (Fin N) (Fin N) ℂ | A.PosSemidef} =
      {A | Aᴴ = A} ∩ ⋂ x : Fin N → ℂ, {A | 0 ≤ star x ⬝ᵥ (A *ᵥ x)} := by
    ext A; simp [Matrix.posSemidef_iff_dotProduct_mulVec, Matrix.IsHermitian]
  rw [this]
  exact (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).inter
    (isClosed_iInter fun x => isClosed_le continuous_const
      (continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)))

lemma p53bt_box {N : ℕ} : IsCompact {A : Matrix (Fin N) (Fin N) ℂ | ∀ a b, ‖A a b‖ ≤ 1} := by
  have h : IsCompact (Set.univ.pi fun _ : Fin N => Set.univ.pi fun _ : Fin N =>
      Metric.closedBall (0:ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have e : {A : Matrix (Fin N) (Fin N) ℂ | ∀ a b, ‖A a b‖ ≤ 1} =
      (Set.univ.pi fun _ : Fin N => Set.univ.pi fun _ : Fin N => Metric.closedBall (0:ℂ) 1 :
        Set (Fin N → Fin N → ℂ)) := by
    ext A
    exact ⟨fun h a _ b _ => by simpa using h a b, fun h a b => by simpa using h a trivial b trivial⟩
  rw [e]; exact h

lemma p53bt_compact_density {N : ℕ} :
    IsCompact {μ : Matrix (Fin N) (Fin N) ℂ | IsDensityMatrix μ} := by
  refine p53bt_box.of_isClosed_subset ?_ ?_
  · have : {μ : Matrix (Fin N) (Fin N) ℂ | IsDensityMatrix μ} =
        {A | A.PosSemidef} ∩ {A | A.trace = 1} := rfl
    rw [this]
    exact p53bt_closed_psd.inter (isClosed_eq continuous_id.matrix_trace continuous_const)
  · intro μ hμ
    refine p53bt_entry μ hμ.1 fun a => ?_
    have h := congrArg Complex.re hμ.2
    rw [Matrix.trace, Complex.re_sum] at h
    simp only [Matrix.diag, Complex.one_re] at h
    rw [← h]
    exact Finset.single_le_sum (f := fun b => (μ b b).re)
      (fun b _ => (Complex.nonneg_iff.mp (hμ.1.diag_nonneg)).1) (Finset.mem_univ a)

lemma p53bt_compact_effect {N : ℕ} :
    IsCompact {E : Matrix (Fin N) (Fin N) ℂ | IsEffect E} := by
  refine p53bt_box.of_isClosed_subset ?_ ?_
  · have : {E : Matrix (Fin N) (Fin N) ℂ | IsEffect E} =
        {A | A.PosSemidef} ∩ (fun A => 1 - A) ⁻¹' {A | A.PosSemidef} := rfl
    rw [this]
    exact p53bt_closed_psd.inter (p53bt_closed_psd.preimage (continuous_const.sub continuous_id))
  · intro E hE
    refine p53bt_entry E hE.1 fun a => ?_
    have := (Complex.nonneg_iff.mp (hE.2.diag_nonneg (i := a))).1
    simp [Matrix.sub_apply, Matrix.one_apply] at this
    linarith
lemma p53bt_sum_psd {N : ℕ} {ι : Type*} (s : Finset ι) (A : ι → Matrix (Fin N) (Fin N) ℂ)
    (h : ∀ i, (A i).PosSemidef) : (∑ i ∈ s, A i).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Matrix.PosSemidef.zero
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact (h a).add ih

lemma p53bt_sqrt_psd {N : ℕ} (Y : Matrix (Fin N) (Fin N) ℂ) :
    (cfc Real.sqrt Y).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => Real.sqrt_nonneg t)

lemma p53bt_sqrt_mul_sqrt {N : ℕ} {Q : Matrix (Fin N) (Fin N) ℂ} (hQ : Q.PosSemidef) :
    cfc Real.sqrt Q * cfc Real.sqrt Q = Q := by
  have hnn : (0 : Matrix (Fin N) (Fin N) ℂ) ≤ Q := Matrix.nonneg_iff_posSemidef.mpr hQ
  rw [← cfc_mul Real.sqrt Real.sqrt Q]
  conv_rhs => rw [← cfc_id ℝ Q]
  apply cfc_congr
  intro t ht
  exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hnn ht)

lemma p53bt_tr_psd_mul {N : ℕ} {P Q : Matrix (Fin N) (Fin N) ℂ} (hP : P.PosSemidef)
    (hQ : Q.PosSemidef) : 0 ≤ (P * Q).trace.re := by
  have hR : (cfc Real.sqrt Q)ᴴ = cfc Real.sqrt Q := (p53bt_sqrt_psd Q).1.eq
  have h := (hP.conjTranspose_mul_mul_same (cfc Real.sqrt Q)).trace_nonneg
  rw [hR, Matrix.trace_mul_comm, ← Matrix.mul_assoc, p53bt_sqrt_mul_sqrt hQ,
    Matrix.trace_mul_comm] at h
  exact (Complex.nonneg_iff.mp h).1

lemma p53bt_unit {N : ℕ} (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (j : Fin N) :
    ∑ w, conj (b j w) * b j w = 1 := by
  have h := orthonormal_iff_ite.mp b.orthonormal j j
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  simp only [if_true] at h
  rw [← h]; simp [dotProduct, mul_comm]

lemma p53bt_psdP {N : ℕ} (v : EuclideanSpace ℂ (Fin N)) : (pureDensity v).PosSemidef := by
  have : pureDensity v = Matrix.vecMulVec (⇑v) (star ⇑v) := by
    ext x y; simp [pureDensity, Matrix.vecMulVec_apply]
  rw [this]; exact Matrix.posSemidef_vecMulVec_self_star _


lemma p53bt_povm_le {M N : ℕ} (D : Fin M → Matrix (Fin N) (Fin N) ℂ) (hD : IsPOVM D) (i : Fin M) :
    (1 - D i).PosSemidef := by
  have : 1 - D i = ∑ k ∈ Finset.univ.erase i, D k := by
    rw [← hD.2, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]; abel
  rw [this]; exact p53bt_sum_psd _ _ hD.1

lemma p53bt_ep_le {N : ℕ} {E ρ : Matrix (Fin N) (Fin N) ℂ} (hE : (1 - E).PosSemidef)
    (hρ : IsDensityMatrix ρ) : (E * ρ).trace.re ≤ 1 := by
  have := p53bt_tr_psd_mul hE hρ.1
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, hρ.2, Complex.sub_re, Complex.one_re] at this
  linarith

lemma p53bt_bdd {M N : ℕ} (p : Fin M → ℝ) (hp : IsPrior p)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) (hrho : ∀ i, IsDensityMatrix (rho i)) :
    BddAbove (Set.range fun D : {D : Fin M → Matrix (Fin N) (Fin N) ℂ // IsPOVM D} =>
      ∑ j, p j * effectProb (D.1 j) (rho j)) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨D, rfl⟩
  calc ∑ j, p j * effectProb (D.1 j) (rho j) ≤ ∑ j, p j * 1 :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
          (p53bt_ep_le (p53bt_povm_le D.1 D.2 j) (hrho j)) (hp.1 j)
    _ = 1 := by simp [hp.2]

lemma p53bt_le_opt {M N : ℕ} (p : Fin M → ℝ) (hp : IsPrior p)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) (hrho : ∀ i, IsDensityMatrix (rho i))
    (D : Fin M → Matrix (Fin N) (Fin N) ℂ) (hD : IsPOVM D) :
    ∑ j, p j * (D j * rho j).trace.re ≤ mixedOptSuccess p rho :=
  le_ciSup (f := fun D : {D : Fin M → Matrix (Fin N) (Fin N) ℂ // IsPOVM D} =>
      ∑ j, p j * effectProb (D.1 j) (rho j)) (p53bt_bdd p hp rho hrho) ⟨D, hD⟩

lemma p53bt_top {N : ℕ} (hN : 0 < N) (S : Matrix (Fin N) (Fin N) ℂ) (hS : S.PosSemidef) :
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
  refine ⟨lam, v, hS.eigenvalues_nonneg i0, ?_, ⟨p53bt_psdP v, ?_⟩, ?_⟩
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
  · have := p53bt_unit hS.1.eigenvectorBasis i0
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
    have hu := p53bt_unit hS.1.eigenvectorBasis i0
    simp only [dotProduct_smul, smul_eq_mul]
    have : star (⇑v) ⬝ᵥ ⇑v = 1 := by
      rw [← hu]; simp [dotProduct, Complex.star_def]; rfl
    rw [this]
    simp [lam]

lemma p53bt_bound_lam {M N : ℕ} (hM : 0 < M) (p : Fin M → ℝ) (hp : IsPrior p)
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
    have h1 := p53bt_le_opt p hp rho hrho D hD
    have h2 : lam⁻¹ * ∑ i, p i * (E i * rho i).trace.re ≤ ∑ j, p j * (D j * rho j).trace.re := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      simp only [hDdef, Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul,
        Complex.add_re, smul_eq_mul, Complex.re_ofReal_mul]
      have : 0 ≤ ((if i = i0 then 1 - ((lam⁻¹ : ℝ) : ℂ) • S else 0) * rho i).trace.re := by
        split_ifs
        · exact p53bt_tr_psd_mul hrest (hrho i).1
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
        rw [this]; exact p53bt_sum_psd _ _ fun j => (hE j).1
      have a1 := p53bt_tr_psd_mul h1 (hrho i).1
      have a2 := p53bt_tr_psd_mul hS (hrho i).1
      simp only [Complex.ofReal_zero, zero_smul, zero_sub, Matrix.neg_mul, Matrix.trace_neg,
        Complex.neg_re] at a2
      rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re] at a1
      linarith
    simp only [mul_zero]
    exact Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hp.1 i) (hle i)

lemma p53bt_affine {V : Type*} [AddCommGroup V] [Module ℝ V] (S : Set V) (hS : Convex ℝ S)
    (g : V → ℝ) (hg : ∀ x y : V, ∀ a b : ℝ, a + b = 1 → g (a • x + b • y) = a * g x + b * g y) :
    QuasiconvexOn ℝ S g ∧ QuasiconcaveOn ℝ S g := by
  have h1 : ConvexOn ℝ S g := ⟨hS, fun x _ y _ a b _ _ hab => by
    rw [hg x y a b hab]; simp [smul_eq_mul]⟩
  have h2 : ConcaveOn ℝ S g := ⟨hS, fun x _ y _ a b _ _ hab => by
    rw [hg x y a b hab]; simp [smul_eq_mul]⟩
  exact ⟨h1.quasiconvexOn, h2.quasiconcaveOn⟩

lemma p53bt_trre_lin {N : ℕ} (A x y : Matrix (Fin N) (Fin N) ℂ) (a b : ℝ) :
    (A * (a • x + b • y)).trace.re = a * (A * x).trace.re + b * (A * y).trace.re := by
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_smul, Complex.add_re, Complex.smul_re, Complex.smul_re, smul_eq_mul, smul_eq_mul]

lemma p53bt_trre_lin' {N : ℕ} (A x y : Matrix (Fin N) (Fin N) ℂ) (a b : ℝ) :
    ((a • x + b • y) * A).trace.re = a * (x * A).trace.re + b * (y * A).trace.re := by
  rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_smul, Complex.add_re, Complex.smul_re, Complex.smul_re, smul_eq_mul, smul_eq_mul]

lemma p53bt_cont {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) :
    Continuous fun x : Matrix (Fin N) (Fin N) ℂ => (A * x).trace.re :=
  Complex.continuous_re.comp ((continuous_const.matrix_mul continuous_id).matrix_trace)

lemma p53bt_cont' {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) :
    Continuous fun x : Matrix (Fin N) (Fin N) ℂ => (x * A).trace.re :=
  Complex.continuous_re.comp ((continuous_id.matrix_mul continuous_const).matrix_trace)

lemma p53bt_psd_comb {N : ℕ} {x y : Matrix (Fin N) (Fin N) ℂ} (hx : x.PosSemidef) (hy : y.PosSemidef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : (a • x + b • y).PosSemidef := by
  have ex : a • x = (a : ℂ) • x := (Complex.coe_smul a x).symm
  have ey : b • y = (b : ℂ) • y := (Complex.coe_smul b y).symm
  rw [ex, ey]
  exact (hx.smul (Complex.zero_le_real.mpr ha)).add (hy.smul (Complex.zero_le_real.mpr hb))

theorem p53bt_key {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
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
    refine ⟨p53bt_psd_comb hx.1 hy.1 ha hb, ?_⟩
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hx.2, hy.2]
    rw [← Complex.coe_smul, ← Complex.coe_smul, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
      ← Complex.ofReal_add, hab, Complex.ofReal_one]
  have neX : X.Nonempty := by
    obtain ⟨_, v, -, -, hv, -⟩ := p53bt_top hN 0 Matrix.PosSemidef.zero
    exact ⟨_, hv⟩
  have kX : IsCompact X := p53bt_compact_density
  have cY : Convex ℝ Y := by
    refine convex_pi fun i _ => ?_
    intro x hx y hy a b ha hb hab
    refine ⟨p53bt_psd_comb hx.1 hy.1 ha hb, ?_⟩
    have : 1 - (a • x + b • y) = a • (1 - x) + b • (1 - y) := by
      have h1 : (1 : Matrix (Fin N) (Fin N) ℂ) = a • 1 + b • 1 := by rw [← add_smul, hab, one_smul]
      rw [smul_sub, smul_sub]
      conv_lhs => rw [h1]
      abel
    rw [this]
    exact p53bt_psd_comb hx.2 hy.2 ha hb
  have neY : Y.Nonempty := ⟨fun _ => 0, fun i _ => ⟨Matrix.PosSemidef.zero, by
    simpa using (Matrix.PosSemidef.one : (1 : Matrix (Fin N) (Fin N) ℂ).PosSemidef)⟩⟩
  have kY : IsCompact Y := isCompact_univ_pi fun _ => p53bt_compact_effect
  have contμ : ∀ E : Fin M → Matrix (Fin N) (Fin N) ℂ, Continuous fun μ => f μ E := by
    intro E
    exact continuous_const.sub (continuous_const.mul
      (continuous_finsetSum _ fun i _ => p53bt_cont (E i)))
  have contE : ∀ μ, Continuous fun E : Fin M → Matrix (Fin N) (Fin N) ℂ => f μ E := by
    intro μ
    exact (continuous_finsetSum _ fun i _ => continuous_const.mul
      ((p53bt_cont' (rho i)).comp (continuous_apply i))).sub
      (continuous_const.mul (continuous_finsetSum _ fun i _ =>
        (p53bt_cont' μ).comp (continuous_apply i)))
  have affμ : ∀ E, ∀ x y : Matrix (Fin N) (Fin N) ℂ, ∀ a b : ℝ, a + b = 1 →
      f (a • x + b • y) E = a * f x E + b * f y E := by
    intro E x y a b hab
    simp only [hf, p53bt_trre_lin, Finset.sum_add_distrib, ← Finset.mul_sum]
    linear_combination -(∑ i, p i * (E i * rho i).trace.re) * hab
  have affE : ∀ μ, ∀ x y : Fin M → Matrix (Fin N) (Fin N) ℂ, ∀ a b : ℝ, a + b = 1 →
      f μ (a • x + b • y) = a * f μ x + b * f μ y := by
    intro μ x y a b hab
    simp only [hf, Pi.add_apply, Pi.smul_apply, p53bt_trre_lin', mul_add, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    have e1 : ∀ i, p i * (a * (x i * rho i).trace.re) = a * (p i * (x i * rho i).trace.re) :=
      fun i => by ring
    have e2 : ∀ i, p i * (b * (y i * rho i).trace.re) = b * (p i * (y i * rho i).trace.re) :=
      fun i => by ring
    simp only [e1, e2, ← Finset.mul_sum]
    ring
  obtain ⟨μs, hμs, Es, hEs, hsad⟩ := Sion.exists_isSaddlePointOn (X := X) (Y := Y) (f := f)
    neX cX kX (fun E _ => (contμ E).continuousOn.lowerSemicontinuousOn)
    (fun E _ => (p53bt_affine X cX _ (affμ E)).1) cY neY kY
    (fun μ _ => (contE μ).continuousOn.upperSemicontinuousOn)
    (fun μ _ => (p53bt_affine Y cY _ (affE μ)).2)
  have hEs' : ∀ i, IsEffect (Es i) := fun i => hEs i (Set.mem_univ i)
  obtain ⟨lam, v, hlam, hlamS, hv, hvS⟩ :=
    p53bt_top hN (∑ i, Es i) (p53bt_sum_psd _ _ fun i => (hEs' i).1)
  have h0 : f (pureDensity v) Es ≤ 0 := by
    have hb := p53bt_bound_lam hM p hp rho hrho Es hEs' lam hlam hlamS
    simp only [hf]
    have : ∑ i, (Es i * pureDensity v).trace.re = lam := by
      rw [← hvS, ← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul]
    rw [this]; linarith
  refine ⟨μs, hμs, fun E hE => ?_⟩
  have := hsad (pureDensity v) hv E (fun i _ => hE i)
  simp only [hf] at this h0
  linarith

/-! ## block embeddings -/

def p53bt_V {M : ℕ} (N : ℕ) (i : Fin M) : Matrix (Fin M × Fin N) (Fin N) ℂ :=
  fun u b => if u = (i, b) then 1 else 0

lemma p53bt_VtV {M N : ℕ} (i j : Fin M) :
    (p53bt_V N i)ᴴ * p53bt_V N j = if i = j then 1 else 0 := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single (i, a)]
  · simp only [Matrix.conjTranspose_apply, p53bt_V, if_true, star_one, one_mul]
    by_cases h : i = j
    · subst h; by_cases hab : a = b
      · subst hab; simp
      · simp [Matrix.one_apply, Prod.ext_iff, hab]
    · simp [h, Prod.ext_iff]
  · intro x _ hx; simp [Matrix.conjTranspose_apply, p53bt_V, hx]
  · simp

lemma p53bt_conj_apply {M N : ℕ} (i j : Fin M) (A : Matrix (Fin N) (Fin N) ℂ)
    (u w : Fin M × Fin N) :
    (p53bt_V N i * A * (p53bt_V N j)ᴴ) u w = if u.1 = i ∧ w.1 = j then A u.2 w.2 else 0 := by
  obtain ⟨u1, u2⟩ := u
  obtain ⟨w1, w2⟩ := w
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, p53bt_V, Prod.ext_iff]
  by_cases h1 : u1 = i <;> by_cases h2 : w1 = j <;> simp [h1, h2, ite_and, eq_comm]

lemma p53bt_sumVV {M N : ℕ} : ∑ i : Fin M, p53bt_V N i * (1 : Matrix (Fin N) (Fin N) ℂ) * (p53bt_V N i)ᴴ = 1 := by
  ext u w
  rw [Matrix.sum_apply]
  simp only [p53bt_conj_apply, Matrix.one_apply]
  obtain ⟨u1, u2⟩ := u
  obtain ⟨w1, w2⟩ := w
  by_cases h : u1 = w1
  · subst h; simp [Prod.ext_iff]
  · simp [Prod.ext_iff, h]
    exact Finset.sum_eq_zero fun x _ => by
      rw [if_neg]; rintro ⟨h1, h2⟩; exact h (h1.trans h2.symm)

lemma p53bt_block {M N : ℕ} (p : Fin M → ℝ) (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) :
    blockEnsembleState p rho = ∑ i, p53bt_V N i * ((p i : ℂ) • rho i) * (p53bt_V N i)ᴴ := by
  ext u w
  rw [Matrix.sum_apply]
  simp only [p53bt_conj_apply, blockEnsembleState, Matrix.smul_apply, smul_eq_mul]
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

lemma p53bt_comp {M N : ℕ} (μ : Matrix (Fin N) (Fin N) ℂ) :
    binaryComparisonState (M := M) μ =
      ∑ i : Fin M, p53bt_V N i * ((((1 / (M : ℝ) : ℝ)) : ℂ) • μ) * (p53bt_V N i)ᴴ := by
  ext u w
  rw [Matrix.sum_apply]
  simp only [p53bt_conj_apply, binaryComparisonState, Matrix.kronecker, Matrix.kroneckerMap_apply,
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

lemma p53bt_ep_blocks {M N : ℕ} (T : Matrix (Fin M × Fin N) (Fin M × Fin N) ℂ)
    (A : Fin M → Matrix (Fin N) (Fin N) ℂ) :
    effectProb T (∑ i, p53bt_V N i * A i * (p53bt_V N i)ᴴ) =
      ∑ i, ((p53bt_V N i)ᴴ * T * p53bt_V N i * A i).trace.re := by
  unfold effectProb
  rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc]

lemma p53bt_blk_eff {M N : ℕ} (T : Matrix (Fin M × Fin N) (Fin M × Fin N) ℂ) (hT : IsEffect T)
    (i : Fin M) : IsEffect ((p53bt_V N i)ᴴ * T * p53bt_V N i) := by
  refine ⟨hT.1.conjTranspose_mul_mul_same _, ?_⟩
  have : 1 - (p53bt_V N i)ᴴ * T * p53bt_V N i = (p53bt_V N i)ᴴ * (1 - T) * p53bt_V N i := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, p53bt_VtV, if_pos rfl]
  rw [this]; exact hT.2.conjTranspose_mul_mul_same _

lemma p53bt_TD {M N : ℕ} (D : Fin M → Matrix (Fin N) (Fin N) ℂ) (hD : IsPOVM D) :
    IsEffect (∑ i, p53bt_V N i * D i * (p53bt_V N i)ᴴ) ∧
      ∀ j, (p53bt_V N j)ᴴ * (∑ i, p53bt_V N i * D i * (p53bt_V N i)ᴴ) * p53bt_V N j = D j := by
  refine ⟨⟨?_, ?_⟩, fun j => ?_⟩
  · exact Matrix.posSemidef_sum _ fun i _ => (hD.1 i).mul_mul_conjTranspose_same _
  · have : 1 - ∑ i, p53bt_V N i * D i * (p53bt_V N i)ᴴ =
        ∑ i, p53bt_V N i * (1 - D i) * (p53bt_V N i)ᴴ := by
      conv_lhs => rw [← p53bt_sumVV (M := M) (N := N)]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.mul_sub, Matrix.sub_mul]
    rw [this]
    exact Matrix.posSemidef_sum _ fun i _ => (p53bt_povm_le D hD i).mul_mul_conjTranspose_same _
  · rw [Matrix.mul_sum, Matrix.sum_mul]
    simp_rw [← Matrix.mul_assoc, p53bt_VtV, Matrix.mul_assoc, p53bt_VtV]
    simp [ite_mul, mul_ite]

def p53bt_blk {M N : ℕ} (T : Matrix (Fin M × Fin N) (Fin M × Fin N) ℂ) (i : Fin M) :
    Matrix (Fin N) (Fin N) ℂ := (p53bt_V N i)ᴴ * T * p53bt_V N i

lemma p53bt_povm_ne {M N : ℕ} (hM : 0 < M) :
    Nonempty {D : Fin M → Matrix (Fin N) (Fin N) ℂ // IsPOVM D} := by
  let i0 : Fin M := ⟨0, hM⟩
  refine ⟨⟨fun j => if j = i0 then 1 else 0, ?_, ?_⟩⟩
  · intro j; dsimp only; split_ifs
    · exact Matrix.PosSemidef.one
    · exact Matrix.PosSemidef.zero
  · simp

lemma p53bt_opt_nonneg {M N : ℕ} (hM : 0 < M) (p : Fin M → ℝ) (hp : IsPrior p)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) (hrho : ∀ i, IsDensityMatrix (rho i)) :
    0 ≤ mixedOptSuccess p rho := by
  obtain ⟨D⟩ := p53bt_povm_ne (N := N) hM
  refine le_trans ?_ (p53bt_le_opt p hp rho hrho D.1 D.2)
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hp.1 j) (p53bt_tr_psd_mul (D.2.1 j) (hrho j).1)

theorem p53bt_main {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (p : Fin M → ℝ) (hp : IsPrior p)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) (hrho : ∀ i, IsDensityMatrix (rho i)) :
    ∃ mu : Matrix (Fin N) (Fin N) ℂ, IsDensityMatrix mu ∧
      1 - mixedOptSuccess p rho = binaryTypeIError (1 / (M : ℝ))
        (blockEnsembleState p rho) (binaryComparisonState (M := M) mu) ∧
      ∀ nu : Matrix (Fin N) (Fin N) ℂ, IsDensityMatrix nu →
        binaryTypeIError (1 / (M : ℝ)) (blockEnsembleState p rho)
          (binaryComparisonState (M := M) nu) ≤
        binaryTypeIError (1 / (M : ℝ)) (blockEnsembleState p rho)
          (binaryComparisonState (M := M) mu) := by
  obtain ⟨mu, hmu, hkey⟩ := p53bt_key hM hN p hp rho hrho
  set s := mixedOptSuccess p rho with hs
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  -- effect probabilities against the two states
  have hΨ0 : ∀ (T : Matrix (Fin M × Fin N) (Fin M × Fin N) ℂ), effectProb T (blockEnsembleState p rho) =
      ∑ i, p i * (p53bt_blk T i * rho i).trace.re := by
    intro T
    rw [p53bt_block, p53bt_ep_blocks]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]; rfl
  have hΨ1 : ∀ (T : Matrix (Fin M × Fin N) (Fin M × Fin N) ℂ) (ν : Matrix (Fin N) (Fin N) ℂ), effectProb T (binaryComparisonState (M := M) ν) =
      (1 / (M : ℝ)) * ∑ i, (p53bt_blk T i * ν).trace.re := by
    intro T ν
    rw [p53bt_comp, p53bt_ep_blocks, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]; rfl
  have hbdd : ∀ ν, BddBelow {e : ℝ | ∃ T, IsEffect T ∧
      effectProb T (binaryComparisonState (M := M) ν) ≤ 1 / (M : ℝ) ∧
      e = 1 - effectProb T (blockEnsembleState p rho)} := by
    intro ν
    refine ⟨0, ?_⟩
    rintro e ⟨T, hT, -, rfl⟩
    rw [hΨ0]
    have : ∑ i, p i * (p53bt_blk T i * rho i).trace.re ≤ ∑ i, p i * 1 :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
        (p53bt_ep_le (p53bt_blk_eff T hT i).2 (hrho i)) (hp.1 i)
    simp only [mul_one, hp.2] at this
    linarith
  -- (a) every comparison state gives error at most 1 - s
  have ha : ∀ ν, IsDensityMatrix ν →
      binaryTypeIError (1 / (M : ℝ)) (blockEnsembleState p rho)
        (binaryComparisonState (M := M) ν) ≤ 1 - s := by
    intro ν hν
    unfold binaryTypeIError
    set I := sInf {e : ℝ | ∃ T, IsEffect T ∧
      effectProb T (binaryComparisonState (M := M) ν) ≤ 1 / (M : ℝ) ∧
      e = 1 - effectProb T (blockEnsembleState p rho)}
    have hall : ∀ D : {D : Fin M → Matrix (Fin N) (Fin N) ℂ // IsPOVM D},
        ∑ j, p j * effectProb (D.1 j) (rho j) ≤ 1 - I := by
      intro D
      obtain ⟨hTe, hTb⟩ := p53bt_TD D.1 D.2
      set T := ∑ i, p53bt_V N i * D.1 i * (p53bt_V N i)ᴴ
      have hmem : 1 - ∑ j, p j * effectProb (D.1 j) (rho j) ∈ {e : ℝ | ∃ T, IsEffect T ∧
          effectProb T (binaryComparisonState (M := M) ν) ≤ 1 / (M : ℝ) ∧
          e = 1 - effectProb T (blockEnsembleState p rho)} := by
        refine ⟨T, hTe, ?_, ?_⟩
        · rw [hΨ1]
          simp only [show ∀ i, p53bt_blk T i = D.1 i from hTb]
          rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, D.2.2, Matrix.one_mul, hν.2]
          simp
        · have e : ∀ i, p53bt_blk T i = D.1 i := hTb
          rw [hΨ0]; simp only [e]; rfl
      have := csInf_le (hbdd ν) hmem
      linarith
    have := p53bt_povm_ne (N := N) hM
    have h2 : s ≤ 1 - I := by rw [hs]; unfold mixedOptSuccess; exact ciSup_le hall
    linarith
  -- (b) the optimal mu gives error at least 1 - s
  have hb : 1 - s ≤ binaryTypeIError (1 / (M : ℝ)) (blockEnsembleState p rho)
      (binaryComparisonState (M := M) mu) := by
    unfold binaryTypeIError
    apply le_csInf
    · refine ⟨1 - effectProb 0 (blockEnsembleState p rho), 0, ⟨Matrix.PosSemidef.zero, by
        simpa using (Matrix.PosSemidef.one : (1 : Matrix (Fin M × Fin N) (Fin M × Fin N) ℂ).PosSemidef)⟩,
        ?_, rfl⟩
      simp [effectProb]
    · rintro e ⟨T, hT, hT1, rfl⟩
      have hE : ∀ i, IsEffect (p53bt_blk T i) := p53bt_blk_eff T hT
      have h1 := hkey _ hE
      rw [hΨ1] at hT1
      rw [hΨ0]
      have h2 : ∑ i, (p53bt_blk T i * mu).trace.re ≤ 1 := by
        rw [one_div, inv_mul_le_iff₀ hMpos, mul_inv_cancel₀ hMpos.ne'] at hT1
        exact hT1
      have h3 := p53bt_opt_nonneg hM p hp rho hrho
      nlinarith
  exact ⟨mu, hmu, (le_antisymm hb (ha mu hmu)).symm ▸ rfl, fun nu hnu => (ha nu hnu).trans hb⟩

end

theorem solution {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (p : Fin M → ℝ) (hp : QAlgorithms.Papers.Independent.Information100.P53.IsPrior p)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) (hrho : ∀ i, QAlgorithms.IsDensityMatrix (rho i)) :
    ∃ mu : Matrix (Fin N) (Fin N) ℂ, QAlgorithms.IsDensityMatrix mu ∧
      1 - QAlgorithms.mixedOptSuccess p rho =
        QAlgorithms.Papers.Independent.Information100.P53.binaryTypeIError (1 / (M : ℝ))
          (QAlgorithms.Papers.Independent.Information100.P53.blockEnsembleState p rho)
          (QAlgorithms.Papers.Independent.Information100.P53.binaryComparisonState (M := M) mu) ∧
      ∀ nu : Matrix (Fin N) (Fin N) ℂ, QAlgorithms.IsDensityMatrix nu →
        QAlgorithms.Papers.Independent.Information100.P53.binaryTypeIError (1 / (M : ℝ))
          (QAlgorithms.Papers.Independent.Information100.P53.blockEnsembleState p rho)
          (QAlgorithms.Papers.Independent.Information100.P53.binaryComparisonState (M := M) nu) ≤
        QAlgorithms.Papers.Independent.Information100.P53.binaryTypeIError (1 / (M : ℝ))
          (QAlgorithms.Papers.Independent.Information100.P53.blockEnsembleState p rho)
          (QAlgorithms.Papers.Independent.Information100.P53.binaryComparisonState (M := M) mu) :=
  p53bt_main hM hN p hp rho hrho

