-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P35.power_purity_family
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:00:38.265415+00:00
-- url     : https://prove2.me/submissions/db08fa55-18ac-4fa4-9559-471f5963d4fe

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P35

-- ===== P35B =====

noncomputable section

namespace X4OB
open Matrix QAlgorithms.Papers.Independent.Support50.P35
open scoped Matrix ComplexConjugate

variable {I K L : Type*} [Fintype I] [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]

lemma tr_real {A B : Matrix I I ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (((A * B).trace.re : ℝ) : ℂ) = (A * B).trace := by
  have h : star (A * B).trace = (A * B).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA.eq, hB.eq, Matrix.trace_mul_comm]
  exact Complex.conj_eq_iff_re.1 h

lemma coeff {nu : L → Matrix I I ℂ} (hnu : IsHermitianONBasis nu) (c : L → ℝ) (l' : L) :
    ((∑ l, (c l : ℂ) • nu l) * nu l').trace.re = c l' := by
  rw [Finset.sum_mul, Matrix.trace_sum]
  simp only [Matrix.smul_mul, Matrix.trace_smul, hnu.2.1, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Complex.ofReal_re]

lemma expand {mu : K → Matrix I I ℂ} {nu : L → Matrix I I ℂ} (hmu : IsHermitianONBasis mu)
    (hnu : IsHermitianONBasis nu) (k : K) :
    mu k = ∑ l, ((basisChange nu mu l k : ℝ) : ℂ) • nu l := by
  obtain ⟨c, hc⟩ := hnu.2.2 (mu k) (hmu.1 k)
  have : ∀ l, basisChange nu mu l k = c l := by
    intro l; simp only [basisChange]; rw [hc, coeff hnu]
  simp only [this]; exact hc

lemma bc_transpose (mu : K → Matrix I I ℂ) (nu : L → Matrix I I ℂ) :
    basisChange mu nu = (basisChange nu mu)ᵀ := by
  ext k l; simp only [basisChange, transpose_apply]; rw [Matrix.trace_mul_comm]

lemma orth {mu : K → Matrix I I ℂ} {nu : L → Matrix I I ℂ} (hmu : IsHermitianONBasis mu)
    (hnu : IsHermitianONBasis nu) : (basisChange nu mu)ᵀ * basisChange nu mu = 1 := by
  ext k k'
  have h := hmu.2.1 k k'
  rw [expand hmu hnu k', Matrix.mul_sum, Matrix.trace_sum] at h
  simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul] at h
  have h2 := congrArg Complex.re h
  rw [Complex.re_sum] at h2
  simp only [Matrix.mul_apply, transpose_apply, Matrix.one_apply]
  rw [show (if k = k' then (1:ℝ) else 0) = ((if k = k' then 1 else 0 : ℂ)).re by split_ifs <;> simp,
    ← h2]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← tr_real (hmu.1 k) (hnu.1 l), ← Complex.ofReal_mul, Complex.ofReal_re]
  simp only [basisChange]; ring

lemma recon {mu : K → Matrix I I ℂ} {nu : L → Matrix I I ℂ} (hmu : IsHermitianONBasis mu)
    (hnu : IsHermitianONBasis nu) (c : K → ℝ) :
    hermitianReconstruction nu ((basisChange nu mu).mulVec c) = hermitianReconstruction mu c := by
  simp only [hermitianReconstruction, Matrix.mulVec, dotProduct]
  conv_rhs => arg 2; ext k; rw [expand hmu hnu k]
  simp only [Finset.smul_sum, smul_smul, Complex.ofReal_sum, Finset.sum_smul, Complex.ofReal_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]

/-- basis-free form of the pure-state equations. -/
lemma charac {mu : K → Matrix I I ℂ} (hmu : IsHermitianONBasis mu) (c : K → ℝ) :
    generalPureEquations mu c ↔
      (hermitianReconstruction mu c).trace.re = 1 ∧
      (hermitianReconstruction mu c * hermitianReconstruction mu c).trace.re = 1 ∧
      ∀ X : Matrix I I ℂ, X.IsHermitian →
        (hermitianReconstruction mu c * hermitianReconstruction mu c * X).trace.re =
          (hermitianReconstruction mu c * X).trace.re := by
  set ρ := hermitianReconstruction mu c
  have e1 : ρ.trace.re = ∑ a, c a * (mu a).trace.re := by
    simp [ρ, hermitianReconstruction, Matrix.trace_sum, Matrix.trace_smul]
  have e2 : (ρ * ρ).trace.re = dotProduct c c := by
    have : ∀ a, (ρ * mu a).trace.re = c a := fun a => coeff hmu c a
    simp only [ρ, hermitianReconstruction] at this ⊢
    rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
    simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, dotProduct]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.re_ofReal_mul, this]
  have e3 : ∀ g, (ρ * ρ * mu g).trace.re = ∑ a, ∑ b, c a * c b * (multiplicationCoefficient mu a b g).re := by
    intro g
    simp only [ρ, hermitianReconstruction, multiplicationCoefficient, Matrix.sum_mul, Matrix.mul_sum,
      Matrix.trace_sum, Complex.re_sum, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    simp only [Finset.mul_sum, Complex.re_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]; ring
  have e4 : ∀ g, (ρ * mu g).trace.re = c g := fun g => coeff hmu c g
  unfold generalPureEquations
  rw [← e1, ← e2]
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h X hX => ?_, fun h g => ?_⟩)
  · obtain ⟨d, rfl⟩ := hmu.2.2 X hX
    simp only [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum, Matrix.mul_smul, Matrix.trace_smul,
      smul_eq_mul, Complex.re_ofReal_mul]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [e3, h g, e4]
  · rw [← e3, h (mu g) (hmu.1 g), e4]

end X4OB

-- ===== P35C =====

noncomputable section

namespace X4OC
open Matrix QAlgorithms QAlgorithms.Papers.Independent.Support50.P35
open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)
open scoped Matrix ComplexConjugate ComplexOrder

variable {I : Type} [Fintype I] [DecidableEq I]

/-- spectral decomposition as a sum of eigenprojectors. -/
lemma spec_sum {ρ : Matrix I I ℂ} (h : ρ.IsHermitian) :
    ρ = ∑ k, ((h.eigenvalues k : ℝ) : ℂ) • pureDensity (h.eigenvectorBasis k) := by
  conv_lhs => rw [h.spectral_theorem, Unitary.conjStarAlgAut_apply]
  ext a b
  simp only [Matrix.mul_apply, diagonal, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
    pureDensity, smul_eq_mul, Function.comp_apply, Matrix.star_apply, RCLike.star_def,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, ite_mul, zero_mul,
    Finset.sum_ite_eq, Matrix.IsHermitian.eigenvectorUnitary_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [RCLike.ofReal_eq_complex_ofReal]
  ring

lemma pure_proj (v : EuclideanSpace ℂ I) (hv : ‖v‖ = 1) :
    pureDensity v * pureDensity v = pureDensity v ∧ (pureDensity v).trace = 1 ∧
      (pureDensity v).IsHermitian := by
  have hs : ∑ i, conj (v i) * v i = 1 := by
    have h1 : ∑ i, ‖v i‖ ^ 2 = 1 := by
      rw [← EuclideanSpace.norm_sq_eq, hv, one_pow]
    have : ∑ i, conj (v i) * v i = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
    rw [this, h1]; simp
  refine ⟨?_, ?_, ?_⟩
  · ext a b
    simp only [pureDensity, Matrix.mul_apply, Matrix.of_apply]
    have : ∑ j, v a * conj (v j) * (v j * conj (v b)) = v a * conj (v b) * ∑ j, conj (v j) * v j := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
    rw [this, hs, mul_one]
  · simp only [Matrix.trace, Matrix.diag, pureDensity, Matrix.of_apply]
    rw [← hs]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · ext a b; simp [pureDensity, mul_comm]

lemma proj_pure {ρ : Matrix I I ℂ} (h : ρ.IsHermitian) (h2 : ρ * ρ = ρ) (h1 : ρ.trace = 1) :
    IsPure ρ := by
  set lam := h.eigenvalues
  set v := h.eigenvectorBasis
  have hv : ∀ k, ‖v k‖ = 1 := fun k => v.orthonormal.1 k
  have hsq : ∀ k, lam k * lam k = lam k := by
    intro k
    have e1 := h.mulVec_eigenvectorBasis k
    have e2 : (ρ * ρ) *ᵥ (v k).ofLp = (lam k * lam k) • (v k).ofLp := by
      rw [← Matrix.mulVec_mulVec, e1, Matrix.mulVec_smul, e1, smul_smul]
    rw [h2, e1] at e2
    have hne : (v k).ofLp ≠ 0 := by
      intro h0
      have : v k = 0 := by ext i; simp [h0]
      have := hv k; simp_all
    by_contra hc
    have : (lam k - lam k * lam k) • (v k).ofLp = 0 := by rw [sub_smul, e2, sub_self]
    exact hne ((smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm hc)))
  have h01 : ∀ k, lam k = 0 ∨ lam k = 1 := by
    intro k
    have := hsq k
    have : lam k * (lam k - 1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  have hsum : ∑ k, lam k = 1 := by
    have := h.trace_eq_sum_eigenvalues
    rw [h1] at this
    have h3 : ((∑ k, lam k : ℝ) : ℂ) = 1 := by push_cast; exact this.symm
    exact_mod_cast h3
  obtain ⟨i0, hi0⟩ : ∃ i0, lam i0 = 1 := by
    by_contra hc
    push Not at hc
    have : ∑ k, lam k = 0 := Finset.sum_eq_zero fun k _ => (h01 k).resolve_right (hc k)
    linarith
  have hother : ∀ k, k ≠ i0 → lam k = 0 := by
    have hs := Finset.add_sum_erase Finset.univ lam (Finset.mem_univ i0)
    rw [hsum, hi0] at hs
    have h0 : ∑ k ∈ Finset.univ.erase i0, lam k = 0 := by linarith
    have hnn : ∀ k ∈ Finset.univ.erase i0, 0 ≤ lam k := fun k _ => by rcases h01 k with h | h <;> simp [h]
    intro k hk
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 k (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩)
  refine ⟨v i0, hv i0, ?_⟩
  rw [spec_sum h]
  rw [Finset.sum_eq_single i0 (fun k _ hk => by simp [lam, hother k hk]) (by simp)]
  simp [lam, hi0]
  rfl

variable {K : Type} [Fintype K] [DecidableEq K]

lemma herm_recon {mu : K → Matrix I I ℂ} (hmu : IsHermitianONBasis mu) (c : K → ℝ) :
    (hermitianReconstruction mu c).IsHermitian := by
  unfold hermitianReconstruction
  rw [IsHermitian, conjTranspose_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [conjTranspose_smul, (hmu.1 k).eq]
  simp

lemma herm_expand {mu : K → Matrix I I ℂ} (hmu : IsHermitianONBasis mu) {H : Matrix I I ℂ}
    (hH : H.IsHermitian) : H = ∑ g, (H * mu g).trace • mu g := by
  obtain ⟨c, hc⟩ := hmu.2.2 H hH
  have : ∀ g, (H * mu g).trace = c g := by
    intro g
    rw [← X4OB.tr_real hH (hmu.1 g)]
    congr 1
    rw [hc, X4OB.coeff hmu]
  simp only [this]; exact hc

lemma all_expand {mu : K → Matrix I I ℂ} (hmu : IsHermitianONBasis mu) (X : Matrix I I ℂ) :
    X = ∑ g, (X * mu g).trace • mu g := by
  set H1 := (1/2 : ℂ) • (X + Xᴴ)
  set H2 := (-(Complex.I / 2)) • (X - Xᴴ)
  have h1 : H1.IsHermitian := by
    simp only [H1, IsHermitian, conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose]
    rw [add_comm]; congr 1; simp [Complex.ext_iff]
  have h2 : H2.IsHermitian := by
    simp only [H2, IsHermitian, conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose]
    have : star (-(Complex.I / 2)) = -(-(Complex.I / 2)) := by
      apply Complex.ext <;> simp <;> norm_num
    rw [this, neg_smul, ← smul_neg, neg_sub]
  have hX : X = H1 + Complex.I • H2 := by
    simp only [H1, H2, smul_smul]
    ext a b
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    ring_nf
    rw [Complex.I_sq]; ring
  conv_lhs => rw [hX, herm_expand hmu h1, herm_expand hmu h2]
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [smul_smul, ← add_smul]
  congr 1
  conv_rhs => rw [hX]
  simp only [Matrix.add_mul, Matrix.trace_add, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

lemma eqs_iff {mu : K → Matrix I I ℂ} (hmu : IsHermitianONBasis mu) (c : K → ℝ) :
    generalPureEquations mu c ↔
      hermitianReconstruction mu c * hermitianReconstruction mu c = hermitianReconstruction mu c ∧
      (hermitianReconstruction mu c).trace = 1 := by
  rw [X4OB.charac hmu]
  set ρ := hermitianReconstruction mu c
  have hρ : ρ.IsHermitian := herm_recon hmu c
  have htr : ((ρ.trace.re : ℝ) : ℂ) = ρ.trace := by
    have := X4OB.tr_real hρ (Matrix.isHermitian_one)
    rwa [Matrix.mul_one] at this
  constructor
  · rintro ⟨t1, t2, t3⟩
    obtain ⟨Y, hYdef⟩ : ∃ Y, Y = ρ * ρ - ρ := ⟨_, rfl⟩
    have hY : Y.IsHermitian := by
      rw [hYdef]; simp only [IsHermitian, conjTranspose_sub, conjTranspose_mul, hρ.eq]
    have h0 : (Y * Y).trace.re = 0 := by
      have := t3 Y hY
      rw [show Y * Y = (ρ * ρ - ρ) * Y by rw [← hYdef], Matrix.sub_mul (ρ * ρ) ρ Y, Matrix.trace_sub, Complex.sub_re, this, sub_self]
    have h0' : (Yᴴ * Y).trace = 0 := by
      rw [hY.eq, ← X4OB.tr_real hY hY, h0, Complex.ofReal_zero]
    have := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 h0'
    refine ⟨sub_eq_zero.1 (hYdef ▸ this), ?_⟩
    rw [← htr, t1, Complex.ofReal_one]
  · rintro ⟨p1, p2⟩
    refine ⟨by rw [p2, Complex.one_re], by rw [p1, p2, Complex.one_re], fun X _ => by rw [p1]⟩

theorem part1 {mu : K → Matrix I I ℂ} (hmu : IsHermitianONBasis mu) (a b : K) :
    mu a * mu b = ∑ g, multiplicationCoefficient mu a b g • mu g :=
  all_expand hmu _

theorem pure_iff {mu : K → Matrix I I ℂ} (hmu : IsHermitianONBasis mu) (c : K → ℝ) :
    IsPure (hermitianReconstruction mu c) ↔ generalPureEquations mu c := by
  rw [eqs_iff hmu]
  constructor
  · rintro ⟨v, hv, he⟩
    obtain ⟨p1, p2, -⟩ := pure_proj v hv
    rw [he]; exact ⟨p1, p2⟩
  · rintro ⟨p1, p2⟩
    exact proj_pure (herm_recon hmu c) p1 p2

lemma recon_lin (mu : K → Matrix I I ℂ) (a b : ℝ) (c d : K → ℝ) :
    hermitianReconstruction mu (a • c + b • d) =
      (a : ℂ) • hermitianReconstruction mu c + (b : ℂ) • hermitianReconstruction mu d := by
  simp only [hermitianReconstruction, Finset.smul_sum, ← Finset.sum_add_distrib, smul_smul,
    ← add_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  push_cast; rfl

/-- coordinates of a pure eigenprojector lie on the pure variety. -/
lemma coord_pure {mu : K → Matrix I I ℂ} (hmu : IsHermitianONBasis mu) (v : EuclideanSpace ℂ I)
    (hv : ‖v‖ = 1) : (fun g => (pureDensity v * mu g).trace.re) ∈ generalPureSet mu := by
  obtain ⟨p1, p2, p3⟩ := pure_proj v hv
  have hr : hermitianReconstruction mu (fun g => (pureDensity v * mu g).trace.re) = pureDensity v := by
    conv_rhs => rw [herm_expand hmu p3]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [X4OB.tr_real p3 (hmu.1 g)]
  show generalPureEquations mu _
  rw [eqs_iff hmu, hr]; exact ⟨p1, p2⟩

theorem hull {mu : K → Matrix I I ℂ} (hmu : IsHermitianONBasis mu) :
    {c : K → ℝ | IsDensityMatrix (hermitianReconstruction mu c)} = convexHull ℝ (generalPureSet mu) := by
  apply Set.Subset.antisymm
  · intro c hc
    obtain ⟨hpsd, htr⟩ := hc
    set ρ := hermitianReconstruction mu c
    have hρ := hpsd.1
    set lam := hρ.eigenvalues
    set v := hρ.eigenvectorBasis
    have hv : ∀ k, ‖v k‖ = 1 := fun k => v.orthonormal.1 k
    have hcg : c = ∑ k, lam k • (fun g => (pureDensity (v k) * mu g).trace.re) := by
      funext g
      rw [← X4OB.coeff hmu c g]
      change (ρ * mu g).trace.re = _
      conv_lhs => rw [spec_sum hρ]
      rw [Finset.sum_mul, Matrix.trace_sum, Complex.re_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
      rfl
    have hsum : ∑ k, lam k = 1 := by
      have := hρ.trace_eq_sum_eigenvalues
      rw [htr] at this
      have h3 : ((∑ k, lam k : ℝ) : ℂ) = 1 := by push_cast; exact this.symm
      exact_mod_cast h3
    rw [hcg]
    exact (convex_convexHull ℝ _).sum_mem (fun k _ => hpsd.eigenvalues_nonneg k) hsum
      (fun k _ => subset_convexHull ℝ _ (coord_pure hmu (v k) (hv k)))
  · refine convexHull_min ?_ ?_
    · intro c hc
      have hc' : generalPureEquations mu c := hc
      obtain ⟨w, hw, he⟩ := (pure_iff hmu c).2 hc'
      obtain ⟨-, p2, p3⟩ := pure_proj w hw
      show IsDensityMatrix _
      rw [he]
      refine ⟨?_, p2⟩
      have := posSemidef_conjTranspose_mul_self (pureDensity w)
      rwa [p3.eq, (pure_proj w hw).1] at this
    · intro c hc d hd a b ha hb hab
      obtain ⟨hc1, hc2⟩ := hc
      obtain ⟨hd1, hd2⟩ := hd
      show IsDensityMatrix _
      rw [recon_lin]
      refine ⟨(hc1.smul (by exact_mod_cast ha)).add (hd1.smul (by exact_mod_cast hb)), ?_⟩
      rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hc2, hd2]
      simp only [smul_eq_mul, mul_one]
      exact_mod_cast hab

end X4OC

-- ===== P35P =====

/-! Generic: power-trace convexity (Peierls), power purity costs, pure marginals of product states. -/

noncomputable section

namespace X4PP
open Matrix QAlgorithms QAlgorithms.Papers.Independent.Support50.P35
open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)
open scoped Matrix ComplexConjugate ComplexOrder

variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma cfc_trace {Y : Matrix ι ι ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma ds_sums (W : Matrix ι ι ℂ)
    (hW : W ∈ Matrix.unitaryGroup ι ℂ) :
    (∀ i, ∑ k, Complex.normSq (W k i) = 1) ∧ (∀ k, ∑ i, Complex.normSq (W k i) = 1) := by
  constructor
  · intro i
    have := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1 hW) i) i
    simp only [Matrix.mul_apply, star_apply, RCLike.star_def, Matrix.one_apply_eq] at this
    have h2 : ((∑ k, Complex.normSq (W k i) : ℝ) : ℂ) = 1 := by
      rw [← this]; push_cast; simp only [Complex.normSq_eq_conj_mul_self]
    exact_mod_cast h2
  · intro k
    have := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.1 hW) k) k
    simp only [Matrix.mul_apply, star_apply, RCLike.star_def, Matrix.one_apply_eq] at this
    have h2 : ((∑ i, Complex.normSq (W k i) : ℝ) : ℂ) = 1 := by
      rw [← this]; push_cast; simp only [Complex.normSq_eq_conj_mul_self]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    exact_mod_cast h2

lemma diag_conj (U V : Matrix ι ι ℂ) (lam : ι → ℝ) (i : ι) :
    (Uᴴ * (V * diagonal (RCLike.ofReal ∘ lam : ι → ℂ) * star V) * U : Matrix ι ι ℂ) i i =
      ∑ k, ((Complex.normSq ((star V * U) k i) * lam k : ℝ) : ℂ) := by
  have hm : Uᴴ * (V * diagonal (RCLike.ofReal ∘ lam : ι → ℂ) * star V) * U =
      (star V * U)ᴴ * diagonal (RCLike.ofReal ∘ lam : ι → ℂ) * (star V * U) := by
    simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.star_eq_conjTranspose,
      conjTranspose_conjTranspose]
  rw [hm, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_diagonal, conjTranspose_apply, RCLike.star_def]
  simp only [Function.comp_apply, Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
  exact mul_right_comm (G := ℂ) _ _ _

lemma pow_cfc {ρ : Matrix ι ι ℂ} (hρ : ρ.IsHermitian) (a : ℕ) : ρ ^ a = cfc (fun x : ℝ => x ^ a) ρ := by
  have : IsSelfAdjoint ρ := hρ
  rw [cfc_pow (fun x : ℝ => x) a ρ, cfc_id' ℝ ρ]

lemma tr_pow {ρ : Matrix ι ι ℂ} (hρ : ρ.IsHermitian) (a : ℕ) :
    (ρ ^ a).trace.re = ∑ i, (hρ.eigenvalues i) ^ a := by
  rw [pow_cfc hρ, cfc_trace hρ, Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [Complex.ofReal_re]

lemma spec (ρ : Matrix ι ι ℂ) (hρ : ρ.IsHermitian) :
    ρ = (hρ.eigenvectorUnitary : Matrix ι ι ℂ) * diagonal (RCLike.ofReal ∘ hρ.eigenvalues : ι → ℂ) *
      star (hρ.eigenvectorUnitary : Matrix ι ι ℂ) := by
  conv_lhs => rw [hρ.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]

/-- Peierls: diagonal power sums in any orthonormal basis are dominated by the power trace. -/
lemma peierls {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ)
    (a : ℕ) :
    (∀ i, 0 ≤ ((Uᴴ * ρ * U) i i).re) ∧ ∑ i, ((Uᴴ * ρ * U) i i).re ^ a ≤ (ρ ^ a).trace.re := by
  set V := hρ.1.eigenvectorUnitary
  set lam := hρ.1.eigenvalues
  have hl0 : ∀ k, 0 ≤ lam k := hρ.eigenvalues_nonneg
  have hV := spec ρ hρ.1
  have hW : star (V : Matrix ι ι ℂ) * U ∈ Matrix.unitaryGroup ι ℂ :=
    Submonoid.mul_mem _ (Unitary.star_mem V.2) hU
  obtain ⟨hcol, hrow⟩ := ds_sums _ hW
  have hdiag : ∀ i, ((Uᴴ * ρ * U) i i).re =
      ∑ k, Complex.normSq ((star (V : Matrix ι ι ℂ) * U) k i) * lam k := by
    intro i
    rw [hV, diag_conj, Complex.re_sum]; simp only [Complex.ofReal_re]; rfl
  refine ⟨fun i => by
    rw [hdiag]; exact Finset.sum_nonneg fun k _ => mul_nonneg (Complex.normSq_nonneg _) (hl0 k), ?_⟩
  rw [tr_pow hρ.1]
  simp only [hdiag]
  calc ∑ i, (∑ k, Complex.normSq ((star (V : Matrix ι ι ℂ) * U) k i) * lam k) ^ a
      ≤ ∑ i, ∑ k, Complex.normSq ((star (V : Matrix ι ι ℂ) * U) k i) * lam k ^ a := by
        refine Finset.sum_le_sum fun i _ => ?_
        have := (convexOn_pow a).map_sum_le (t := Finset.univ)
          (w := fun k => Complex.normSq ((star (V : Matrix ι ι ℂ) * U) k i)) (p := lam)
          (fun k _ => Complex.normSq_nonneg _) (hcol i) (fun k _ => Set.mem_Ici.2 (hl0 k))
        simpa only [smul_eq_mul] using this
    _ = ∑ k, lam k ^ a := by
        rw [Finset.sum_comm]
        simp only [← Finset.sum_mul, hrow, one_mul]

lemma eig_diag {ρ : Matrix ι ι ℂ} (hρ : ρ.IsHermitian) (i : ι) :
    ((((hρ.eigenvectorUnitary : Matrix ι ι ℂ))ᴴ * ρ * (hρ.eigenvectorUnitary : Matrix ι ι ℂ)) i i).re =
      hρ.eigenvalues i := by
  set V := hρ.eigenvectorUnitary
  have h1 : star (V : Matrix ι ι ℂ) * V = 1 := Unitary.star_mul_self_of_mem V.2
  have : ((V : Matrix ι ι ℂ))ᴴ * ρ * V = diagonal (RCLike.ofReal ∘ hρ.eigenvalues : ι → ℂ) := by
    conv_lhs => rw [spec ρ hρ]
    rw [← Matrix.star_eq_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [h1, Matrix.mul_one, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [this]; simp

lemma diag_lin (U ρ₁ ρ₂ : Matrix ι ι ℂ) (s t : ℝ) (i : ι) :
    ((Uᴴ * (s • ρ₁ + t • ρ₂) * U) i i).re = s * ((Uᴴ * ρ₁ * U) i i).re + t * ((Uᴴ * ρ₂ * U) i i).re := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_apply,
    Matrix.smul_apply, Complex.add_re, Complex.real_smul, Complex.re_ofReal_mul]

/-- convexity of the power trace on PSD matrices. -/
lemma tr_convex {ρ₁ ρ₂ : Matrix ι ι ℂ} (h1 : ρ₁.PosSemidef) (h2 : ρ₂.PosSemidef) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) (a : ℕ) :
    ((s • ρ₁ + t • ρ₂) ^ a).trace.re ≤ s * (ρ₁ ^ a).trace.re + t * (ρ₂ ^ a).trace.re := by
  have hσ : (s • ρ₁ + t • ρ₂).PosSemidef :=
    (h1.smul (by exact_mod_cast hs)).add (h2.smul (by exact_mod_cast ht))
  set V := hσ.1.eigenvectorUnitary
  have hVU : (V : Matrix ι ι ℂ) ∈ Matrix.unitaryGroup ι ℂ := V.2
  obtain ⟨n1, p1⟩ := peierls h1 V hVU a
  obtain ⟨n2, p2⟩ := peierls h2 V hVU a
  rw [tr_pow hσ.1]
  simp only [← eig_diag hσ.1, diag_lin]
  calc ∑ i, (s * ((((V : Matrix ι ι ℂ))ᴴ * ρ₁ * V) i i).re + t * ((((V : Matrix ι ι ℂ))ᴴ * ρ₂ * V) i i).re) ^ a
      ≤ ∑ i, (s * ((((V : Matrix ι ι ℂ))ᴴ * ρ₁ * V) i i).re ^ a +
          t * ((((V : Matrix ι ι ℂ))ᴴ * ρ₂ * V) i i).re ^ a) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have := (convexOn_pow a).2 (Set.mem_Ici.2 (n1 i)) (Set.mem_Ici.2 (n2 i)) hs ht hst
        simpa only [smul_eq_mul] using this
    _ ≤ s * (ρ₁ ^ a).trace.re + t * (ρ₂ ^ a).trace.re := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        exact add_le_add (mul_le_mul_of_nonneg_left p1 hs) (mul_le_mul_of_nonneg_left p2 ht)

lemma conj_pow (U ρ : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) (a : ℕ) :
    (U * ρ * Uᴴ) ^ a = U * ρ ^ a * Uᴴ := by
  have h : Uᴴ * U = 1 := (Matrix.mem_unitaryGroup_iff').1 hU
  have h' : U * Uᴴ = 1 := (Matrix.mem_unitaryGroup_iff).1 hU
  induction a with
  | zero => simp [h']
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, h, Matrix.one_mul]

theorem marginal (a : ℕ) : IsMarginalCost (powerPurityCost (I := ι) a) := by
  refine ⟨?_, ?_, ?_⟩
  · apply Continuous.continuousOn
    unfold powerPurityCost
    fun_prop
  · intro rho _ U
    unfold powerPurityCost
    rw [conj_pow _ _ U.2, Matrix.trace_mul_cycle, ← Matrix.star_eq_conjTranspose,
      (Matrix.mem_unitaryGroup_iff').1 U.2, Matrix.one_mul]
  · refine ⟨?_, ?_⟩
    · intro x hx y hy s t hs ht hst
      obtain ⟨hx1, hx2⟩ := hx
      obtain ⟨hy1, hy2⟩ := hy
      refine ⟨(hx1.smul (by exact_mod_cast hs)).add (hy1.smul (by exact_mod_cast ht)), ?_⟩
      rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hx2, hy2]
      simp only [Complex.real_smul, mul_one]
      exact_mod_cast hst
    · intro x hx y hy s t hs ht hst
      have := tr_convex hx.1 hy.1 hs ht hst a
      simp only [powerPurityCost, smul_eq_mul]
      have e : s * (2 * (1 - (x ^ a).trace.re)) + t * (2 * (1 - (y ^ a).trace.re)) =
          2 * ((s + t) - (s * (x ^ a).trace.re + t * (y ^ a).trace.re)) := by ring
      rw [e, hst]
      linarith

lemma pure_pow {ρ : Matrix ι ι ℂ} (h : IsPure ρ) {a : ℕ} (ha : 1 ≤ a) : ρ ^ a = ρ := by
  obtain ⟨v, hv, rfl⟩ := h
  have hp := (X4OC.pure_proj v hv).1
  induction a, ha using Nat.le_induction with
  | base => simp
  | succ n _ ih => rw [pow_succ, ih, hp]

lemma pure_cost {ρ : Matrix ι ι ℂ} (h : IsPure ρ) {a : ℕ} (ha : 1 ≤ a) : powerPurityCost a ρ = 0 := by
  obtain ⟨v, hv, he⟩ := h
  rw [powerPurityCost, pure_pow ⟨v, hv, he⟩ ha, he, (X4OC.pure_proj v hv).2.1]
  simp

/-- PSD trace-one matrices with `Re tr ρ^a = 1`, `a > 1`, are idempotent. -/
lemma idem_of {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) (h1 : ρ.trace = 1) {a : ℕ} (ha : 1 < a)
    (h : (ρ ^ a).trace.re = 1) : ρ * ρ = ρ := by
  set lam := hρ.1.eigenvalues
  have hl0 : ∀ k, 0 ≤ lam k := hρ.eigenvalues_nonneg
  have hsum : ∑ k, lam k = 1 := by
    have := hρ.1.trace_eq_sum_eigenvalues
    rw [h1] at this
    have h3 : ((∑ k, lam k : ℝ) : ℂ) = 1 := by push_cast; exact this.symm
    exact_mod_cast h3
  have hle1 : ∀ k, lam k ≤ 1 := fun k => by
    rw [← hsum]; exact Finset.single_le_sum (fun j _ => hl0 j) (Finset.mem_univ k)
  have hpa : ∑ k, lam k ^ a = 1 := by rw [← tr_pow hρ.1]; exact h
  have hle : ∀ k, lam k ^ a ≤ lam k := fun k => pow_le_of_le_one (hl0 k) (hle1 k) (by omega)
  have heq : ∀ k, lam k ^ a = lam k := by
    have hz : ∑ k, (lam k - lam k ^ a) = 0 := by rw [Finset.sum_sub_distrib, hsum, hpa, sub_self]
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sub_nonneg.2 (hle k))).1 hz
    intro k; linarith [this k (Finset.mem_univ k)]
  have h01 : ∀ k, lam k * lam k = lam k := by
    intro k
    rcases (hl0 k).eq_or_lt with h0 | h0
    · rw [← h0]; simp
    rcases (hle1 k).eq_or_lt with h1' | h1'
    · rw [h1']; simp
    exfalso
    have := pow_lt_self_of_lt_one₀ h0 h1' ha
    linarith [heq k]
  have : IsSelfAdjoint ρ := hρ.1
  have hsq : ρ * ρ = cfc (fun x : ℝ => x * x) ρ := by
    rw [cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) ρ, cfc_id' ℝ ρ]
  rw [hsq]
  conv_rhs => rw [← cfc_id' ℝ ρ]
  refine cfc_congr fun x hx => ?_
  rw [Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues hρ.1] at hx
  obtain ⟨k, rfl⟩ := hx
  exact h01 k

variable {κ : Type} [Fintype κ] [DecidableEq κ]

lemma unit_sum (v : EuclideanSpace ℂ ι) (hv : ‖v‖ = 1) : ∑ i, v i * conj (v i) = 1 := by
  have := (X4OC.pure_proj v hv).2.1
  simpa [Matrix.trace, pureDensity] using this

lemma tr_ent (ψ : EuclideanSpace ℂ (ι × κ)) (j k : ι) :
    traceRight (pureDensity ψ) j k = ∑ h, ψ (j, h) * conj (ψ (k, h)) := by
  simp [traceRight, pureDensity]

lemma marg_psd (ψ : EuclideanSpace ℂ (ι × κ)) (hψ : ‖ψ‖ = 1) :
    (traceRight (pureDensity ψ)).PosSemidef ∧ (traceRight (pureDensity ψ)).trace = 1 := by
  set W : Matrix ι κ ℂ := Matrix.of fun j h => ψ (j, h)
  have hW : traceRight (pureDensity ψ) = W * Wᴴ := by
    ext j k
    rw [tr_ent, Matrix.mul_apply]
    simp [W, conjTranspose_apply]
  refine ⟨hW ▸ posSemidef_self_mul_conjTranspose W, ?_⟩
  rw [Matrix.trace]
  simp only [Matrix.diag, tr_ent]
  rw [← unit_sum ψ hψ, Fintype.sum_prod_type]

lemma marg_prod (u : EuclideanSpace ℂ ι) (v : EuclideanSpace ℂ κ) (hv : ‖v‖ = 1) :
    traceRight (pureDensity (tensorVec u v)) = pureDensity u := by
  ext j k
  rw [tr_ent]
  simp only [tensorVec, PiLp.toLp_apply, map_mul, pureDensity, Matrix.of_apply]
  have := unit_sum v hv
  calc ∑ h, u j * v h * (conj (u k) * conj (v h)) = u j * conj (u k) * ∑ h, v h * conj (v h) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun h _ => by ring
    _ = _ := by rw [this, mul_one]

/-- a state whose marginal is pure is a product state. -/
lemma prod_of_pure (ψ : EuclideanSpace ℂ (ι × κ)) (hψ : ‖ψ‖ = 1) (u : EuclideanSpace ℂ ι) (hu : ‖u‖ = 1)
    (h : traceRight (pureDensity ψ) = pureDensity u) :
    ∃ v : EuclideanSpace ℂ κ, ‖v‖ = 1 ∧ ψ = tensorVec u v := by
  set v : EuclideanSpace ℂ κ := WithLp.toLp 2 (fun h => ∑ i, conj (u i) * ψ (i, h))
  have hvk : ∀ h, v h = ∑ i, conj (u i) * ψ (i, h) := fun h => rfl
  have hU := unit_sum u hu
  have hP := unit_sum ψ hψ
  have hρ : ∀ j k, ∑ h, ψ (j, h) * conj (ψ (k, h)) = u j * conj (u k) := by
    intro j k
    rw [← tr_ent, h]; rfl
  -- N = Σ |v|² = 1
  have hN : ∑ h, v h * conj (v h) = 1 := by
    calc ∑ h, v h * conj (v h)
        = ∑ i, ∑ j, conj (u i) * u j * ∑ h, ψ (i, h) * conj (ψ (j, h)) := by
          simp only [hvk, map_sum, map_mul, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          conv_rhs => rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun h _ => ?_
          ring
      _ = (∑ i, u i * conj (u i)) * (∑ j, u j * conj (u j)) := by
          simp only [hρ, Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          ring
      _ = 1 := by rw [hU, one_mul]
  have hvn : ‖v‖ = 1 := by
    have h2 : ((‖v‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [EuclideanSpace.norm_sq_eq]; push_cast
      rw [← hN]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
    have h3 : ‖v‖ ^ 2 = 1 := by exact_mod_cast h2
    have := norm_nonneg v
    nlinarith
  refine ⟨v, hvn, ?_⟩
  -- E = Σ |ψ - u ⊗ v|² = 0
  set e : ι × κ → ℂ := fun p => ψ p - u p.1 * v p.2
  have hB : ∑ p : ι × κ, ψ p * conj (u p.1 * v p.2) = 1 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm, ← hN]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [hvk, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul]; ring
  have hD : ∑ p : ι × κ, u p.1 * v p.2 * conj (u p.1 * v p.2) = 1 := by
    rw [Fintype.sum_prod_type]
    calc ∑ i, ∑ h, u i * v h * conj (u i * v h) = ∑ i, u i * conj (u i) * ∑ h, v h * conj (v h) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun h _ => ?_
          rw [map_mul]; ring
      _ = 1 := by rw [hN]; simp [hU]
  have hE : ∑ p, e p * conj (e p) = 0 := by
    have hC : ∑ p : ι × κ, u p.1 * v p.2 * conj (ψ p) = 1 := by
      have := congrArg conj hB
      rw [map_sum, map_one] at this
      rw [← this]; refine Finset.sum_congr rfl fun p _ => ?_
      rw [map_mul, Complex.conj_conj]; ring
    calc ∑ p, e p * conj (e p) = ∑ p : ι × κ, ψ p * conj (ψ p) - ∑ p : ι × κ, ψ p * conj (u p.1 * v p.2)
          - ∑ p : ι × κ, u p.1 * v p.2 * conj (ψ p) + ∑ p : ι × κ, u p.1 * v p.2 * conj (u p.1 * v p.2) := by
          rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun p _ => ?_
          simp only [e, map_sub]; ring
      _ = 0 := by rw [hP, hB, hC, hD]; ring
  have hE' : ∀ p, e p = 0 := by
    have h2 : ((∑ p, Complex.normSq (e p) : ℝ) : ℂ) = 0 := by
      rw [← hE]; push_cast
      exact Finset.sum_congr rfl fun p _ => (Complex.mul_conj (e p)).symm
    have h3 : ∑ p, Complex.normSq (e p) = 0 := by exact_mod_cast h2
    intro p
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => Complex.normSq_nonneg (e p))).1 h3 p
      (Finset.mem_univ p)
    exact Complex.normSq_eq_zero.1 this
  ext p
  have := hE' p
  simp only [e, sub_eq_zero] at this
  simp [tensorVec, this]

theorem zero_iff (ψ : EuclideanSpace ℂ (ι × κ)) (hψ : IsState ψ) {a : ℕ} (ha : 1 < a) :
    powerPurityCost a (traceRight (pureDensity ψ)) = 0 ↔
      ∃ u : EuclideanSpace ℂ ι, ∃ v : EuclideanSpace ℂ κ, IsState u ∧ IsState v ∧ ψ = tensorVec u v := by
  obtain ⟨hpsd, htr⟩ := marg_psd ψ hψ
  constructor
  · intro h0
    have h1 : ((traceRight (pureDensity ψ)) ^ a).trace.re = 1 := by
      unfold powerPurityCost at h0; linarith
    have hi := idem_of hpsd htr ha h1
    obtain ⟨u, hu, he⟩ := X4OC.proj_pure hpsd.1 hi htr
    obtain ⟨v, hv, hpv⟩ := prod_of_pure ψ hψ u hu he
    exact ⟨u, v, hu, hv, hpv⟩
  · rintro ⟨u, v, hu, hv, rfl⟩
    rw [marg_prod u v hv]
    exact pure_cost ⟨u, hu, rfl⟩ (by omega)

end X4PP

-- ===== P35PSol =====

noncomputable section

open scoped Matrix ComplexConjugate Topology Manifold

namespace QAlgorithms.Papers.Independent.Support50.P35

theorem _root_.solution (M N a : ℕ) (hN : 0 < N) (hNM : N ≤ M) (ha : 1 < a) :
    IsMarginalCost (powerPurityCost (I := Fin M) a) ∧
    (∀ rho : Matrix (Fin M) (Fin M) ℂ, QAlgorithms.Papers.Independent.Information100.P08.IsPure rho → powerPurityCost a rho = 0) ∧
    (∀ psi : EuclideanSpace ℂ (Fin M × Fin N), IsState psi →
      (powerPurityCost a (traceRight (pureDensity psi)) = 0 ↔
        ∃ u : EuclideanSpace ℂ (Fin M), ∃ v : EuclideanSpace ℂ (Fin N),
          IsState u ∧ IsState v ∧ psi = tensorVec u v)) :=
  ⟨X4PP.marginal a, fun _ h => X4PP.pure_cost h (by omega), fun psi h => X4PP.zero_iff psi h ha⟩

end QAlgorithms.Papers.Independent.Support50.P35

end

#print axioms solution
