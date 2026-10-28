-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P35.formation_coordinate_roof
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:08:00.70187+00:00
-- url     : https://prove2.me/submissions/ffb5c880-a51c-41da-afc1-173a7aa8bfb0

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

-- ===== P35F =====

noncomputable section

namespace X4PF
open Matrix QAlgorithms QAlgorithms.Papers.Independent.Support50.P35
open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)
open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble convexRoof)
open scoped Matrix ComplexConjugate ComplexOrder

variable {I : Type} [Fintype I] [DecidableEq I] {K : Type} [Fintype K] [DecidableEq K]

lemma coord_sum {n : ℕ} (mu : K → Matrix I I ℂ) (w : Fin n → ℝ) (X : Fin n → Matrix I I ℂ) :
    hermitianCoordinates mu (∑ j, (w j : ℂ) • X j) = ∑ j, w j • hermitianCoordinates mu (X j) := by
  funext g
  simp only [hermitianCoordinates, Finset.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul,
    smul_eq_mul, Complex.re_sum, Complex.re_ofReal_mul, Finset.sum_apply, Pi.smul_apply]

lemma recon_sum {n : ℕ} (mu : K → Matrix I I ℂ) (w : Fin n → ℝ) (c : Fin n → K → ℝ) :
    hermitianReconstruction mu (∑ j, w j • c j) = ∑ j, (w j : ℂ) • hermitianReconstruction mu (c j) := by
  simp only [hermitianReconstruction, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_sum,
    Complex.ofReal_mul, Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

lemma recon_coord {mu : K → Matrix I I ℂ} (hmu : IsHermitianONBasis mu) {X : Matrix I I ℂ}
    (hX : X.IsHermitian) : hermitianReconstruction mu (hermitianCoordinates mu X) = X := by
  conv_rhs => rw [X4OC.herm_expand hmu hX]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [hermitianCoordinates, X4OB.tr_real hX (hmu.1 g)]

lemma ens_iff {mu : K → Matrix I I ℂ} (hmu : IsHermitianONBasis mu) {rho : Matrix I I ℂ}
    (hrho : rho.IsHermitian) (e : PureEnsemble I) :
    ensembleDensity e.weight e.vector = rho ↔
      (∑ j, e.weight j • hermitianCoordinates mu (pureDensity (e.vector j))) = hermitianCoordinates mu rho := by
  rw [← coord_sum]
  constructor
  · intro h; rw [← h]; rfl
  · intro h
    have := congrArg (hermitianReconstruction mu) h
    rw [recon_coord hmu hrho, recon_coord hmu] at this
    · exact this
    · rw [IsHermitian, conjTranspose_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [conjTranspose_smul, (X4OC.pure_proj _ (e.normalized j)).2.2.eq]
      simp

variable {M N : ℕ}

theorem main (mu : Fin ((M * N) ^ 2) → Matrix (Fin M × Fin N) (Fin M × Fin N) ℂ)
    (hmu : IsHermitianONBasis mu) (f : Matrix (Fin M) (Fin M) ℂ → ℝ)
    (rho : Matrix (Fin M × Fin N) (Fin M × Fin N) ℂ) (hrho : IsDensityMatrix rho) :
    formationValues f rho =
      roofValues (generalPureSet mu) (coordinateCost mu f) (hermitianCoordinates mu rho) ∧
    convexRoof (fun psi => f (traceRight (pureDensity psi))) rho =
      lowerRoof (generalPureSet mu) (coordinateCost mu f) (hermitianCoordinates mu rho) ∧
    (∀ e : PureEnsemble (Fin M × Fin N),
      ensembleDensity e.weight e.vector = rho ↔
        (∑ j, e.weight j • hermitianCoordinates mu (pureDensity (e.vector j))) = hermitianCoordinates mu rho) := by
  have hH := hrho.1.1
  have hset : formationValues f rho =
      roofValues (generalPureSet mu) (coordinateCost mu f) (hermitianCoordinates mu rho) := by
    ext z
    constructor
    · rintro ⟨e, he, rfl⟩
      have hpos : 0 < e.count := by
        rcases Nat.eq_zero_or_pos e.count with h0 | h0
        · exfalso
          have := e.total
          have hz : ∑ k : Fin e.count, e.weight k = 0 := by
            have : IsEmpty (Fin e.count) := by rw [h0]; exact Fin.isEmpty'
            exact Finset.sum_of_isEmpty _
          linarith
        · exact h0
      refine ⟨⟨e.count, hpos, fun j => hermitianCoordinates mu (pureDensity (e.vector j)),
        fun j => X4OC.coord_pure hmu _ (e.normalized j), e.weight, e.nonnegative, e.total,
        (ens_iff hmu hH e).1 he⟩, ?_⟩
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [coordinateCost]
      rw [recon_coord hmu (X4OC.pure_proj _ (e.normalized j)).2.2]
    · rintro ⟨d, rfl⟩
      have hv : ∀ j, ∃ v : EuclideanSpace ℂ (Fin M × Fin N), ‖v‖ = 1 ∧
          hermitianReconstruction mu (d.point j) = pureDensity v :=
        fun j => (X4OC.pure_iff hmu (d.point j)).2 (d.member j)
      choose v hv1 hv2 using hv
      let e : PureEnsemble (Fin M × Fin N) :=
        ⟨d.count, d.weight, v, d.nonnegative, d.total, hv1⟩
      refine ⟨e, ?_, ?_⟩
      · show ∑ j, (d.weight j : ℂ) • pureDensity (v j) = rho
        simp only [← hv2]
        rw [← recon_sum, d.barycenter, recon_coord hmu hH]
      · refine Finset.sum_congr rfl fun j _ => ?_
        simp only [coordinateCost, hv2]
        rfl
  refine ⟨hset, ?_, fun e => ens_iff hmu hH e⟩
  rw [lowerRoof, ← hset]
  rfl

end X4PF

-- ===== P35FSol =====

noncomputable section

open scoped Matrix ComplexConjugate Topology Manifold

namespace QAlgorithms.Papers.Independent.Support50.P35

theorem _root_.solution (M N : ℕ) (hN : 0 < N) (hNM : N ≤ M)
    (f : Matrix (Fin M) (Fin M) ℂ → ℝ) (hf : IsMarginalCost f)
    (mu : Fin ((M * N) ^ 2) → Matrix (Fin M × Fin N) (Fin M × Fin N) ℂ)
    (hmu : IsHermitianONBasis mu)
    (rho : Matrix (Fin M × Fin N) (Fin M × Fin N) ℂ) (hrho : IsDensityMatrix rho) :
    formationValues f rho =
      roofValues (generalPureSet mu) (coordinateCost mu f) (hermitianCoordinates mu rho) ∧
    QAlgorithms.Papers.Independent.Information100.P03.convexRoof (fun psi => f (traceRight (pureDensity psi))) rho =
      lowerRoof (generalPureSet mu) (coordinateCost mu f) (hermitianCoordinates mu rho) ∧
    (∀ e : QAlgorithms.Papers.Independent.Information100.P03.PureEnsemble (Fin M × Fin N),
      ensembleDensity e.weight e.vector = rho ↔
        (∑ j, e.weight j • hermitianCoordinates mu (pureDensity (e.vector j))) = hermitianCoordinates mu rho) :=
  X4PF.main mu hmu f rho hrho

end QAlgorithms.Papers.Independent.Support50.P35

end

#print axioms solution
