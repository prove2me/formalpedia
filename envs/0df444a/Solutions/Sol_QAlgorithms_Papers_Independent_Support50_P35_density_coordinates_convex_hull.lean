-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P35.density_coordinates_convex_hull
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T08:45:23.669117+00:00
-- url     : https://prove2.me/submissions/0e75d078-8fa3-4571-bc24-cae87608dc98

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

-- ===== P35G =====

noncomputable section

namespace X4GM
open Matrix QAlgorithms QAlgorithms.Papers.Independent.Support50.P35
open scoped Matrix ComplexConjugate

/-- `n²` orthonormal Hermitian matrices are complete. -/
lemma complete {n : ℕ} {K : Type*} [Fintype K] [DecidableEq K] (g : K → Matrix (Fin n) (Fin n) ℂ)
    (hh : ∀ k, (g k).IsHermitian) (ho : ∀ j k, (g j * g k).trace = if j = k then 1 else 0)
    (hc : Fintype.card K = n * n) :
    ∀ A : Matrix (Fin n) (Fin n) ℂ, A.IsHermitian → ∃ c : K → ℝ, A = ∑ k, (c k : ℂ) • g k := by
  have hli : LinearIndependent ℂ g := by
    rw [Fintype.linearIndependent_iff]
    intro z hz j
    have := congrArg (fun M => (M * g j).trace) hz
    simp only [Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul, ho, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.zero_mul,
      Matrix.trace_zero] at this
    exact this
  have hspan : Submodule.span ℂ (Set.range g) = ⊤ := by
    apply hli.span_eq_top_of_card_eq_finrank'
    rw [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one, hc]
  intro A hA
  have hmem : A ∈ Submodule.span ℂ (Set.range g) := by rw [hspan]; trivial
  obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
  have hzk : ∀ k, z k = (A * g k).trace := by
    intro k
    rw [← hz]
    simp only [Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul, ho, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine ⟨fun k => (A * g k).trace.re, ?_⟩
  conv_lhs => rw [← hz]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only
  rw [X4OB.tr_real hA (hh k), hzk]

open Finset in
lemma card_lt (D : ℕ) : 2 * Fintype.card {p : Fin D × Fin D // p.1 < p.2} + D = D * D := by
  rw [Fintype.card_subtype]
  have hswap : #({p : Fin D × Fin D | p.2 < p.1} : Finset _) = #({p : Fin D × Fin D | p.1 < p.2} : Finset _) := by
    refine Finset.card_bij (fun p _ => p.swap) ?_ ?_ ?_
    · intro p hp; simpa using hp
    · intro p _ q _ h; simpa using h
    · intro q hq; exact ⟨q.swap, by simpa using hq, by simp⟩
  have hoff : #((univ : Finset (Fin D)).offDiag) = D * D - D := by
    rw [Finset.offDiag_card]; simp
  have hsplit : (univ : Finset (Fin D)).offDiag =
      ({p : Fin D × Fin D | p.1 < p.2} : Finset _) ∪ ({p : Fin D × Fin D | p.2 < p.1} : Finset _) := by
    ext p; simp only [Finset.mem_offDiag, mem_univ, true_and, mem_union, mem_filter]; exact ⟨fun h => lt_or_gt_of_ne h, fun h => h.elim ne_of_lt ne_of_gt⟩
  have hdisj : Disjoint ({p : Fin D × Fin D | p.1 < p.2} : Finset _) ({p : Fin D × Fin D | p.2 < p.1} : Finset _) := by
    rw [Finset.disjoint_filter]; intro p _ h1 h2; exact lt_asymm h1 h2
  rw [hsplit, Finset.card_union_of_disjoint hdisj, hswap] at hoff
  have : D ≤ D * D := Nat.le_mul_self D
  omega

open Finset in
lemma card_pos (D : ℕ) (hD : 0 < D) : Fintype.card {a : Fin D // 0 < a.val} = D - 1 := by
  rw [Fintype.card_subtype]
  have : ({a : Fin D | 0 < a.val} : Finset _) = univ.erase ⟨0, hD⟩ := by
    ext a; simp [Fin.ext_iff, Nat.pos_iff_ne_zero]
  rw [this, Finset.card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]

/-- numerators of the diagonal generators. -/
def numN (a i : ℕ) : ℝ := if i < a then 1 else if i = a then -(a : ℝ) else 0

lemma sum_numN (a n : ℕ) : ∑ i ∈ Finset.range n, numN a i = if n ≤ a then (n : ℝ) else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    unfold numN
    by_cases h1 : n + 1 ≤ a
    · rw [if_pos (by omega), if_pos h1, if_pos (by omega)]; push_cast; ring
    · rw [if_neg h1]
      by_cases h2 : n = a
      · subst h2; simp
      · rw [if_neg (by omega), if_neg (by omega), if_neg h2]; simp

lemma sum_numN2 (a n : ℕ) :
    ∑ i ∈ Finset.range n, numN a i ^ 2 = if n ≤ a then (n : ℝ) else a + (a : ℝ) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    unfold numN
    by_cases h1 : n + 1 ≤ a
    · rw [if_pos (by omega), if_pos h1, if_pos (by omega)]; push_cast; ring
    · rw [if_neg h1]
      by_cases h2 : n = a
      · subst h2; simp
      · rw [if_neg (by omega), if_neg (by omega), if_neg h2]; simp

lemma numN_mul {a b : ℕ} (hab : a < b) (i : ℕ) : numN a i * numN b i = numN a i := by
  unfold numN
  split_ifs <;> first | ring1 | (exfalso; omega) | (simp_all; omega)

variable {D : ℕ}

/-- off-diagonal two-entry matrices. -/
def offM (p : PairIndex D) (x y : ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  fun i j => if i = p.1.1 ∧ j = p.1.2 then x else if i = p.1.2 ∧ j = p.1.1 then y else 0

lemma sum_offM (p : PairIndex D) (x y : ℂ) (F : Fin D → Fin D → ℂ) :
    ∑ i, ∑ j, offM p x y i j * F i j = x * F p.1.1 p.1.2 + y * F p.1.2 p.1.1 := by
  have hp : p.1.1 ≠ p.1.2 := ne_of_lt p.2
  have e : ∀ i j, offM p x y i j * F i j =
      (if i = p.1.1 then (if j = p.1.2 then x * F i j else 0) else 0) +
      (if i = p.1.2 then (if j = p.1.1 then y * F i j else 0) else 0) := by
    intro i j
    simp only [offM]
    by_cases h1 : i = p.1.1 <;> by_cases h2 : j = p.1.2 <;> by_cases h3 : i = p.1.2 <;>
      by_cases h4 : j = p.1.1 <;> simp_all
  simp only [e, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp

lemma tr_off (p : PairIndex D) (x y : ℂ) : (offM p x y).trace = 0 := by
  have hp : p.1.1 ≠ p.1.2 := ne_of_lt p.2
  simp only [Matrix.trace, Matrix.diag, offM]
  refine Finset.sum_eq_zero fun i _ => ?_
  split_ifs with h1 h2
  · exact absurd (h1.1.symm.trans h1.2) hp
  · exact absurd (h2.1.symm.trans h2.2) hp.symm
  · rfl

lemma tr_off_off (p q : PairIndex D) (x y x' y' : ℂ) :
    (offM p x y * offM q x' y').trace = if p = q then x * y' + y * x' else 0 := by
  rw [Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_apply]
  rw [sum_offM p x y (fun i j => offM q x' y' j i)]
  have hp := p.2
  have hq := q.2
  simp only [offM]
  by_cases hpq : p = q
  · subst hpq
    have hne : p.1.2 ≠ p.1.1 := (ne_of_lt hp).symm
    simp [hne]
  · rw [if_neg hpq]
    rw [Fin.lt_iff_val_lt_val] at hp hq
    have n1 : ¬ (p.1.2 = q.1.1 ∧ p.1.1 = q.1.2) := fun ⟨h1, h2⟩ => by
      rw [Fin.ext_iff] at h1 h2; omega
    have n2 : ¬ (p.1.2 = q.1.2 ∧ p.1.1 = q.1.1) := fun ⟨h1, h2⟩ => hpq (Subtype.ext (Prod.ext h2 h1))
    have n3 : ¬ (p.1.1 = q.1.1 ∧ p.1.2 = q.1.2) := fun ⟨h1, h2⟩ => hpq (Subtype.ext (Prod.ext h1 h2))
    have n4 : ¬ (p.1.1 = q.1.2 ∧ p.1.2 = q.1.1) := fun ⟨h1, h2⟩ => by
      rw [Fin.ext_iff] at h1 h2; omega
    rw [if_neg n1, if_neg n2, if_neg n3, if_neg n4]; ring

/-- diagonal entries -/
def dd (a : {a : Fin D // 0 < a.val}) (i : Fin D) : ℝ :=
  numN a.val.val i.val / Real.sqrt (((a.val.val : ℝ) + 1) * a.val.val)

lemma gen_inl (a : {a : Fin D // 0 < a.val}) :
    normOneGellmannGenerator (Sum.inl a) = diagonal (fun i => ((dd a i : ℝ) : ℂ)) := by
  ext i j
  simp only [normOneGellmannGenerator, diagonal, Matrix.of_apply, dd, numN, Fin.ext_iff]

lemma gen_false (p : PairIndex D) :
    normOneGellmannGenerator (Sum.inr (p, false)) =
      offM p (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) := by
  have hp : p.1.1 ≠ p.1.2 := ne_of_lt p.2
  ext i j
  simp only [normOneGellmannGenerator, offM]
  by_cases h1 : i = p.1.1 <;> by_cases h2 : j = p.1.2 <;> by_cases h3 : i = p.1.2 <;>
    by_cases h4 : j = p.1.1 <;> simp_all

lemma gen_true (p : PairIndex D) :
    normOneGellmannGenerator (Sum.inr (p, true)) =
      offM p (-Complex.I / (Real.sqrt 2 : ℂ)) (Complex.I / (Real.sqrt 2 : ℂ)) := rfl

lemma tr_diag_off (d : Fin D → ℂ) (p : PairIndex D) (x y : ℂ) :
    (diagonal d * offM p x y).trace = 0 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hp : p.1.1 ≠ p.1.2 := ne_of_lt p.2
  simp only [offM]
  split_ifs with h1 h2
  · exact absurd (h1.1.symm.trans h1.2) hp
  · exact absurd (h2.1.symm.trans h2.2) hp.symm
  · ring

lemma sqrt_sq_pos (a : {a : Fin D // 0 < a.val}) :
    Real.sqrt (((a.val.val : ℝ) + 1) * a.val.val) ^ 2 = ((a.val.val : ℝ) + 1) * a.val.val := by
  rw [Real.sq_sqrt]; positivity

lemma dd_sum (a : {a : Fin D // 0 < a.val}) : ∑ i, dd a i = 0 := by
  simp only [dd, ← Finset.sum_div]
  rw [Fin.sum_univ_eq_sum_range (fun i => numN a.val.val i), sum_numN, if_neg (by omega)]
  simp

lemma dd_orth (a b : {a : Fin D // 0 < a.val}) :
    ∑ i, dd a i * dd b i = if a = b then 1 else 0 := by
  have key : ∀ a b : {a : Fin D // 0 < a.val}, a.val.val < b.val.val → ∑ i, dd a i * dd b i = 0 := by
    intro a b hab
    simp only [dd, div_mul_div_comm, ← Finset.sum_div]
    simp_rw [numN_mul hab]
    rw [Fin.sum_univ_eq_sum_range (fun i => numN a.val.val i), sum_numN, if_neg (by omega)]
    simp
  split_ifs with h
  · subst h
    simp only [dd, ← pow_two, div_pow, ← Finset.sum_div]
    rw [Fin.sum_univ_eq_sum_range (fun i => numN a.val.val i ^ 2), sum_numN2, if_neg (by omega),
      sqrt_sq_pos]
    have : (0 : ℝ) < a.val.val := by exact_mod_cast a.2
    field_simp
    ring
  · rcases lt_trichotomy a.val.val b.val.val with hab | hab | hab
    · exact key a b hab
    · exact absurd (Subtype.ext (Fin.ext hab)) h
    · rw [← key b a hab]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma offM_herm (p : PairIndex D) (x y : ℂ) (h : y = conj x) : (offM p x y).IsHermitian := by
  have hp : p.1.1 ≠ p.1.2 := ne_of_lt p.2
  ext i j
  simp only [conjTranspose_apply, offM, h]
  by_cases h1 : j = p.1.1 <;> by_cases h2 : i = p.1.2 <;> by_cases h3 : j = p.1.2 <;>
    by_cases h4 : i = p.1.1 <;> simp_all

lemma herm_gen (j : TracelessIndex D) : (normOneGellmannGenerator j).IsHermitian := by
  rcases j with a | ⟨p, _ | _⟩
  · rw [gen_inl]; ext i j; simp [diagonal, conjTranspose_apply]; split_ifs <;> simp_all
  · rw [gen_false]; exact offM_herm p _ _ (by simp)
  · rw [gen_true]; refine offM_herm p _ _ ?_
    simp [map_div₀, Complex.conj_ofReal]

lemma tr_gen (j : TracelessIndex D) : (normOneGellmannGenerator j).trace = 0 := by
  rcases j with a | ⟨p, _ | _⟩
  · rw [gen_inl, trace_diagonal, ← Complex.ofReal_sum, dd_sum, Complex.ofReal_zero]
  · rw [gen_false, tr_off]
  · rw [gen_true, tr_off]

lemma s2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

lemma s2ne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
  have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  exact_mod_cast this.ne'

lemma orth_gen (j k : TracelessIndex D) :
    (normOneGellmannGenerator j * normOneGellmannGenerator k).trace = if j = k then 1 else 0 := by
  rcases j with a | ⟨p, _ | _⟩ <;> rcases k with b | ⟨q, _ | _⟩
  · rw [gen_inl, gen_inl, diagonal_mul_diagonal, trace_diagonal]
    have : ∑ i, ((dd a i : ℝ) : ℂ) * ((dd b i : ℝ) : ℂ) = ((∑ i, dd a i * dd b i : ℝ) : ℂ) := by
      push_cast; rfl
    rw [this, dd_orth]
    by_cases h : a = b <;> simp [h]
  all_goals first
    | (rw [gen_inl, gen_false, tr_diag_off]; simp)
    | (rw [gen_inl, gen_true, tr_diag_off]; simp)
    | (rw [Matrix.trace_mul_comm, gen_inl, gen_false, tr_diag_off]; simp)
    | (rw [Matrix.trace_mul_comm, gen_inl, gen_true, tr_diag_off]; simp)
    | skip
  all_goals
    first
    | rw [gen_false, gen_false, tr_off_off]
    | rw [gen_false, gen_true, tr_off_off]
    | rw [gen_true, gen_false, tr_off_off]
    | rw [gen_true, gen_true, tr_off_off]
  all_goals
    by_cases h : p = q
    · subst h
      simp only [if_true, Sum.inr.injEq, Prod.mk.injEq, true_and]
      push_cast
      field_simp [s2ne]
      rw [show ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 by rw [sq, s2]]
      try simp
      try (rw [Complex.I_sq]; norm_num)
      try norm_num
    · simp [h]

lemma card_T (hD : 0 < D) : Fintype.card (TracelessIndex D) = D ^ 2 - 1 := by
  have h1 : 2 * Fintype.card (PairIndex D) + D = D * D := card_lt D
  have h2 := card_pos D hD
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, h2]
  have : D ≤ D * D := Nat.le_mul_self D
  rw [sq]; omega

lemma sD (hD : 0 < D) : ((Real.sqrt D : ℝ) : ℂ)⁻¹ * ((Real.sqrt D : ℝ) : ℂ)⁻¹ = (D : ℂ)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]; push_cast; rfl

lemma gm_herm (j : FullIndex D) : (gellmann D j).IsHermitian := by
  rcases j with _ | j
  · simp only [gellmann]
    rw [IsHermitian, conjTranspose_smul, conjTranspose_one]
    simp [Complex.conj_ofReal]
  · exact herm_gen j

lemma gm_orth (hD : 0 < D) (j k : FullIndex D) :
    (gellmann D j * gellmann D k).trace = if j = k then 1 else 0 := by
  rcases j with _ | j <;> rcases k with _ | k
  · simp only [gellmann, smul_mul_smul_comm, Matrix.one_mul, Matrix.trace_smul, Matrix.trace_one,
      Fintype.card_fin, smul_eq_mul, if_true]
    rw [sD hD]; field_simp
    exact div_self (by exact_mod_cast hD.ne')
  · simp only [gellmann, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, tr_gen, smul_zero]; simp
  · simp only [gellmann, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, tr_gen, smul_zero]; simp
  · simp only [gellmann, orth_gen, Option.some.injEq]

lemma gm_basis (hD : 0 < D) : IsHermitianONBasis (gellmann D) := by
  refine ⟨gm_herm, gm_orth hD, complete _ gm_herm (gm_orth hD) ?_⟩
  rw [Fintype.card_option, card_T hD, sq]
  have : 1 ≤ D * D := Nat.one_le_iff_ne_zero.2 (by positivity)
  omega

lemma conj_tr (j k l : TracelessIndex D) :
    (normOneGellmannGenerator k * normOneGellmannGenerator j * normOneGellmannGenerator l).trace =
      conj (normOneGellmannGenerator j * normOneGellmannGenerator k * normOneGellmannGenerator l).trace := by
  rw [← RCLike.star_def, ← Matrix.trace_conjTranspose]
  simp only [Matrix.conjTranspose_mul, (herm_gen _).eq]
  rw [Matrix.trace_mul_cycle, Matrix.mul_assoc]

lemma prod_gen (hD : 0 < D) (j k : TracelessIndex D) :
    normOneGellmannGenerator j * normOneGellmannGenerator k =
      (if j = k then (D : ℂ)⁻¹ else 0) • (1 : Matrix (Fin D) (Fin D) ℂ) +
      ∑ l, ((symmetricConstant j k l : ℂ) + Complex.I * antisymmetricConstant j k l) •
        normOneGellmannGenerator l := by
  conv_lhs => rw [X4OC.all_expand (gm_basis hD) (normOneGellmannGenerator j * normOneGellmannGenerator k)]
  rw [Fintype.sum_option]
  congr 1
  · simp only [gellmann, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, orth_gen, smul_smul]
    congr 1
    split_ifs <;> simp [sD hD, mul_comm]
  · refine Finset.sum_congr rfl fun l _ => ?_
    congr 1
    simp only [gellmann, symmetricConstant, antisymmetricConstant]
    rw [mul_comm Complex.I]; exact (Complex.re_add_im _).symm

end X4GM

-- ===== P35Q =====

noncomputable section

namespace X4PQ
open Matrix QAlgorithms QAlgorithms.Papers.Independent.Support50.P35
open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)
open scoped Matrix ComplexConjugate

variable {D : ℕ}


/-- the traceless part. -/
def S (c : TracelessIndex D → ℝ) : Matrix (Fin D) (Fin D) ℂ := ∑ j, (c j : ℂ) • normOneGellmannGenerator j

lemma S_herm (c : TracelessIndex D → ℝ) : (S c).IsHermitian := by
  unfold S
  rw [IsHermitian, conjTranspose_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [conjTranspose_smul, (X4GM.herm_gen k).eq]
  simp

lemma tr_S (c : TracelessIndex D → ℝ) : (S c).trace = 0 := by
  simp [S, Matrix.trace_sum, Matrix.trace_smul, X4GM.tr_gen]

lemma tr_S_gen (c : TracelessIndex D → ℝ) (l : TracelessIndex D) :
    (S c * normOneGellmannGenerator l).trace = c l := by
  simp only [S, Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul, X4GM.orth_gen,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma tr_SS (c : TracelessIndex D → ℝ) : (S c * S c).trace = ((dotProduct c c : ℝ) : ℂ) := by
  conv_lhs => rw [S]
  rw [Finset.sum_mul, Matrix.trace_sum]
  simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, dotProduct]
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.trace_mul_comm]; exact congrArg _ (tr_S_gen c x)

lemma tr_SSl (c : TracelessIndex D → ℝ) (l : TracelessIndex D) :
    (S c * S c * normOneGellmannGenerator l).trace.re = starProduct c c l := by
  simp only [S, Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sum,
    Matrix.trace_smul, smul_eq_mul, Complex.re_sum, starProduct, symmetricConstant]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.re_ofReal_mul, Complex.re_ofReal_mul]; ring

/-- the defect matrix. -/
def M (c : TracelessIndex D → ℝ) : Matrix (Fin D) (Fin D) ℂ :=
  S c * S c - ((D : ℂ) - 1) • (1 : Matrix (Fin D) (Fin D) ℂ) - ((D : ℂ) - 2) • S c

lemma M_herm (c : TracelessIndex D → ℝ) : (M c).IsHermitian := by
  have h := S_herm c
  unfold M
  refine IsHermitian.sub (IsHermitian.sub ?_ ?_) ?_
  · simp only [IsHermitian, conjTranspose_mul, h.eq]
  · rw [IsHermitian, conjTranspose_smul, conjTranspose_one]
    congr 1; simp [Complex.ext_iff]
  · rw [IsHermitian, conjTranspose_smul, h.eq]
    congr 1; simp [Complex.ext_iff]

lemma tr_M (c : TracelessIndex D → ℝ) :
    (M c).trace.re = dotProduct c c - ((D : ℝ) - 1) * D := by
  simp [M, Matrix.trace_sub, Matrix.trace_smul, tr_SS, tr_S]

lemma tr_Ml (c : TracelessIndex D → ℝ) (l : TracelessIndex D) :
    (M c * normOneGellmannGenerator l).trace.re = starProduct c c l - ((D : ℝ) - 2) * c l := by
  simp only [M, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_sub, Matrix.trace_smul,
    X4GM.tr_gen, tr_S_gen, smul_eq_mul, Complex.sub_re, tr_SSl, mul_zero, sub_zero]
  simp [Complex.mul_re]

lemma M_zero_iff (hD : 0 < D) (c : TracelessIndex D → ℝ) : M c = 0 ↔ c ∈ pureQuadraticSet D := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := tr_M c; rw [h] at this; simp at this; linarith
    · funext l
      have := tr_Ml c l; rw [h] at this; simp at this
      simp only [Pi.smul_apply, smul_eq_mul]; linarith
  · rintro ⟨h1, h2⟩
    rw [X4OC.herm_expand (X4GM.gm_basis hD) (M_herm c), Fintype.sum_option]
    have e0 : (M c * gellmann D none).trace = 0 := by
      have h := X4OB.tr_real (M_herm c) (X4GM.gm_herm (D := D) none)
      rw [← h]
      simp only [gellmann, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]
      have h0 : (M c).trace.re = 0 := by rw [tr_M, h1]; ring
      have hM1 := X4OB.tr_real (M_herm c) isHermitian_one
      rw [Matrix.mul_one] at hM1
      rw [← hM1, h0]; simp
    have el : ∀ l, (M c * gellmann D (some l)).trace = 0 := by
      intro l
      have h := X4OB.tr_real (M_herm c) (X4GM.gm_herm (D := D) (some l))
      rw [← h]
      simp only [gellmann]
      rw [tr_Ml, show starProduct c c l = ((D : ℝ) - 2) * c l from congrFun h2 l]
      simp
    simp [e0, el]

lemma tr_rho (hD : 0 < D) (c : TracelessIndex D → ℝ) : (scaledGellmannState c).trace = 1 := by
  have : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  simp only [scaledGellmannState, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_one, Fintype.card_fin]
  rw [show (∑ j, (c j : ℂ) • normOneGellmannGenerator j) = S c from rfl, tr_S]
  simp [this]

lemma rho_herm (c : TracelessIndex D → ℝ) : (scaledGellmannState c).IsHermitian := by
  rw [scaledGellmannState, show (∑ j, (c j : ℂ) • normOneGellmannGenerator j) = S c from rfl]
  rw [IsHermitian, conjTranspose_smul, conjTranspose_add, conjTranspose_one, (S_herm c).eq]
  congr 1; simp [Complex.ext_iff]

lemma sq_iff (hD : 0 < D) (c : TracelessIndex D → ℝ) :
    scaledGellmannState c * scaledGellmannState c = scaledGellmannState c ↔ M c = 0 := by
  have hD' : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  set u : ℂ := (D : ℂ)⁻¹
  have hu : u * u * D = u := by simp only [u]; field_simp
  have hA : (1 + S c) * (1 + S c) - (D : ℂ) • (1 + S c) = M c := by
    rw [M, add_mul, mul_add, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]
    module
  have hr : scaledGellmannState c = u • (1 + S c) := rfl
  rw [hr, smul_mul_smul_comm, ← hA, sub_eq_zero]
  have hne : u * u ≠ 0 := by simp [u, hD']
  constructor
  · intro h
    apply smul_right_injective _ hne
    simp only
    rw [h, smul_smul, hu]
  · intro h
    rw [h, smul_smul, hu]

theorem main (hD : 0 < D) (c : TracelessIndex D → ℝ) :
    IsPure (scaledGellmannState c) ↔ c ∈ pureQuadraticSet D := by
  rw [← M_zero_iff hD, ← sq_iff hD]
  constructor
  · rintro ⟨v, hv, he⟩
    rw [he]; exact (X4OC.pure_proj v hv).1
  · intro h
    exact X4OC.proj_pure (rho_herm c) h (tr_rho hD c)

end X4PQ

-- ===== P35H =====

noncomputable section

namespace X4PH
open Matrix QAlgorithms QAlgorithms.Papers.Independent.Support50.P35
open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)
open scoped Matrix ComplexConjugate ComplexOrder

variable {D : ℕ}

/-- scaled coordinates of a matrix. -/
def coordOf (X : Matrix (Fin D) (Fin D) ℂ) : TracelessIndex D → ℝ :=
  fun j => (D : ℝ) * (X * normOneGellmannGenerator j).trace.re

lemma coords (hD : 0 < D) {X : Matrix (Fin D) (Fin D) ℂ} (hX : X.IsHermitian) (h1 : X.trace = 1) :
    X = scaledGellmannState (coordOf X) := by
  have hD' : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  conv_lhs => rw [X4OC.herm_expand (X4GM.gm_basis hD) hX, Fintype.sum_option]
  simp only [gellmann, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, h1, smul_eq_mul, mul_one,
    smul_smul, X4GM.sD hD, scaledGellmannState, coordOf, smul_add, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [← X4OB.tr_real hX (X4GM.herm_gen j)]
  push_cast
  field_simp
  simp

lemma tr_rho_gen (c : TracelessIndex D → ℝ) (l : TracelessIndex D) :
    (scaledGellmannState c * normOneGellmannGenerator l).trace = (D : ℂ)⁻¹ * c l := by
  rw [scaledGellmannState, show (∑ j, (c j : ℂ) • normOneGellmannGenerator j) = X4PQ.S c from rfl,
    Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul, Matrix.trace_smul, Matrix.trace_add, X4GM.tr_gen,
    X4PQ.tr_S_gen, zero_add, smul_eq_mul]

lemma coord_rho (hD : 0 < D) (c : TracelessIndex D → ℝ) : coordOf (scaledGellmannState c) = c := by
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  funext j
  simp only [coordOf, tr_rho_gen]
  rw [show ((D : ℂ)⁻¹ * (c j : ℂ)) = (((D : ℝ)⁻¹ * c j : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_re]
  field_simp

lemma affine (c d : TracelessIndex D → ℝ) (a b : ℝ) (hab : a + b = 1) :
    scaledGellmannState (a • c + b • d) =
      (a : ℂ) • scaledGellmannState c + (b : ℂ) • scaledGellmannState d := by
  have hS : (∑ j, ((a • c + b • d) j : ℂ) • normOneGellmannGenerator j) =
      (a : ℂ) • X4PQ.S c + (b : ℂ) • X4PQ.S d :=
    X4OC.recon_lin normOneGellmannGenerator a b c d
  have hab' : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
  rw [scaledGellmannState, hS, scaledGellmannState, scaledGellmannState,
    show (∑ j, (c j : ℂ) • normOneGellmannGenerator j) = X4PQ.S c from rfl,
    show (∑ j, (d j : ℂ) • normOneGellmannGenerator j) = X4PQ.S d from rfl]
  have e : (1 : Matrix (Fin D) (Fin D) ℂ) = ((a : ℂ) + (b : ℂ)) • (1 : Matrix (Fin D) (Fin D) ℂ) := by
    rw [hab', one_smul]
  conv_lhs => rw [e]
  module

theorem hull (hD : 0 < D) :
    {c : TracelessIndex D → ℝ | IsDensityMatrix (scaledGellmannState c)} =
      convexHull ℝ (pureQuadraticSet D) := by
  apply Set.Subset.antisymm
  · intro c hc
    obtain ⟨hpsd, htr⟩ := hc
    set ρ := scaledGellmannState c
    have hρ := hpsd.1
    set lam := hρ.eigenvalues
    set v := hρ.eigenvectorBasis
    have hv : ∀ k, ‖v k‖ = 1 := fun k => v.orthonormal.1 k
    have hcg : c = ∑ k, lam k • coordOf (pureDensity (v k)) := by
      conv_lhs => rw [← coord_rho hD c]
      funext g
      change (D : ℝ) * (ρ * normOneGellmannGenerator g).trace.re = _
      conv_lhs => rw [X4OC.spec_sum hρ]
      rw [Finset.sum_mul, Matrix.trace_sum, Complex.re_sum, Finset.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
      simp only [Pi.smul_apply, coordOf, smul_eq_mul]
      ring
    have hsum : ∑ k, lam k = 1 := by
      have := hρ.trace_eq_sum_eigenvalues
      rw [htr] at this
      have h3 : ((∑ k, lam k : ℝ) : ℂ) = 1 := by push_cast; exact this.symm
      exact_mod_cast h3
    rw [hcg]
    refine (convex_convexHull ℝ _).sum_mem (fun k _ => hpsd.eigenvalues_nonneg k) hsum
      (fun k _ => subset_convexHull ℝ _ ?_)
    obtain ⟨-, p2, p3⟩ := X4OC.pure_proj (v k) (hv k)
    rw [← X4PQ.main hD, ← coords hD p3 p2]
    exact ⟨v k, hv k, rfl⟩
  · refine convexHull_min ?_ ?_
    · intro c hc
      obtain ⟨w, hw, he⟩ := (X4PQ.main hD c).2 hc
      obtain ⟨-, p2, p3⟩ := X4OC.pure_proj w hw
      show IsDensityMatrix _
      rw [he]
      refine ⟨?_, p2⟩
      have := posSemidef_conjTranspose_mul_self (pureDensity w)
      rwa [p3.eq, (X4OC.pure_proj w hw).1] at this
    · intro c hc d hd a b ha hb hab
      obtain ⟨hc1, hc2⟩ := hc
      obtain ⟨hd1, hd2⟩ := hd
      show IsDensityMatrix _
      rw [affine c d a b hab]
      refine ⟨(hc1.smul (by exact_mod_cast ha)).add (hd1.smul (by exact_mod_cast hb)), ?_⟩
      rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hc2, hd2]
      simp only [smul_eq_mul, mul_one]
      exact_mod_cast hab

end X4PH

-- ===== P35HSol =====

noncomputable section

open scoped Matrix ComplexConjugate Topology Manifold

namespace QAlgorithms.Papers.Independent.Support50.P35

/-- PDF p.14: the density-coordinate set is the finite convex hull of the
pure quadratic variety; pure boundary states are included among densities. -/
theorem _root_.solution (D : ℕ) (hD : 0 < D) :
    {c : TracelessIndex D → ℝ | IsDensityMatrix (scaledGellmannState c)} =
      convexHull ℝ (pureQuadraticSet D) :=
  X4PH.hull hD

end QAlgorithms.Papers.Independent.Support50.P35

end

#print axioms solution
