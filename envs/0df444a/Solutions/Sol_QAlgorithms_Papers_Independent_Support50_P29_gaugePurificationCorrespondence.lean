-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P29.gaugePurificationCorrespondence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:46:30.216684+00:00
-- url     : https://prove2.me/submissions/d0d81b6c-e896-43b6-b74b-0b97fe36c15d

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P29
noncomputable section

open Filter

open scoped BigOperators ENNReal Topology ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace A3S54P29
open QAlgorithms.Papers.Independent.Support50.P29
open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma complexify)
open Matrix Polynomial

lemma herm_exists {F : Type} [Fintype F] [DecidableEq F] (M : Matrix F F ℂ) (hM : M.IsHermitian) :
    ∃ P d, SimilarityData M P d := by
  refine ⟨(hM.eigenvectorUnitary : Matrix F F ℂ), (RCLike.ofReal ∘ hM.eigenvalues), ?_, ?_⟩
  · exact ⟨⟨_, star (hM.eigenvectorUnitary : Matrix F F ℂ),
      Unitary.mul_star_self_of_mem hM.eigenvectorUnitary.2,
      Unitary.star_mul_self_of_mem hM.eigenvectorUnitary.2⟩, rfl⟩
  · have hinv : (hM.eigenvectorUnitary : Matrix F F ℂ)⁻¹ = star (hM.eigenvectorUnitary : Matrix F F ℂ) :=
      Matrix.inv_eq_right_inv (Unitary.mul_star_self_of_mem hM.eigenvectorUnitary.2)
    rw [hinv]
    conv_lhs => rw [hM.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply]

lemma eig_real {F : Type} [Fintype F] (M : Matrix F F ℂ) (hM : M.IsHermitian)
    (v : F → ℂ) (hv : v ≠ 0) (d : ℂ) (h : M *ᵥ v = d • v) : ((d.re : ℝ) : ℂ) = d := by
  have h1 : star v ⬝ᵥ (M *ᵥ v) = d * (star v ⬝ᵥ v) := by rw [h, dotProduct_smul, smul_eq_mul]
  have h2 : star v ⬝ᵥ (M *ᵥ v) = (starRingEnd ℂ d) * (star v ⬝ᵥ v) := by
    rw [dotProduct_mulVec]
    have : star v ᵥ* M = star (M *ᵥ v) := by
      rw [star_mulVec, hM.eq]
    rw [this, h, star_smul, smul_dotProduct]
    rfl
  have hn : star v ⬝ᵥ v ≠ 0 := fun h0 => hv (dotProduct_star_self_eq_zero.mp h0)
  have : starRingEnd ℂ d = d := by
    have := h2.symm.trans h1
    exact mul_right_cancel₀ hn this
  exact Complex.conj_eq_iff_re.mp this


lemma conj_pow {F : Type} [Fintype F] [DecidableEq F] (P D : Matrix F F ℂ) (hP : IsUnit P) (n : ℕ) :
    (P * D * P⁻¹) ^ n = P * D ^ n * P⁻¹ := by
  have hPi : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).mp hP)
  have hPi' : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).mp hP)
  induction n with
  | zero => simp [hPi']
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    calc P * D ^ n * P⁻¹ * (P * D * P⁻¹) = P * D ^ n * (P⁻¹ * P) * D * P⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hPi, Matrix.mul_one]; simp only [Matrix.mul_assoc]

lemma aeval_conj {F : Type} [Fintype F] [DecidableEq F] (P D : Matrix F F ℂ) (hP : IsUnit P)
    (q : ℝ[X]) : aeval (P * D * P⁻¹) q = P * aeval D q * P⁻¹ := by
  induction q using Polynomial.induction_on' with
  | add p r hp hr => simp [hp, hr, Matrix.mul_add, Matrix.add_mul]
  | monomial n a =>
    simp only [aeval_monomial, conj_pow P D hP n]
    simp only [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm]

lemma aeval_diag {F : Type} [Fintype F] [DecidableEq F] (d : F → ℂ) (q : ℝ[X]) :
    aeval (Matrix.diagonal d) q = Matrix.diagonal (fun j => aeval (d j) q) := by
  have := Polynomial.aeval_algHom_apply (Matrix.diagonalAlgHom ℝ (n := F) (α := ℂ)) d q
  simp only [Matrix.diagonalAlgHom_apply] at this
  rw [this]
  congr 1
  ext j
  simp [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, Finset.sum_apply]

lemma simFun_eq {F : Type} [Fintype F] [DecidableEq F] (M : Matrix F F ℂ) (f : ℂ → ℂ)
    (h : ∃ P d, SimilarityData M P d) (q : ℝ[X])
    (hq : ∀ j, aeval (h.choose_spec.choose j) q = f (h.choose_spec.choose j)) :
    similarityFunction M f = aeval M q := by
  unfold similarityFunction
  rw [dif_pos h]
  have hs := h.choose_spec.choose_spec
  dsimp only
  conv_rhs => rw [hs.2]
  rw [aeval_conj _ _ hs.1, aeval_diag]
  simp_rw [hq]


@[simp] lemma realify_ll {F : Type} (X : Matrix F F ℂ) (i j : F) :
    realify X (Sum.inl i) (Sum.inl j) = (X i j).re := rfl
@[simp] lemma realify_lr {F : Type} (X : Matrix F F ℂ) (i j : F) :
    realify X (Sum.inl i) (Sum.inr j) = -(X i j).im := rfl
@[simp] lemma realify_rl {F : Type} (X : Matrix F F ℂ) (i j : F) :
    realify X (Sum.inr i) (Sum.inl j) = (X i j).im := rfl
@[simp] lemma realify_rr {F : Type} (X : Matrix F F ℂ) (i j : F) :
    realify X (Sum.inr i) (Sum.inr j) = (X i j).re := rfl

def realifyHom (F : Type) [Fintype F] [DecidableEq F] :
    Matrix F F ℂ →ₐ[ℝ] Matrix (F ⊕ F) (F ⊕ F) ℝ where
  toFun := realify
  map_one' := by
    ext (i | i) (j | j) <;> by_cases h : i = j <;> simp [Matrix.one_apply, h]
  map_mul' X Y := by
    ext (i | i) (j | j) <;>
      simp [Matrix.mul_apply, Fintype.sum_sum_type, Complex.mul_re, Complex.mul_im,
        Finset.sum_add_distrib, sub_eq_add_neg] <;> ring
  map_zero' := by ext (i | i) (j | j) <;> simp
  map_add' X Y := by ext (i | i) (j | j) <;> simp <;> ring
  commutes' r := by
    ext (i | i) (j | j) <;> by_cases h : i = j <;>
      simp [Matrix.algebraMap_matrix_apply, h]

lemma realifyHom_apply {F : Type} [Fintype F] [DecidableEq F] (X : Matrix F F ℂ) :
    realifyHom F X = realify X := rfl

lemma complexify_aeval {F : Type} [Fintype F] [DecidableEq F] (R : Matrix F F ℝ) (q : ℝ[X]) :
    complexify (aeval R q) = aeval (complexify R) q := by
  have := Polynomial.aeval_algHom_apply ((Algebra.ofId ℝ ℂ).mapMatrix (m := F)) R q
  exact this.symm

lemma realify_conjTranspose {F : Type} (X : Matrix F F ℂ) :
    realify Xᴴ = (realify X).transpose := by
  ext (i | i) (j | j) <;> simp [Matrix.conjTranspose_apply]

lemma realify_blocks {s : ℕ} (X Y Z W : Matrix (Fin s) (Fin s) ℂ) :
    (realify (Matrix.fromBlocks X Y Z W)).submatrix shuffle shuffle =
      Matrix.fromBlocks (realify X) (realify Y) (realify Z) (realify W) := by
  ext ((i | i) | (i | i)) ((j | j) | (j | j)) <;> simp [shuffle]

lemma sigma_eq (s : ℕ) : sigma s = realify ((-Complex.I) • (1 : Matrix (Fin s) (Fin s) ℂ)) := by
  ext (i | i) (j | j) <;> by_cases h : i = j <;>
    simp [sigma, Matrix.one_apply, h]


lemma sim_real {F : Type} [Fintype F] [DecidableEq F] (M P : Matrix F F ℂ) (d : F → ℂ)
    (hM : M.IsHermitian) (hs : SimilarityData M P d) (j : F) : (((d j).re : ℝ) : ℂ) = d j := by
  have hdet := (Matrix.isUnit_iff_isUnit_det P).mp hs.1
  have hPi : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  apply eig_real M hM (P *ᵥ Pi.single j 1)
  · intro h0
    have := congrArg (fun v => P⁻¹ *ᵥ v) h0
    simp only [Matrix.mulVec_mulVec, hPi, Matrix.one_mulVec, Matrix.mulVec_zero] at this
    have := congrFun this j
    simp at this
  · conv_lhs => rw [hs.2]
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hPi, Matrix.mul_one,
      ← Matrix.mulVec_mulVec, Matrix.diagonal_mulVec_single, mul_one]
    rw [show Pi.single j (d j) = d j • (Pi.single j (1 : ℂ) : F → ℂ) by
      ext k; by_cases hk : k = j
      · subst hk; simp
      · simp [hk], Matrix.mulVec_smul]

lemma key_sqrt {F : Type} [Fintype F] [DecidableEq F] (H : Matrix F F ℂ) (hH : H.IsHermitian) :
    realSpectralSqrt (realify H) = realify (similarityFunction H (fun z => (Real.sqrt z.re : ℂ))) := by
  have hR : (complexify (realify H)).IsHermitian := by
    ext i j
    have := congrArg (fun X => X j i) (realify_conjTranspose H)
    simp only [hH.eq, Matrix.transpose_apply] at this
    simp [Matrix.conjTranspose_apply, complexify, this]
  obtain h1 := herm_exists H hH
  obtain h2 := herm_exists _ hR
  set d1 := h1.choose_spec.choose with hd1
  set d2 := h2.choose_spec.choose with hd2
  have r1 := sim_real _ _ _ hH h1.choose_spec.choose_spec
  have r2 := sim_real _ _ _ hR h2.choose_spec.choose_spec
  set S : Finset ℝ := Finset.univ.image (fun j => (d1 j).re) ∪ Finset.univ.image (fun j => (d2 j).re)
  set q := Lagrange.interpolate S id (fun x => Real.sqrt x)
  have hq : ∀ x ∈ S, q.eval x = Real.sqrt x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) (fun x => Real.sqrt x) (Set.injOn_id _) hx
  have hz : ∀ z : ℂ, ((z.re : ℝ) : ℂ) = z → z.re ∈ S →
      aeval z q = (Real.sqrt z.re : ℂ) := by
    intro z hz hS
    rw [← hz, show ((z.re : ℝ) : ℂ) = algebraMap ℝ ℂ z.re from rfl,
      aeval_algebraMap_apply_eq_algebraMap_eval, hq _ hS]
    simp
  have e1 : similarityFunction H (fun z => (Real.sqrt z.re : ℂ)) = aeval H q :=
    simFun_eq _ _ h1 q (fun j => hz _ (r1 j) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))))
  have e2 : similarityFunction (complexify (realify H)) (fun z => (Real.sqrt z.re : ℂ)) =
      aeval (complexify (realify H)) q :=
    simFun_eq _ _ h2 q (fun j => hz _ (r2 j) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))))
  have e3 : realify (aeval H q) = aeval (realify H) q :=
    (Polynomial.aeval_algHom_apply (realifyHom F) H q).symm
  ext i j
  unfold realSpectralSqrt
  rw [e2, ← complexify_aeval, ← e3, e1]
  simp [complexify]


lemma canon_eq (s : ℕ) (hbar : ℝ) : canonicalCommutation s hbar =
    realify ((-(hbar : ℂ) * Complex.I) • (1 : Matrix (Fin s) (Fin s) ℂ)) := by
  ext (i | i) (j | j) <;> by_cases h : i = j <;>
    simp [canonicalCommutation, sigma, Matrix.one_apply, h]

lemma cplx_id {s : ℕ} (N : Matrix (Fin s) (Fin s) ℂ) :
    -((Complex.I • (N + (1 / 2 : ℂ) • 1)) ^ 2) - ((1 / 4 : ℝ) • (1 : Matrix (Fin s) (Fin s) ℂ)) =
      N ^ 2 + N := by
  rw [_root_.smul_pow, Complex.I_sq, sq, sq]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, mul_one, one_mul, smul_add, smul_smul]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  module

theorem main (s : ℕ) (hs : 0 < s)
    (hbar : ℝ) (hhbar : 0 < hbar) (N : Matrix (Fin s) (Fin s) ℂ)
    (hN : N.PosSemidef) :
    (reflectedDelta s hbar)⁻¹ * purificationCovariance hbar (gaugeCovariance hbar N) =
      (realify (gaugePurificationMatrix N)).submatrix shuffle shuffle := by
  have hb : (hbar : ℂ) ≠ 0 := by exact_mod_cast hhbar.ne'
  set ρ := realifyHom (Fin s)
  set Y : Matrix (Fin s) (Fin s) ℂ := N + (1 / 2 : ℂ) • 1
  set Dc : Matrix (Fin s) (Fin s) ℂ := (-(hbar : ℂ) * Complex.I) • 1
  set Ei : Matrix (Fin s) (Fin s) ℂ := (Complex.I / hbar) • 1
  have hED : Ei * Dc = 1 := by
    simp only [Ei, Dc, smul_mul_assoc, one_mul, smul_smul]
    rw [show Complex.I / hbar * (-(hbar : ℂ) * Complex.I) = 1 by
      field_simp; rw [Complex.I_sq]; ring]
    simp
  have hΔ : canonicalCommutation s hbar = ρ Dc := canon_eq s hbar
  have hΔi : (canonicalCommutation s hbar)⁻¹ = ρ Ei := by
    apply Matrix.inv_eq_left_inv
    rw [hΔ, ← map_mul, hED, map_one]
  have hDi : (reflectedDelta s hbar)⁻¹ = Matrix.fromBlocks (ρ Ei) 0 0 (-ρ Ei) := by
    apply Matrix.inv_eq_left_inv
    have h1 : ρ Ei * ρ Dc = 1 := by rw [← map_mul, hED, map_one]
    rw [reflectedDelta, Matrix.fromBlocks_multiply, hΔ]
    simp [h1]
  have hα : gaugeCovariance hbar N = ρ ((hbar : ℂ) • Y) := by
    rw [gaugeCovariance, show ((hbar : ℂ) • Y) = hbar • Y by ext i j; simp, map_smul]; rfl
  have hA : (canonicalCommutation s hbar)⁻¹ * gaugeCovariance hbar N = ρ (Complex.I • Y) := by
    rw [hΔi, hα, ← map_mul]
    congr 1
    simp only [Ei, smul_mul_assoc, one_mul, smul_smul]
    congr 1
    field_simp
  have hHerm : (N ^ 2 + N).IsHermitian := by
    have h := hN.isHermitian
    exact (h.pow 2).add h
  have hsq : realSpectralSqrt (-(((canonicalCommutation s hbar)⁻¹ * gaugeCovariance hbar N) ^ 2) -
      (1 / 4 : ℝ) • 1) = ρ (similarityFunction (N ^ 2 + N) (fun z => (Real.sqrt z.re : ℂ))) := by
    rw [hA, ← map_pow, show ((1 / 4 : ℝ) • (1 : Matrix (Phase s) (Phase s) ℝ)) =
      ρ ((1 / 4 : ℝ) • 1) by rw [map_smul, map_one], ← map_neg, ← map_sub, cplx_id]
    exact key_sqrt _ hHerm
  set C := similarityFunction (N ^ 2 + N) (fun z => (Real.sqrt z.re : ℂ))
  have hA' : ρ Ei * gaugeCovariance hbar N = ρ (Complex.I • Y) := by rw [← hΔi]; exact hA
  have hB : ρ Ei * (ρ Dc * ρ C) = ρ C := by
    rw [← Matrix.mul_assoc, ← map_mul, hED, map_one, Matrix.one_mul]
  rw [hDi, purificationCovariance]
  rw [hsq, hΔ, Matrix.fromBlocks_multiply, gaugePurificationMatrix]
  rw [realify_blocks]
  simp only [Matrix.zero_mul, add_zero, zero_add, neg_mul_neg, neg_mul, hA', hB]
  congr 1
  · simp only [Matrix.mul_neg, neg_neg, hB]; rfl
  · rw [← realifyHom_apply, neg_smul, map_neg]

end A3S54P29

open QAlgorithms.Papers.Independent.Support50.P29 in
theorem solution (s : ℕ) (hs : 0 < s)
    (hbar : ℝ) (hhbar : 0 < hbar) (N : Matrix (Fin s) (Fin s) ℂ)
    (hN : N.PosSemidef) :
    (reflectedDelta s hbar)⁻¹ * purificationCovariance hbar (gaugeCovariance hbar N) =
      (realify (gaugePurificationMatrix N)).submatrix shuffle shuffle :=
  A3S54P29.main s hs hbar hhbar N hN

end
