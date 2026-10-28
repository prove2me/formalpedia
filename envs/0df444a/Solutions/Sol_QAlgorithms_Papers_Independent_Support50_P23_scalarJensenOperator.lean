-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P23.scalarJensenOperator
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T08:56:01.313119+00:00
-- url     : https://prove2.me/submissions/c3ef0db1-43e0-46c9-901e-0fb2a845cfdb

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P23
open Matrix
open scoped ComplexOrder

theorem x5js_eig {I : Type*} [Fintype I] [DecidableEq I] {X : Matrix I I ℂ} (hX : X.IsHermitian)
    (g : ℝ → ℝ) (j : I) :
    cfc g X *ᵥ (hX.eigenvectorBasis j).ofLp = ((g (hX.eigenvalues j) : ℝ) : ℂ) • (hX.eigenvectorBasis j).ofLp := by
  rw [hX.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, ← mulVec_mulVec, ← mulVec_mulVec,
    hX.star_eigenvectorUnitary_mulVec, diagonal_mulVec_single, ← hX.eigenvectorUnitary_mulVec,
    ← mulVec_smul]
  congr 1; ext i; simp [Pi.single_apply]

theorem x5js_quad {I : Type*} [Fintype I] [DecidableEq I] {X : Matrix I I ℂ} (hX : X.IsHermitian)
    (g : ℝ → ℝ) (phi : EuclideanSpace ℂ I) :
    (inner ℂ phi (QAlgorithms.act (cfc g X) phi)).re =
      ∑ j, ‖inner ℂ (hX.eigenvectorBasis j) phi‖ ^ 2 * g (hX.eigenvalues j) := by
  have hphi : phi = ∑ j, inner ℂ (hX.eigenvectorBasis j) phi • hX.eigenvectorBasis j := (hX.eigenvectorBasis.sum_repr' phi).symm
  have hact : QAlgorithms.act (cfc g X) phi = ∑ j, (inner ℂ (hX.eigenvectorBasis j) phi * ((g (hX.eigenvalues j) : ℝ) : ℂ)) • hX.eigenvectorBasis j := by
    unfold QAlgorithms.act
    conv_lhs => rw [hphi]
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, mulVec_sum, mulVec_smul, x5js_eig]
    rw [← WithLp.toLp_sum]
    congr 1; refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul]; rfl
  rw [hact, inner_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_right, ← inner_conj_symm (hX.eigenvectorBasis j) phi, mul_right_comm, Complex.conj_mul', RCLike.norm_conj, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem x5js_bounds {I : Type*} [Fintype I] [DecidableEq I] {X : Matrix I I ℂ} (hX : X.IsHermitian)
    (a b : ℝ) (hLower : (X - (a : ℂ) • (1 : Matrix I I ℂ)).PosSemidef)
    (hUpper : ((b : ℂ) • (1 : Matrix I I ℂ) - X).PosSemidef) (j : I) :
    hX.eigenvalues j ∈ Set.Icc a b := by
  set v := (hX.eigenvectorBasis j).ofLp
  have hv : star v ⬝ᵥ v = 1 := by
    have hn := (hX.eigenvectorBasis).orthonormal.1 j
    have : inner ℂ (hX.eigenvectorBasis j) (hX.eigenvectorBasis j) = (1 : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K, hn]; simp
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at this
    exact this
  have hXv := hX.mulVec_eigenvectorBasis j
  have h1 := hLower.dotProduct_mulVec_nonneg v
  have h2 := hUpper.dotProduct_mulVec_nonneg v
  rw [sub_mulVec, smul_mulVec, one_mulVec, hXv, dotProduct_sub, dotProduct_smul, dotProduct_smul, hv] at h1
  rw [sub_mulVec, smul_mulVec, one_mulVec, hXv, dotProduct_sub, dotProduct_smul, dotProduct_smul, hv] at h2
  simp only [smul_eq_mul, mul_one, RCLike.real_smul_eq_coe_mul] at h1 h2
  constructor
  · have := Complex.nonneg_iff.1 h1; simp at this; linarith
  · have := Complex.nonneg_iff.1 h2; simp at this; linarith

theorem x5js_main {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ) (hf : ConvexOn ℝ (Set.Icc a b) f)
    (X : Matrix I I ℂ) (hX : X.IsHermitian)
    (hLower : (X - (a : ℂ) • (1 : Matrix I I ℂ)).PosSemidef)
    (hUpper : ((b : ℂ) • (1 : Matrix I I ℂ) - X).PosSemidef)
    (phi : EuclideanSpace ℂ I) (hphi : ‖phi‖ = 1) :
    f ((inner ℂ phi (QAlgorithms.act X phi)).re) ≤ (inner ℂ phi (QAlgorithms.act (cfc f X) phi)).re := by
  have hXid : cfc id X = X := cfc_id' ℝ X (ha := hX.isSelfAdjoint)
  conv_lhs => rw [← hXid]
  rw [x5js_quad hX, x5js_quad hX]
  have hw : ∑ j, ‖inner ℂ (hX.eigenvectorBasis j) phi‖ ^ 2 = 1 := by
    rw [hX.eigenvectorBasis.sum_sq_norm_inner_right, hphi, one_pow]
  have := hf.map_sum_le (t := Finset.univ) (w := fun j => ‖inner ℂ (hX.eigenvectorBasis j) phi‖ ^ 2)
    (p := hX.eigenvalues) (fun j _ => by positivity) hw (fun j _ => x5js_bounds hX a b hLower hUpper j)
  simpa [smul_eq_mul] using this

theorem solution {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ) (hf : ConvexOn ℝ (Set.Icc a b) f)
    (X : Matrix I I ℂ) (hX : X.IsHermitian)
    (hLower : (X - (a : ℂ) • (1 : Matrix I I ℂ)).PosSemidef)
    (hUpper : ((b : ℂ) • (1 : Matrix I I ℂ) - X).PosSemidef)
    (phi : EuclideanSpace ℂ I) (hphi : ‖phi‖ = 1) :
    f ((inner ℂ phi (QAlgorithms.act X phi)).re) ≤ (inner ℂ phi (QAlgorithms.act (cfc f X) phi)).re :=
  x5js_main a b hab f hf X hX hLower hUpper phi hphi
