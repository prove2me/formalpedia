-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P39.unit_kernel_form_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T12:05:57.031214+00:00
-- url     : https://prove2.me/submissions/681a128e-76b3-4e5e-a4c2-7a5ad7b2d0b8

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P39
noncomputable section

open scoped BigOperators Matrix

namespace QAlgorithms.Papers.Independent.Intake100.P39

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic canonicalJ)

open QAlgorithms.Papers.Independent.Gap50repair.P01
  (Coord GroupedRealMatrix omegaMatrix omegaR omegaC shifted generalizedSpace
    IsEigenvalue HasNilpotentHeight restrictedKernel GeneralizedQuotient)

theorem AuxH_add_l {n : ℕ} (v v' w : Coord n → ℂ) : omegaC (v + v') w = omegaC v w + omegaC v' w := by
  simp only [omegaC, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem AuxH_add_r {n : ℕ} (v w w' : Coord n → ℂ) : omegaC v (w + w') = omegaC v w + omegaC v w' := by
  simp only [omegaC, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem AuxH_smul_l {n : ℕ} (c : ℂ) (v w : Coord n → ℂ) : omegaC (c • v) w = c * omegaC v w := by
  simp only [omegaC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem AuxH_smul_r {n : ℕ} (c : ℂ) (v w : Coord n → ℂ) : omegaC v (c • w) = c * omegaC v w := by
  simp only [omegaC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem AuxH_zero_l {n : ℕ} (w : Coord n → ℂ) : omegaC 0 w = 0 := by simp [omegaC]

theorem AuxH_zero_r {n : ℕ} (v : Coord n → ℂ) : omegaC v 0 = 0 := by simp [omegaC]

theorem AuxH_eq {n : ℕ} (v w : Coord n → ℂ) :
    omegaC v w = -(v ⬝ᵥ (complexify (canonicalJ n) *ᵥ w)) := by
  have h1 : ∀ i, (complexify (canonicalJ n) *ᵥ w) (Sum.inl i) = -w (Sum.inr i) := by
    intro i; simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, canonicalJ, complexify, Matrix.one_apply, apply_ite]
  have h2 : ∀ i, (complexify (canonicalJ n) *ᵥ w) (Sum.inr i) = w (Sum.inl i) := by
    intro i; simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, canonicalJ, complexify, Matrix.one_apply, apply_ite]
  rw [dotProduct, Fintype.sum_sum_type]
  simp only [h1, h2]
  rw [omegaC, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem AuxH_inv {n : ℕ} (A : GroupedRealMatrix n) (hA : IsSymplectic A) (v w : Coord n → ℂ) :
    omegaC (complexify A *ᵥ v) (complexify A *ᵥ w) = omegaC v w := by
  have hC : (complexify A)ᵀ * complexify (canonicalJ n) * complexify A = complexify (canonicalJ n) := by
    have := congrArg (Matrix.map · Complex.ofRealHom) hA
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map] at this
    exact this
  rw [AuxH_eq, AuxH_eq]
  conv_rhs => rw [← hC]
  simp only [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem AuxH_sh {n : ℕ} (A : GroupedRealMatrix n) (z : ℂ) (v : Coord n → ℂ) :
    complexify A *ᵥ v = shifted A z v + z • v := by
  simp [shifted, Matrix.toLin'_apply]

theorem AuxH_sub_l {n : ℕ} (v v' w : Coord n → ℂ) : omegaC (v - v') w = omegaC v w - omegaC v' w := by
  simp only [omegaC, Pi.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem AuxH_sub_r {n : ℕ} (v w w' : Coord n → ℂ) : omegaC v (w - w') = omegaC v w - omegaC v w' := by
  simp only [omegaC, Pi.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem AuxH_J2 (n : ℕ) : complexify (canonicalJ n) * complexify (canonicalJ n) = -1 := by
  have hR : canonicalJ n * canonicalJ n = -1 := by
    rw [canonicalJ, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp
  have := congrArg (Matrix.map · Complex.ofRealHom) hR
  rw [Matrix.map_mul, Matrix.map_neg _ (fun a => map_neg Complex.ofRealHom a),
    Matrix.map_one _ (map_zero _) (map_one _)] at this
  exact this

theorem AuxH_nd {n : ℕ} (x : Coord n → ℂ) (h : ∀ u, omegaC x u = 0) : x = 0 := by
  funext k
  rcases k with i | i
  · have := h (Pi.single (Sum.inr i) 1)
    simpa [omegaC, Pi.single_apply] using this
  · have := h (Pi.single (Sum.inl i) 1)
    simpa [omegaC, Pi.single_apply] using this

theorem AuxH_star_sh {n : ℕ} (A : GroupedRealMatrix n) (c : ℂ) (x : Coord n → ℂ) :
    star (shifted A c x) = shifted A (star c) (star x) := by
  funext i
  simp [shifted, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, complexify, star_sum]

theorem AuxH_star_pow {n : ℕ} (A : GroupedRealMatrix n) (c : ℂ) (p : ℕ) (x : Coord n → ℂ) :
    star ((shifted A c ^ p) x) = (shifted A (star c) ^ p) (star x) := by
  induction p with
  | zero => simp
  | succ p ih => rw [pow_succ', Module.End.mul_apply, AuxH_star_sh, ih, pow_succ', Module.End.mul_apply]

theorem AuxH_star_om {n : ℕ} (x y : Coord n → ℂ) : star (omegaC x y) = omegaC (star x) (star y) := by
  simp [omegaC, star_sum]

theorem AuxH_skew {n : ℕ} (v w : Coord n → ℂ) : omegaC w v = -omegaC v w := by
  simp only [omegaC, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem _root_.solution {n : ℕ} (A : GroupedRealMatrix n) (hA : IsSymplectic A)
    (z : ℂ) (hz1 : ‖z‖ = 1) (hplus : z ≠ 1) (hminus : z ≠ -1)
    (m : ℕ) (hm : 0 < m) (v w : CVec n)
    (hv : (shifted A z ^ m) v = 0) (hw : (shifted A z ^ m) w = 0) :
    unitQ A z m v w = star (unitQ A z m w v) := by
  have hz : z ≠ 0 := by intro h; rw [h, norm_zero] at hz1; exact zero_ne_one hz1
  have hsz : star z = z⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hz1]; simp
  have hss : ∀ x : Coord n → ℂ, star (star x) = x := fun x => star_star x
  set Ac := complexify A with hAc
  set Jc := complexify (canonicalJ n) with hJc
  have hC : Acᵀ * Jc * Ac = Jc := by
    have := congrArg (Matrix.map · Complex.ofRealHom) hA
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map] at this
    exact this
  set Linv : Matrix (Coord n) (Coord n) ℂ := -(Jc * Acᵀ * Jc) with hLdef
  have hL : Linv * Ac = 1 := by
    have e : Jc * Acᵀ * Jc * Ac = Jc * (Acᵀ * Jc * Ac) := by simp only [Matrix.mul_assoc]
    rw [hLdef, neg_mul, e, hC, AuxH_J2, neg_neg]
  have hR : Ac * Linv = 1 := mul_eq_one_comm.1 hL
  set Lc : Module.End ℂ (Coord n → ℂ) := Matrix.toLin' Linv with hLc
  set Ap : Module.End ℂ (Coord n → ℂ) := Matrix.toLin' Ac with hAp
  have hLA : Lc * Ap = 1 := by rw [hLc, hAp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hL, Matrix.toLin'_one]; rfl
  have hAL : Ap * Lc = 1 := by rw [hLc, hAp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hR, Matrix.toLin'_one]; rfl
  have hN : ∀ c : ℂ, shifted A c = Ap - c • 1 := fun c => rfl
  have adj0 : ∀ x y, omegaC x (Ap y) = omegaC (Lc x) y := by
    intro x y
    rw [← AuxH_inv A hA (Lc x) y]
    show omegaC x (Ac *ᵥ y) = omegaC (Ac *ᵥ (Linv *ᵥ x)) (Ac *ᵥ y)
    rw [Matrix.mulVec_mulVec, hR, Matrix.one_mulVec]
  set S : Module.End ℂ (Coord n → ℂ) := Lc - z⁻¹ • 1 with hS
  have adj1 : ∀ x u, omegaC x (shifted A z⁻¹ u) = omegaC (S x) u := by
    intro x u
    rw [hN, hS]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [AuxH_sub_r, AuxH_sub_l, AuxH_smul_r, AuxH_smul_l, adj0]
  have adjj : ∀ k : ℕ, ∀ x u, omegaC x ((shifted A z⁻¹ ^ k) u) = omegaC ((S ^ k) x) u := by
    intro k
    induction k with
    | zero => intro x u; simp
    | succ k ih =>
      intro x u
      rw [pow_succ, Module.End.mul_apply, ih, adj1, pow_succ', Module.End.mul_apply]
  set U : Module.End ℂ (Coord n → ℂ) := (-z⁻¹) • Lc with hU
  have hSU : S = U * shifted A z := by
    rw [hS, hU, hN, smul_mul_assoc, mul_sub, hLA, mul_smul_comm, mul_one, smul_sub, smul_smul,
      neg_mul, inv_mul_cancel₀ hz]
    module
  have hUN : U * shifted A z = shifted A z * U := by
    rw [hU, hN, smul_mul_assoc, mul_sub, hLA, mul_smul_comm, mul_one, mul_smul_comm, sub_mul, hAL,
      smul_mul_assoc, one_mul]
  rcases Nat.even_or_odd m with ⟨p, hp⟩ | ⟨p, hp⟩
  · -- even
    have hm2 : m % 2 = 0 := by omega
    have hmp : m / 2 = p := by omega
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    simp only [unitQ, hm2, hmp, if_true]
    rw [show p' + 1 - 1 = p' by omega]
    set y := (shifted A z ^ (2*p'+1)) v with hy
    have hNy : shifted A z y = 0 := by
      rw [hy, ← Module.End.mul_apply, ← pow_succ']
      rw [show 2*p'+1+1 = m by omega]; exact hv
    have hAy : Ap y = z • y := by
      have := hNy; rw [hN] at this
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at this
      exact this
    have hLy : Lc y = z⁻¹ • y := by
      have h1 : y = Lc (Ap y) := by rw [← Module.End.mul_apply, hLA, Module.End.one_apply]
      rw [hAy, map_smul] at h1
      calc Lc y = (z⁻¹ * z) • Lc y := by rw [inv_mul_cancel₀ hz, one_smul]
        _ = z⁻¹ • (z • Lc y) := by rw [smul_smul]
        _ = z⁻¹ • y := by rw [← h1]
    have hUy : U y = (-(z⁻¹ * z⁻¹)) • y := by
      rw [hU, LinearMap.smul_apply, hLy, smul_smul, neg_mul]
    have hUmy : ∀ k : ℕ, (U ^ k) y = ((-(z⁻¹ * z⁻¹)) ^ k) • y := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hUy, smul_smul, pow_succ, mul_comm]
    have hSm : ∀ k x, (S ^ k) x = (U ^ k) ((shifted A z ^ k) x) := by
      intro k x
      rw [hSU, Commute.mul_pow hUN, Module.End.mul_apply]
    have q1 : omegaC ((shifted A z ^ (p'+1)) v) ((shifted A z⁻¹ ^ p') (star w)) =
        (-(z⁻¹ * z⁻¹)) ^ p' * omegaC y (star w) := by
      rw [adjj, hSm, ← Module.End.mul_apply (shifted A z ^ p'), ← pow_add,
        show p' + (p'+1) = 2*p'+1 by ring, hUmy, AuxH_smul_l]
    have q2 : omegaC ((shifted A z ^ p') v) ((shifted A z⁻¹ ^ (p'+1)) (star w)) =
        (-(z⁻¹ * z⁻¹)) ^ (p'+1) * omegaC y (star w) := by
      rw [adjj, hSm, ← Module.End.mul_apply (shifted A z ^ (p'+1)), ← pow_add,
        show p' + 1 + p' = 2*p'+1 by ring, hUmy, AuxH_smul_l]
    rw [star_mul', AuxH_star_om, AuxH_star_pow, AuxH_star_pow, hss, star_star, star_inv₀, hsz, inv_inv,
      AuxH_skew ((shifted A z ^ p') v) ((shifted A z⁻¹ ^ (p'+1)) (star w)), q2, q1, pow_succ]
    field_simp
  · -- odd
    have hm2 : m % 2 = 1 := by omega
    have hmp : m / 2 = p := by omega
    simp only [unitQ, hm2, hmp, one_ne_zero, if_false]
    rw [star_mul', AuxH_star_om, AuxH_star_pow, AuxH_star_pow, hss, star_star, AuxH_skew,
      Complex.star_def, Complex.conj_I]
    ring

end QAlgorithms.Papers.Independent.Intake100.P39
