-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P39.normalized_chain_pairing_identities
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T12:10:10.626183+00:00
-- url     : https://prove2.me/submissions/b82abb60-9582-43b3-a9a3-fb1af1a217f8

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

theorem AuxN_add_l {n : ℕ} (v v' w : Coord n → ℂ) : omegaC (v + v') w = omegaC v w + omegaC v' w := by
  simp only [omegaC, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem AuxN_add_r {n : ℕ} (v w w' : Coord n → ℂ) : omegaC v (w + w') = omegaC v w + omegaC v w' := by
  simp only [omegaC, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem AuxN_smul_l {n : ℕ} (c : ℂ) (v w : Coord n → ℂ) : omegaC (c • v) w = c * omegaC v w := by
  simp only [omegaC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem AuxN_smul_r {n : ℕ} (c : ℂ) (v w : Coord n → ℂ) : omegaC v (c • w) = c * omegaC v w := by
  simp only [omegaC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem AuxN_zero_l {n : ℕ} (w : Coord n → ℂ) : omegaC 0 w = 0 := by simp [omegaC]

theorem AuxN_zero_r {n : ℕ} (v : Coord n → ℂ) : omegaC v 0 = 0 := by simp [omegaC]

theorem AuxN_eq {n : ℕ} (v w : Coord n → ℂ) :
    omegaC v w = -(v ⬝ᵥ (complexify (canonicalJ n) *ᵥ w)) := by
  have h1 : ∀ i, (complexify (canonicalJ n) *ᵥ w) (Sum.inl i) = -w (Sum.inr i) := by
    intro i; simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, canonicalJ, complexify, Matrix.one_apply, apply_ite]
  have h2 : ∀ i, (complexify (canonicalJ n) *ᵥ w) (Sum.inr i) = w (Sum.inl i) := by
    intro i; simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, canonicalJ, complexify, Matrix.one_apply, apply_ite]
  rw [dotProduct, Fintype.sum_sum_type]
  simp only [h1, h2]
  rw [omegaC, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem AuxN_inv {n : ℕ} (A : GroupedRealMatrix n) (hA : IsSymplectic A) (v w : Coord n → ℂ) :
    omegaC (complexify A *ᵥ v) (complexify A *ᵥ w) = omegaC v w := by
  have hC : (complexify A)ᵀ * complexify (canonicalJ n) * complexify A = complexify (canonicalJ n) := by
    have := congrArg (Matrix.map · Complex.ofRealHom) hA
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map] at this
    exact this
  rw [AuxN_eq, AuxN_eq]
  conv_rhs => rw [← hC]
  simp only [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem AuxN_sh {n : ℕ} (A : GroupedRealMatrix n) (z : ℂ) (v : Coord n → ℂ) :
    complexify A *ᵥ v = shifted A z v + z • v := by
  simp [shifted, Matrix.toLin'_apply]

theorem AuxN_sub_l {n : ℕ} (v v' w : Coord n → ℂ) : omegaC (v - v') w = omegaC v w - omegaC v' w := by
  simp only [omegaC, Pi.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem AuxN_sub_r {n : ℕ} (v w w' : Coord n → ℂ) : omegaC v (w - w') = omegaC v w - omegaC v w' := by
  simp only [omegaC, Pi.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem AuxN_J2 (n : ℕ) : complexify (canonicalJ n) * complexify (canonicalJ n) = -1 := by
  have hR : canonicalJ n * canonicalJ n = -1 := by
    rw [canonicalJ, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp
  have := congrArg (Matrix.map · Complex.ofRealHom) hR
  rw [Matrix.map_mul, Matrix.map_neg _ (fun a => map_neg Complex.ofRealHom a),
    Matrix.map_one _ (map_zero _) (map_one _)] at this
  exact this

theorem AuxN_nd {n : ℕ} (x : Coord n → ℂ) (h : ∀ u, omegaC x u = 0) : x = 0 := by
  funext k
  rcases k with i | i
  · have := h (Pi.single (Sum.inr i) 1)
    simpa [omegaC, Pi.single_apply] using this
  · have := h (Pi.single (Sum.inl i) 1)
    simpa [omegaC, Pi.single_apply] using this

theorem AuxN_star_sh {n : ℕ} (A : GroupedRealMatrix n) (c : ℂ) (x : Coord n → ℂ) :
    star (shifted A c x) = shifted A (star c) (star x) := by
  funext i
  simp [shifted, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, complexify, star_sum]

theorem AuxN_star_pow {n : ℕ} (A : GroupedRealMatrix n) (c : ℂ) (p : ℕ) (x : Coord n → ℂ) :
    star ((shifted A c ^ p) x) = (shifted A (star c) ^ p) (star x) := by
  induction p with
  | zero => simp
  | succ p ih => rw [pow_succ', Module.End.mul_apply, AuxN_star_sh, ih, pow_succ', Module.End.mul_apply]

theorem AuxN_star_om {n : ℕ} (x y : Coord n → ℂ) : star (omegaC x y) = omegaC (star x) (star y) := by
  simp [omegaC, star_sum]

theorem AuxN_skew {n : ℕ} (v w : Coord n → ℂ) : omegaC w v = -omegaC v w := by
  simp only [omegaC, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem AuxN_P1 {n : ℕ} (A : GroupedRealMatrix n)
    (hA : IsSymplectic A) (z : ℂ) (hz : z ≠ 0) :
    (∀ (v w : CVec n) (i j : ℕ), 0 < j →
      omegaC ((shifted A z ^ i) v) ((shifted A z⁻¹ ^ j) w) =
        -z⁻¹ * omegaC ((shifted A z ^ (i + 1)) v) ((shifted A z⁻¹ ^ j) w) -
        (z ^ 2)⁻¹ * omegaC ((shifted A z ^ (i + 1)) v) ((shifted A z⁻¹ ^ (j - 1)) w)) := by
  set Ac := complexify A with hAc
  set Jc := complexify (canonicalJ n) with hJc
  have hC : Acᵀ * Jc * Ac = Jc := by
    have := congrArg (Matrix.map · Complex.ofRealHom) hA
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map] at this
    exact this
  set Linv : Matrix (Coord n) (Coord n) ℂ := -(Jc * Acᵀ * Jc) with hLdef
  have hL : Linv * Ac = 1 := by
    have e : Jc * Acᵀ * Jc * Ac = Jc * (Acᵀ * Jc * Ac) := by simp only [Matrix.mul_assoc]
    rw [hLdef, neg_mul, e, hC, AuxN_J2, neg_neg]
  have hR : Ac * Linv = 1 := mul_eq_one_comm.1 hL
  set Lc : Module.End ℂ (Coord n → ℂ) := Matrix.toLin' Linv with hLc
  set Ap : Module.End ℂ (Coord n → ℂ) := Matrix.toLin' Ac with hAp
  have hLA : Lc * Ap = 1 := by rw [hLc, hAp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hL, Matrix.toLin'_one]; rfl
  have hAL : Ap * Lc = 1 := by rw [hLc, hAp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hR, Matrix.toLin'_one]; rfl
  have hN : ∀ c : ℂ, shifted A c = Ap - c • 1 := fun c => rfl
  have adj0 : ∀ x y, omegaC x (Ap y) = omegaC (Lc x) y := by
    intro x y
    rw [← AuxN_inv A hA (Lc x) y]
    show omegaC x (Ac *ᵥ y) = omegaC (Ac *ᵥ (Linv *ᵥ x)) (Ac *ᵥ y)
    rw [Matrix.mulVec_mulVec, hR, Matrix.one_mulVec]
  set S : Module.End ℂ (Coord n → ℂ) := Lc - z⁻¹ • 1 with hS
  have adj1 : ∀ x u, omegaC x (shifted A z⁻¹ u) = omegaC (S x) u := by
    intro x u
    rw [hN, hS]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [AuxN_sub_r, AuxN_sub_l, AuxN_smul_r, AuxN_smul_l, adj0]
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
  have hSm : ∀ k x, (S ^ k) x = (U ^ k) ((shifted A z ^ k) x) := by
    intro k x
    rw [hSU, Commute.mul_pow hUN, Module.End.mul_apply]
  have hUS : ∀ x, U x = (-z⁻¹) • S x - (z^2)⁻¹ • x := by
    intro x
    rw [hU, hS]
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply]
    rw [show (z^2)⁻¹ = z⁻¹ * z⁻¹ by rw [sq, mul_inv]]
    module
  have P1 : ∀ (v w : CVec n) (i j : ℕ), 0 < j →
      omegaC ((shifted A z ^ i) v) ((shifted A z⁻¹ ^ j) w) =
        -z⁻¹ * omegaC ((shifted A z ^ (i + 1)) v) ((shifted A z⁻¹ ^ j) w) -
        (z ^ 2)⁻¹ * omegaC ((shifted A z ^ (i + 1)) v) ((shifted A z⁻¹ ^ (j - 1)) w) := by
    intro v w i j hj
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [show j' + 1 - 1 = j' by omega, pow_succ' (shifted A z⁻¹) j', Module.End.mul_apply, adj1, adj1]
    rw [show S ((shifted A z ^ i) v) = U ((shifted A z ^ (i+1)) v) by
      rw [hSU, Module.End.mul_apply, pow_succ' (shifted A z) i, Module.End.mul_apply], hUS, AuxN_sub_l, AuxN_smul_l,
      AuxN_smul_l]
  exact P1

theorem _root_.solution {n : ℕ} (A : GroupedRealMatrix n)
    (hA : IsSymplectic A) (z : ℂ) (hz : ‖z‖ = 1) (he : IsEigenvalue A z)
    (v : CVec n) (hv : v ∈ generalizedSpace A z) :
    (∀ i j : ℕ, 0 < j → chainT A z v i j =
      -chainT A z v (i + 1) j - chainT A z v (i + 1) (j - 1)) ∧
    (∀ i j : ℕ, chainT A z v i j = -star (chainT A z v j i)) := by
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; exact zero_ne_one hz
  have hstar : star z = z⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hz]
    simp
  refine ⟨?_, ?_⟩
  · intro i j hj
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have h1 := AuxN_P1 A hA z hz0 v (star v) i (j' + 1) hj
    simp only [chainT, hstar, show j' + 1 - 1 = j' by omega] at h1 ⊢
    rw [h1]
    generalize omegaC ((shifted A z ^ (i + 1)) v) ((shifted A z⁻¹ ^ j') (star v)) = X
    generalize omegaC ((shifted A z ^ (i + 1)) v) ((shifted A z⁻¹ ^ (j' + 1)) (star v)) = Y
    field_simp
    have hzi : z * z⁻¹ = 1 := mul_inv_cancel₀ hz0
    linear_combination (z * z ^ i * z⁻¹ ^ j' * X) * hzi
  · intro i j
    simp only [chainT]
    rw [star_mul', AuxN_star_om, AuxN_star_pow, AuxN_star_pow, star_star, star_star,
      AuxN_skew]
    simp only [star_inv₀, star_mul', star_pow, star_star]
    ring

end QAlgorithms.Papers.Independent.Intake100.P39

end
