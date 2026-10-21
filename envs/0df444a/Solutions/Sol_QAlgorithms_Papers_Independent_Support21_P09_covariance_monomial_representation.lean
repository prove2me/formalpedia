-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P09.covariance_monomial_representation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:30:11.489834+00:00
-- url     : https://prove2.me/submissions/9abecd1a-c8b9-43b5-899c-e4e84c230e4d

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P09
noncomputable section
open QAlgorithms.Papers.Independent.Support21.P09
open scoped BigOperators ComplexConjugate
open Matrix
open QAlgorithms.Papers.Independent.Frontier18.P17 (clock)

theorem g66c_conj_pure {I : Type*} [Fintype I] (A : Matrix I I ℂ) (w : I → ℂ) :
    A * Matrix.vecMulVec w (star w) * A.conjTranspose =
      Matrix.vecMulVec (A *ᵥ w) (star (A *ᵥ w)) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

theorem g66c_eff_eq {I O : Type*} [Fintype I] (M : Matrix I O ℂ) (o : O) :
    columnEffect M o = Matrix.vecMulVec (fun i => M i o) (star (fun i => M i o)) := by
  ext a b; rfl

theorem g66c_phase {I : Type*} [Fintype I] (w u : I → ℂ) (hu : u ≠ 0)
    (h : Matrix.vecMulVec w (star w) = Matrix.vecMulVec u (star u)) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ w = z • u := by
  obtain ⟨k, hk⟩ : ∃ k, u k ≠ 0 := by
    by_contra hc; push Not at hc; exact hu (funext hc)
  have hkk := congrFun (congrFun h k) k
  simp only [Matrix.vecMulVec_apply, Pi.star_apply, RCLike.star_def] at hkk
  rw [Complex.mul_conj, Complex.mul_conj] at hkk
  have hn : Complex.normSq (w k) = Complex.normSq (u k) := by exact_mod_cast hkk
  have hwk : w k ≠ 0 := by
    intro h0; rw [h0, map_zero] at hn; exact hk (Complex.normSq_eq_zero.mp hn.symm)
  refine ⟨conj (u k) / conj (w k), ?_, ?_⟩
  · rw [norm_div, Complex.norm_conj, Complex.norm_conj]
    have : ‖w k‖ = ‖u k‖ := by
      rw [← Real.sqrt_sq (norm_nonneg (w k)), ← Real.sqrt_sq (norm_nonneg (u k)),
        ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, hn]
    rw [this, div_self (norm_ne_zero_iff.mpr hk)]
  · funext i
    have hik := congrFun (congrFun h i) k
    simp only [Matrix.vecMulVec_apply, Pi.star_apply, RCLike.star_def] at hik
    have hc : conj (w k) ≠ 0 := (map_ne_zero _).mpr hwk
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination hik

theorem solution
    {G : Type*} [Group G] [Fintype G] {d n : ℕ} (hd : 0 < d)
    (phi : Rep G (Fin d)) (hphi : UnitaryRep phi)
    (M : Matrix (Fin d) (Fin n) ℂ) (hM : RankOnePOVM M)
    (hdist : Function.Injective (columnEffect M)) (hcov : EffectsCovariant phi M) :
    ∃ R : Rep G (Fin n), ∃ pi : G →* Equiv.Perm (Fin n), ∃ z : G → Fin n → ℂ,
      UnitaryRep R ∧ (∀ g j, ‖z g j‖ = 1) ∧
      (∀ g i j, R g i j = if i = pi g j then z g j else 0) ∧
      (∀ g j i, (phi g).mulVec (fun r => M r j) i = z g j * M i (pi g j)) ∧
      MatrixIntertwines phi R M := by
  classical
  have hm0 : ∀ j, (fun i => M i j) ≠ 0 := hM.1
  choose σ hσ using hcov
  have hconj : ∀ g h (X : Matrix (Fin d) (Fin d) ℂ), phi (g * h) * X * (phi (g * h))ᴴ =
      phi g * (phi h * X * (phi h)ᴴ) * (phi g)ᴴ := by
    intro g h X
    rw [map_mul, conjTranspose_mul]; simp only [Matrix.mul_assoc]
  have hσmul : ∀ g h o, σ (g * h) o = σ g (σ h o) := by
    intro g h o; apply hdist; rw [← hσ, ← hσ, ← hσ, hconj]
  have hσone : ∀ o, σ 1 o = o := by
    intro o; apply hdist; rw [← hσ, map_one]; simp
  let pi : G →* Equiv.Perm (Fin n) :=
    { toFun := fun g =>
        { toFun := σ g, invFun := σ g⁻¹,
          left_inv := fun o => by rw [← hσmul, inv_mul_cancel, hσone],
          right_inv := fun o => by rw [← hσmul, mul_inv_cancel, hσone] }
      map_one' := by ext o; simp [hσone]
      map_mul' := by intro g h; ext o; simp [hσmul, Equiv.Perm.mul_apply] }
  have hpi : ∀ g o, pi g o = σ g o := fun _ _ => rfl
  have hph : ∀ g j, ∃ c : ℂ, ‖c‖ = 1 ∧
      phi g *ᵥ (fun i => M i j) = c • (fun i => M i (σ g j)) := by
    intro g j
    apply g66c_phase _ _ (hm0 (σ g j))
    have := hσ g j
    rw [g66c_eff_eq, g66c_eff_eq, g66c_conj_pure] at this
    exact this
  choose z hz1 hz using hph
  have hcancel : ∀ (a b : ℂ) j, a • (fun i => M i j) = b • (fun i => M i j) → a = b := by
    intro a b j h
    have h2 : (a - b) • (fun i => M i j) = 0 := by rw [sub_smul, h, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 (hm0 j)
  have hzmul : ∀ g h j, z (g * h) j = z g (σ h j) * z h j := by
    intro g h j
    apply hcancel _ _ (σ g (σ h j))
    rw [← hσmul, ← hz, map_mul, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_smul, hz, smul_smul,
      hσmul, mul_comm]
  have hzone : ∀ j, z 1 j = 1 := by
    intro j
    apply hcancel _ _ j
    have := hz 1 j
    rw [map_one, Matrix.one_mulVec, hσone] at this
    rw [← this, one_smul]
  let R : Rep G (Fin n) :=
    { toFun := fun g => Matrix.of fun i j => if i = σ g j then z g j else 0
      map_one' := by
        ext i j
        simp only [Matrix.of_apply, hσone, hzone, Matrix.one_apply]
      map_mul' := by
        intro g h
        ext i j
        simp only [Matrix.of_apply, Matrix.mul_apply, mul_ite, mul_zero, ite_mul, zero_mul]
        rw [Finset.sum_ite_eq']
        simp only [Finset.mem_univ, if_true, hσmul, hzmul] }
  refine ⟨R, pi, z, ?_, hz1, fun g i j => rfl, ?_, ?_⟩
  · intro g
    rw [Matrix.mem_unitaryGroup_iff']
    ext j j'
    simp only [R, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.mul_apply, Matrix.star_apply,
      Matrix.of_apply, Matrix.one_apply]
    simp only [apply_ite star, star_zero, ite_mul, zero_mul, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    by_cases hj : j = j'
    · subst hj
      simp only [if_true]
      rw [RCLike.star_def, Complex.conj_mul', hz1]; simp
    · have : σ g j ≠ σ g j' := fun h => hj ((pi g).injective h)
      rw [if_neg (Ne.symm this), if_neg hj]
  · intro g j i
    have := congrFun (hz g j) i
    rw [this, hpi]; simp
  · intro g
    ext i j
    have h1 := congrFun (hz g j) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1
    simp only [R, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.mul_apply, Matrix.of_apply, mul_ite,
      mul_zero]
    rw [h1, Finset.sum_ite_eq']
    simp [mul_comm]

end
