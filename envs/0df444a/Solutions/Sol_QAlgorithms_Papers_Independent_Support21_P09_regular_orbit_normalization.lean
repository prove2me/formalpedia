-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P09.regular_orbit_normalization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:22:03.9738+00:00
-- url     : https://prove2.me/submissions/919d0113-6e51-48e2-ba25-df8ab6577d39

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P09
noncomputable section
open QAlgorithms.Papers.Independent.Support21.P09
open scoped BigOperators ComplexConjugate
open Matrix
open scoped ComplexOrder
open QAlgorithms.Papers.Independent.Frontier18.P17 (clock)

theorem g66c_schur {G I : Type*} [Fintype I] [DecidableEq I]
    (phi : G → Matrix I I ℂ) (hirr : QAlgorithms.Papers.Independent.Support21.P09.Irreducible phi)
    (T : Matrix I I ℂ) (hT : ∀ g, phi g * T = T * phi g) :
    ∃ c : ℂ, T = c • 1 := by
  have : Nonempty I := hirr.1
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' T)
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  refine ⟨c, ?_⟩
  have hinv := hirr.2 (LinearMap.ker (Matrix.toLin' (T - c • 1))) (by
    intro g w hw
    rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hw ⊢
    have e1 : (T - c • 1) * phi g = phi g * (T - c • 1) := by
      rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, ← hT g, Matrix.mul_sub, Matrix.mul_smul,
        Matrix.mul_one]
    rw [Matrix.mulVec_mulVec, e1, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero])
  rcases hinv with h | h
  · exfalso
    have hv1 : v ∈ LinearMap.ker (Matrix.toLin' (T - c • 1)) := by
      rw [LinearMap.mem_ker, map_sub, LinearMap.sub_apply, hv.apply_eq_smul, map_smul,
        Matrix.toLin'_one]
      simp
    rw [h] at hv1
    exact hv.2 ((Submodule.mem_bot ℂ).1 hv1)
  · have : Matrix.toLin' (T - c • 1) = 0 := LinearMap.ker_eq_top.1 h
    have h2 : T - c • 1 = 0 := Matrix.toLin'.injective (by rw [this, map_zero])
    exact sub_eq_zero.1 h2

theorem g66c_conj_pure {I : Type*} [Fintype I] (A : Matrix I I ℂ) (w : I → ℂ) :
    A * Matrix.vecMulVec w (star w) * A.conjTranspose =
      Matrix.vecMulVec (A *ᵥ w) (star (A *ᵥ w)) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

theorem g66c_norm_unitary {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (w : I → ℂ) :
    star (A *ᵥ w) ⬝ᵥ (A *ᵥ w) = star w ⬝ᵥ w := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
  have : A.conjTranspose * A = 1 := Matrix.mem_unitaryGroup_iff'.mp hA
  rw [this, Matrix.one_mulVec]

theorem g66c_star_dot {I : Type*} [Fintype I] (w : I → ℂ) :
    star w ⬝ᵥ w = ((∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.star_def, Complex.conj_mul']

theorem solution
    {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ} (hd : 0 < d)
    (phi : Rep G (Fin d)) (hphi : UnitaryRep phi) (v : Fin d → ℂ) :
    MatrixIntertwines phi groupLeftRegular (orbitMatrix phi v) ∧
    (Irreducible phi → (∑ i, ‖v i‖ ^ 2) = (d : ℝ) / Fintype.card G →
      RankOnePOVM (orbitMatrix phi v)) := by
  refine ⟨?_, ?_⟩
  · intro g
    ext i t
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [orbitMatrix, groupLeftRegular, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
    have : (phi g * phi t) *ᵥ v = phi g *ᵥ (phi t *ᵥ v) := (Matrix.mulVec_mulVec _ _ _).symm
    rw [← map_mul] at this
    rw [this]
    simp [Matrix.mulVec, dotProduct]
  · intro hirr hnorm
    have hG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
    have hEff : ∀ g, columnEffect (orbitMatrix phi v) g =
        phi g * Matrix.vecMulVec v (star v) * (phi g).conjTranspose := by
      intro g
      rw [g66c_conj_pure]
      ext a b
      rfl
    refine ⟨?_, ?_, ?_⟩
    · intro g hz
      have h0 : phi g *ᵥ v = 0 := hz
      have h1 := g66c_norm_unitary (phi g) (hphi g) v
      rw [h0, g66c_star_dot v] at h1
      simp only [star_zero, zero_dotProduct] at h1
      have h2 : (∑ i, ‖v i‖ ^ 2 : ℝ) = 0 := by exact_mod_cast h1.symm
      rw [hnorm] at h2
      have : (0 : ℝ) < (d : ℝ) / Fintype.card G := div_pos (by exact_mod_cast hd) hG
      linarith
    · intro g
      exact Matrix.posSemidef_vecMulVec_self_star _
    · set S := ∑ g, columnEffect (orbitMatrix phi v) g with hS
      have hS' : S = ∑ g, phi g * Matrix.vecMulVec v (star v) * (phi g).conjTranspose :=
        Finset.sum_congr rfl fun g _ => hEff g
      have hcomm : ∀ h, phi h * S = S * phi h := by
        intro h
        rw [hS', Finset.mul_sum, Finset.sum_mul]
        conv_rhs => rw [← Equiv.sum_comp (Equiv.mulLeft h)]
        refine Finset.sum_congr rfl fun g _ => ?_
        simp only [Equiv.coe_mulLeft, map_mul]
        have hu : (phi h).conjTranspose * phi h = 1 := Matrix.mem_unitaryGroup_iff'.mp (hphi h)
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
        rw [hu, Matrix.mul_one]
      obtain ⟨c, hc⟩ := g66c_schur (fun g => phi g) hirr S hcomm
      have htr : S.trace = (d : ℂ) := by
        rw [hS, Matrix.trace_sum]
        have : ∀ g, (columnEffect (orbitMatrix phi v) g).trace = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
          intro g
          rw [hEff, g66c_conj_pure, Matrix.trace_vecMulVec, dotProduct_comm,
            g66c_norm_unitary _ (hphi g), g66c_star_dot]
        simp only [this, Finset.sum_const, Finset.card_univ, hnorm, nsmul_eq_mul]
        push_cast
        field_simp
      rw [hc, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul] at htr
      have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
      have hc1 : c = 1 := by
        have := htr
        field_simp at this
        exact this
      rw [hc, hc1, one_smul]

end
