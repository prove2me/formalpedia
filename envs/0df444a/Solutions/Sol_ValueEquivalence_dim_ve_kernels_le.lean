-- Prove2me | solution 1 for ValueEquivalence.dim_ve_kernels_le
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T07:15:04.219933+00:00
-- url     : https://prove2.me/submissions/cc269741-ca3d-4912-bde2-3ecd25fec912

import Mathlib
import Definitions.Def_ValueEquivalence_Basic

open Matrix

namespace ValueEquivalence

theorem ve5_rightInv {ι : Type*} [Fintype ι] {n : ℕ} (f : Fin n → ι → ℝ)
    (hf : LinearIndependent ℝ f) : ∃ X : Matrix ι (Fin n) ℝ, Matrix.of f * X = 1 := by
  rw [← Matrix.mulVec_surjective_iff_exists_right_inverse]
  have hr : (Matrix.of f).rank = n := by
    have := LinearIndependent.rank_matrix (M := Matrix.of f) hf
    simpa using this
  have htop : LinearMap.range (Matrix.of f).mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank, hr]; simp
  intro y
  have : y ∈ LinearMap.range (Matrix.of f).mulVecLin := by rw [htop]; trivial
  obtain ⟨x, hx⟩ := this
  exact ⟨x, hx⟩

/-- the linear map `B ↦ (s,i,j) ↦ Σ_a pol i s a Σ_s' B s a s' vs j s'` -/
noncomputable def ve5_L {S A : Type*} [Fintype S] [Fintype A] {m k : ℕ}
    (pol : Fin m → S → A → ℝ) (vs : Fin k → S → ℝ) :
    (S → A → S → ℝ) →ₗ[ℝ] (S → Fin m → Fin k → ℝ) where
  toFun B s i j := ∑ a, pol i s a * ∑ s', B s a s' * vs j s'
  map_add' B C := by
    ext s i j; simp [add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' c B := by
    ext s i j; simp [Finset.mul_sum, mul_assoc, mul_left_comm]

theorem ve5_L_apply {S A : Type*} [Fintype S] [Fintype A] {m k : ℕ}
    (pol : Fin m → S → A → ℝ) (vs : Fin k → S → ℝ) (B : S → A → S → ℝ) (s : S) :
    ve5_L pol vs B s =
      Matrix.of (fun i a => pol i s a) * Matrix.of (B s) * (Matrix.of vs)ᵀ := by
  ext i j
  simp only [ve5_L, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_apply, Matrix.of_apply,
    Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [mul_assoc]

theorem ve5_L_surj {S A : Type*} [Fintype S] [Fintype A] {m k : ℕ}
    (pol : Fin m → S → A → ℝ) (hind : ∀ s, LinearIndependent ℝ (fun i => pol i s))
    (vs : Fin k → S → ℝ) (hvs : LinearIndependent ℝ vs) :
    Function.Surjective (ve5_L pol vs) := by
  intro T
  choose X hX using fun s => ve5_rightInv (fun i => pol i s) (hind s)
  obtain ⟨Y, hY⟩ := ve5_rightInv vs hvs
  refine ⟨fun s a s' => (X s * Matrix.of (T s) * Yᵀ) a s', ?_⟩
  funext s
  rw [ve5_L_apply pol vs _ s]
  have h1 : Matrix.of (fun i a => pol i s a) * X s = 1 := hX s
  have h2 : Yᵀ * (Matrix.of vs)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hY, Matrix.transpose_one]
  have : Matrix.of (fun i a => pol i s a) * Matrix.of (fun a s' => (X s * Matrix.of (T s) * Yᵀ) a s') *
      (Matrix.of vs)ᵀ = Matrix.of (T s) := by
    change Matrix.of (fun i a => pol i s a) * (X s * Matrix.of (T s) * Yᵀ) *
      (Matrix.of vs)ᵀ = Matrix.of (T s)
    simp only [Matrix.mul_assoc]
    rw [h2, Matrix.mul_one, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [this]; rfl

theorem ve5_finrank_ker {S A : Type*} [Fintype S] [Fintype A] {m k : ℕ}
    (pol : Fin m → S → A → ℝ) (hind : ∀ s, LinearIndependent ℝ (fun i => pol i s))
    (vs : Fin k → S → ℝ) (hvs : LinearIndependent ℝ vs) :
    Module.finrank ℝ (LinearMap.ker (ve5_L pol vs)) + Fintype.card S * m * k =
      Fintype.card S * Fintype.card A * Fintype.card S := by
  have h := LinearMap.finrank_range_add_finrank_ker (ve5_L pol vs)
  rw [LinearMap.range_eq_top.mpr (ve5_L_surj pol hind vs hvs), finrank_top] at h
  simp only [Module.finrank_pi_fintype, Module.finrank_self, Fintype.card_fin,
    Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  linarith [h]

theorem ve5_sub_mem_ker {S A : Type*} [Fintype S] [Fintype A] {m k : ℕ}
    (γ : ℝ) (hγ0 : 0 < γ) (mstar : Model S A)
    (pol : Fin m → S → A → ℝ) (vs : Fin k → S → ℝ) :
    (fun x => x + (-mstar.p)) '' veKernels γ mstar Set.univ (Set.range pol) (Set.range vs) ⊆
      (LinearMap.ker (ve5_L pol vs) : Set (S → A → S → ℝ)) := by
  rintro _ ⟨P, ⟨m', ⟨⟨hr, -⟩, hve⟩, rfl⟩, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker]
  funext s i j
  have h := congrFun (hve (pol i) ⟨i, rfl⟩ (vs j) ⟨j, rfl⟩) s
  simp only [bellman, hr] at h
  show ∑ a, pol i s a * ∑ s', (m'.p s a s' + -mstar.p s a s') * vs j s' = 0
  have key : γ * (∑ a, pol i s a * ∑ s', (m'.p s a s' + -mstar.p s a s') * vs j s') =
      (∑ a, pol i s a * (mstar.r s a + γ * ∑ s', m'.p s a s' * vs j s')) -
        ∑ a, pol i s a * (mstar.r s a + γ * ∑ s', mstar.p s a s' * vs j s') := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [add_mul, neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    ring
  rw [← h, sub_self] at key
  exact (mul_eq_zero.mp key).resolve_left hγ0.ne'

end ValueEquivalence

open ValueEquivalence in
theorem solution {S A : Type*} [Fintype S] [Fintype A] {m k : ℕ}
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (mstar : Model S A)
    (pol : Fin m → S → A → ℝ) (hpol : ∀ i, pol i ∈ policies)
    (hind : ∀ s, LinearIndependent ℝ (fun i => pol i s))
    (vs : Fin k → S → ℝ) (hvs : LinearIndependent ℝ vs) :
    (setDim (veKernels γ mstar Set.univ (Set.range pol) (Set.range vs)) : ℤ) ≤
      (Fintype.card S : ℤ) * ((Fintype.card S : ℤ) * Fintype.card A - (m : ℤ) * k) := by
  have hle : setDim (veKernels γ mstar Set.univ (Set.range pol) (Set.range vs)) ≤
      Module.finrank ℝ (LinearMap.ker (ve5_L pol vs)) :=
    Nat.sInf_le ⟨_, -mstar.p, ve5_sub_mem_ker γ hγ0 mstar pol vs, rfl⟩
  have hk := ve5_finrank_ker pol hind vs hvs
  have hk' : (Module.finrank ℝ (LinearMap.ker (ve5_L pol vs)) : ℤ) +
      (Fintype.card S : ℤ) * m * k =
      (Fintype.card S : ℤ) * Fintype.card A * Fintype.card S := by
    exact_mod_cast hk
  have hle' : (setDim (veKernels γ mstar Set.univ (Set.range pol) (Set.range vs)) : ℤ) ≤
      Module.finrank ℝ (LinearMap.ker (ve5_L pol vs)) := by exact_mod_cast hle
  linarith
