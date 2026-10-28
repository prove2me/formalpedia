-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P01.fullRankOutput_environmentDimension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:06:17.422146+00:00
-- url     : https://prove2.me/submissions/a15e2a54-d7b7-4241-93e9-031fd2fffe2e

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P01

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P01

open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel IsDegradable dilationPower maximumCoherentInformation)
open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)
open Matrix

variable {a b e : ℕ}

/-- coefficient matrix of `U ψ`. -/
def x5cdM (U : Matrix (Fin b × Fin e) (Fin a) ℂ) (ψ : EuclideanSpace ℂ (Fin a)) :
    Matrix (Fin b) (Fin e) ℂ :=
  Matrix.of fun j h => ∑ x, U (j, h) x * ψ x

/-- `U` reshaped as `(B × A) × E`. -/
def x5cdV (U : Matrix (Fin b × Fin e) (Fin a) ℂ) : Matrix (Fin b × Fin a) (Fin e) ℂ :=
  Matrix.of fun p h => U (p.1, h) p.2

theorem x5cd_recv (U : Matrix (Fin b × Fin e) (Fin a) ℂ) (ψ : EuclideanSpace ℂ (Fin a)) :
    receiverChannel U (pureDensity ψ) = x5cdM U ψ * (x5cdM U ψ)ᴴ := by
  ext j k
  simp only [receiverChannel, traceRight, pureDensity, x5cdM, Matrix.mul_apply,
    conjTranspose_apply, of_apply, star_sum, star_mul', RCLike.star_def]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp only [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem x5cd_comp (U : Matrix (Fin b × Fin e) (Fin a) ℂ) (ψ : EuclideanSpace ℂ (Fin a)) :
    complementaryChannel U (pureDensity ψ) = ((x5cdM U ψ)ᴴ * x5cdM U ψ)ᵀ := by
  ext h h'
  simp only [complementaryChannel, traceLeft, pureDensity, x5cdM, Matrix.mul_apply,
    conjTranspose_apply, of_apply, star_sum, star_mul', RCLike.star_def, transpose_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem x5cd_choi (U : Matrix (Fin b × Fin e) (Fin a) ℂ) :
    outputFirstChoi (receiverChannel U) = x5cdV U * (x5cdV U)ᴴ := by
  ext p q
  simp only [outputFirstChoi, QAlgorithms.Papers.Independent.Information100.P34.choi,
    receiverChannel, traceRight, x5cdV, Matrix.mul_apply, conjTranspose_apply, of_apply,
    Matrix.single_apply]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp only [mul_ite, mul_one, mul_zero, ite_and, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    ite_mul, zero_mul, Finset.sum_ite_eq']

theorem x5cd_compI (U : Matrix (Fin b × Fin e) (Fin a) ℂ) :
    (complementaryChannel U 1)ᵀ = (x5cdV U)ᴴ * x5cdV U := by
  ext h h'
  simp only [complementaryChannel, traceLeft, x5cdV, Matrix.mul_apply, conjTranspose_apply,
    of_apply, transpose_apply, Matrix.one_apply]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => ?_
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem x5cd_part1 (U : Matrix (Fin b × Fin e) (Fin a) ℂ) (ψ : EuclideanSpace ℂ (Fin a)) :
    (receiverChannel U (pureDensity ψ)).rank = (complementaryChannel U (pureDensity ψ)).rank := by
  rw [x5cd_recv, x5cd_comp, rank_transpose, rank_conjTranspose_mul_self,
    rank_self_mul_conjTranspose]

theorem x5cd_ker_rank {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ) (hw : w ≠ 0)
    (h : A *ᵥ w = 0) : A.rank < n := by
  have h1 := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hk : 0 < Module.finrank ℂ (LinearMap.ker A.mulVecLin) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨w, by simpa using h⟩, by simpa using hw⟩
  rw [Module.finrank_fin_fun] at h1
  rw [Matrix.rank]
  omega

theorem x5cd_star_kraus {p q : ℕ} (K : Matrix (Fin q) (Fin p) ℂ) (Y : Matrix (Fin p) (Fin q) ℂ) (w : Fin q → ℂ) :
    star w ⬝ᵥ ((K * (Y * Yᴴ) * Kᴴ) *ᵥ w) = star (Yᴴ *ᵥ (Kᴴ *ᵥ w)) ⬝ᵥ (Yᴴ *ᵥ (Kᴴ *ᵥ w)) := by
  have : (K * (Y * Yᴴ) * Kᴴ) *ᵥ w = (K * Y) *ᵥ (Yᴴ *ᵥ (Kᴴ *ᵥ w)) := by
    simp only [mulVec_mulVec, Matrix.mul_assoc]
  rw [this, dotProduct_mulVec, star_mulVec, star_mulVec, conjTranspose_conjTranspose,
    conjTranspose_conjTranspose, vecMul_vecMul]

theorem x5cd_part2 (U : Matrix (Fin b × Fin e) (Fin a) ℂ) (hU : ConjugateDegradable U)
    (m : ℕ) (psi : Fin m → EuclideanSpace ℂ (Fin a))
    (hmin : e = (outputFirstChoi (receiverChannel U)).rank)
    (hspan : (⨆ j, LinearMap.range (receiverChannel U (pureDensity (psi j))).mulVecLin) = ⊤) :
    (⨆ j, LinearMap.range (complementaryChannel U (pureDensity (psi j))).mulVecLin) = ⊤ := by
  obtain ⟨-, D, ⟨k, K, -, hDK⟩, hD⟩ := hU
  by_contra hne
  obtain ⟨f, hf0, hfS⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  set w : Fin e → ℂ := fun h => f (fun j => if h = j then 1 else 0) with hw
  have hfw : ∀ s, f s = ∑ h, s h * w h := by
    intro s
    conv_lhs => rw [pi_eq_sum_univ s]
    simp [map_sum, map_smul, hw]
  have hw0 : w ≠ 0 := by
    intro h0; apply hf0; ext s; simp [hfw, h0]
  have h1 : ∀ j, (x5cdM U (psi j)) *ᵥ w = 0 := by
    intro j
    have : ((x5cdM U (psi j))ᴴ * x5cdM U (psi j)) *ᵥ w = 0 := by
      funext h
      have hm : f ((complementaryChannel U (pureDensity (psi j))) *ᵥ
          (fun i => if h = i then 1 else 0)) = 0 :=
        hfS (Submodule.mem_iSup_of_mem j (LinearMap.mem_range_self _ _))
      rw [hfw, x5cd_comp] at hm
      simpa [mulVec, dotProduct, transpose_apply, mul_comm] using hm
    exact (conjTranspose_mul_self_mulVec_eq_zero _ _).mp this
  have h2 : ∀ i, (K i)ᴴ *ᵥ w = 0 := by
    intro i
    have h3 : ∀ j, (x5cdM U (psi j))ᴴ *ᵥ ((K i)ᴴ *ᵥ w) = 0 := by
      intro j
      have hDj := hD (pureDensity (psi j))
      rw [hDK, x5cd_recv, x5cd_comp, transpose_transpose] at hDj
      have h0 : star w ⬝ᵥ (krausApply K (x5cdM U (psi j) * (x5cdM U (psi j))ᴴ) *ᵥ w) = 0 := by
        rw [hDj, ← mulVec_mulVec, h1 j, mulVec_zero, dotProduct_zero]
      simp only [krausApply, sum_mulVec, dotProduct_sum] at h0
      rw [Finset.sum_congr rfl fun i _ => x5cd_star_kraus (K i) (x5cdM U (psi j)) w] at h0
      have hnn : ∀ i ∈ (Finset.univ : Finset (Fin k)),
          0 ≤ star ((x5cdM U (psi j))ᴴ *ᵥ (K i)ᴴ *ᵥ w) ⬝ᵥ ((x5cdM U (psi j))ᴴ *ᵥ (K i)ᴴ *ᵥ w) :=
        fun i _ => dotProduct_star_self_nonneg _
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h0 i (Finset.mem_univ _)
      exact dotProduct_star_self_eq_zero.mp this
    set y := (K i)ᴴ *ᵥ w
    let g : (Fin b → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun v => star y ⬝ᵥ v
        map_add' := fun u v => dotProduct_add _ _ _
        map_smul' := fun c v => by simp [dotProduct_smul] }
    have hle : (⨆ j, LinearMap.range (receiverChannel U (pureDensity (psi j))).mulVecLin) ≤
        LinearMap.ker g := by
      refine iSup_le fun j => ?_
      rintro _ ⟨x, rfl⟩
      show star y ⬝ᵥ ((receiverChannel U (pureDensity (psi j))) *ᵥ x) = 0
      rw [x5cd_recv, ← mulVec_mulVec, dotProduct_mulVec]
      have : star y ᵥ* x5cdM U (psi j) = star ((x5cdM U (psi j))ᴴ *ᵥ y) := by
        rw [star_mulVec (x5cdM U (psi j))ᴴ y, conjTranspose_conjTranspose]
      rw [this, h3 j, star_zero, zero_dotProduct]
    rw [hspan] at hle
    have : g y = 0 := hle Submodule.mem_top
    exact dotProduct_star_self_eq_zero.mp this
  have h4 : ((x5cdV U)ᴴ * x5cdV U) *ᵥ w = 0 := by
    rw [← x5cd_compI, ← hD 1, hDK]
    simp only [krausApply, sum_mulVec]
    exact Finset.sum_eq_zero fun i _ => by rw [← mulVec_mulVec, h2 i, mulVec_zero]
  have := x5cd_ker_rank _ w hw0 h4
  rw [rank_conjTranspose_mul_self, ← rank_self_mul_conjTranspose, ← x5cd_choi, ← hmin] at this
  exact lt_irrefl _ this

end QAlgorithms.Papers.Independent.Support50.P01

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P01
open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel IsDegradable dilationPower maximumCoherentInformation)
open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)
open scoped Matrix ComplexConjugate ComplexOrder

theorem solution {a b e : ℕ} (ha : 0<a) (hb : 0<b) (he : 0<e)
    (U : Matrix (Fin b × Fin e) (Fin a) ℂ) (hU : ConjugateDegradable U)
    (hminimal : e = (outputFirstChoi (receiverChannel U)).rank)
    (hfull : ∃ psi : EuclideanSpace ℂ (Fin a), ‖psi‖ = 1 ∧
      (receiverChannel U (pureDensity psi)).rank = b) : b=e := by
  obtain ⟨ψ, -, hr⟩ := hfull
  have h1 := x5cd_part1 U ψ
  have hspan : (⨆ _j : Fin 1, LinearMap.range
      (receiverChannel U (pureDensity ((fun _ => ψ) _j))).mulVecLin) = ⊤ := by
    rw [iSup_const]
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]
    exact hr
  have h2 := x5cd_part2 U hU 1 (fun _ => ψ) hminimal hspan
  rw [iSup_const] at h2
  have h3 : (complementaryChannel U (pureDensity ψ)).rank = e := by
    rw [Matrix.rank, h2, finrank_top, Module.finrank_fin_fun]
  omega
