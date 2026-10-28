-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P01.qubitOutput_dimensionBounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:29:08.914036+00:00
-- url     : https://prove2.me/submissions/e4e253b4-e873-47a1-ac83-4b5298b2b642

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

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P01

open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel IsDegradable dilationPower maximumCoherentInformation)
open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)
open Matrix

variable {a b e : ℕ}

def x5cdR1 {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) : Prop :=
  ∀ i j h k, M i h * M j k = M i k * M j h

def x5cdPar {n : ℕ} (p q : Fin n → ℂ) : Prop := ∀ i j, p i * q j = p j * q i

theorem x5cd_unit {n : ℕ} (ψ : EuclideanSpace ℂ (Fin n)) (h : ‖ψ‖ = 1) :
    star (ψ : Fin n → ℂ) ⬝ᵥ (ψ : Fin n → ℂ) = 1 := by
  have h1 : (inner ℂ ψ ψ : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, h]; simp
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h1
  rw [dotProduct_comm]; exact h1

theorem x5cd_fact {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) (φ : Fin m → ℂ)
    (hφ : star φ ⬝ᵥ φ = 1) (h : M * Mᴴ = vecMulVec φ (star φ)) :
    M = vecMulVec φ (star φ ᵥ* M) := by
  set P := vecMulVec φ (star φ) with hP
  have hPP : P * P = P := by
    rw [hP, vecMulVec_mul_vecMulVec, hφ, one_smul]
  have hPh : Pᴴ = P := by
    rw [hP, conjTranspose_vecMulVec, star_star]
  have hPM : vecMulVec φ (star φ ᵥ* M) = P * M := by rw [hP, vecMulVec_mul]
  rw [hPM]
  have e1 : (M - P * M) * (M - P * M)ᴴ = 0 := by
    have hM' : M - P * M = (1 - P) * M := by rw [Matrix.sub_mul, Matrix.one_mul]
    rw [hM', conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hPh]
    have : (1 - P) * M * (Mᴴ * (1 - P)) = (1 - P) * (M * Mᴴ) * (1 - P) := by
      simp only [Matrix.mul_assoc]
    rw [this, h, Matrix.sub_mul, Matrix.one_mul, hPP, sub_self, Matrix.zero_mul]
  have e2 : (M - P * M)ᴴ = 0 := by
    apply conjTranspose_mul_self_eq_zero.mp
    rwa [conjTranspose_conjTranspose]
  have e3 : M - P * M = 0 := by
    rw [← conjTranspose_conjTranspose (M - P * M), e2, conjTranspose_zero]
  exact (sub_eq_zero.mp e3)

theorem x5cd_R1_vmv {m n : ℕ} (u : Fin m → ℂ) (v : Fin n → ℂ) : x5cdR1 (vecMulVec u v) := by
  intro i j h k; simp only [vecMulVec_apply]; ring

theorem x5cd_R1_smul {m n : ℕ} (c : ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (h : x5cdR1 M) :
    x5cdR1 (c • M) := by
  intro i j h' k; simp only [Matrix.smul_apply, smul_eq_mul]
  linear_combination c * c * h i j h' k

theorem x5cd_M_smul (U : Matrix (Fin b × Fin e) (Fin a) ℂ) (c : ℂ) (ψ : EuclideanSpace ℂ (Fin a)) :
    x5cdM U (c • ψ) = c • x5cdM U ψ := by
  ext j h; simp [x5cdM, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring

theorem x5cd_M_add (U : Matrix (Fin b × Fin e) (Fin a) ℂ) (ψ ψ' : EuclideanSpace ℂ (Fin a)) :
    x5cdM U (ψ + ψ') = x5cdM U ψ + x5cdM U ψ' := by
  ext j h; simp [x5cdM, mul_add, Finset.sum_add_distrib]

theorem x5cd_M_single (U : Matrix (Fin b × Fin e) (Fin a) ℂ) (x : Fin a) :
    x5cdM U (EuclideanSpace.single x 1) = Matrix.of fun j h => U (j, h) x := by
  ext j h; simp [x5cdM]

theorem x5cd_pure_fact (U : Matrix (Fin b × Fin e) (Fin a) ℂ)
    (hpure : ∀ psi : EuclideanSpace ℂ (Fin a), ‖psi‖ = 1 →
      ∃ phi : EuclideanSpace ℂ (Fin b), ‖phi‖ = 1 ∧
        receiverChannel U (pureDensity psi) = pureDensity phi)
    (ψ : EuclideanSpace ℂ (Fin a)) (hψ : ‖ψ‖ = 1) :
    ∃ φ : Fin b → ℂ, star φ ⬝ᵥ φ = 1 ∧ x5cdM U ψ = vecMulVec φ (star φ ᵥ* x5cdM U ψ) := by
  obtain ⟨φ, hφ1, hφ⟩ := hpure ψ hψ
  refine ⟨φ, x5cd_unit φ hφ1, x5cd_fact _ _ (x5cd_unit φ hφ1) ?_⟩
  rw [← x5cd_recv, hφ]
  ext i j; simp [pureDensity, vecMulVec_apply]

theorem x5cd_R1_all (U : Matrix (Fin b × Fin e) (Fin a) ℂ)
    (hpure : ∀ psi : EuclideanSpace ℂ (Fin a), ‖psi‖ = 1 →
      ∃ phi : EuclideanSpace ℂ (Fin b), ‖phi‖ = 1 ∧
        receiverChannel U (pureDensity psi) = pureDensity phi)
    (ψ : EuclideanSpace ℂ (Fin a)) : x5cdR1 (x5cdM U ψ) := by
  by_cases h0 : ψ = 0
  · subst h0
    have : x5cdM U (0 : EuclideanSpace ℂ (Fin a)) = 0 := by ext; simp [x5cdM]
    rw [this]; intro i j h k; simp
  · have hn : ‖ψ‖ ≠ 0 := norm_ne_zero_iff.mpr h0
    set ψ' := ((‖ψ‖⁻¹ : ℝ) : ℂ) • ψ
    have hψ' : ‖ψ'‖ = 1 := by
      rw [norm_smul]; simp [hn]
    have he : ψ = ((‖ψ‖ : ℝ) : ℂ) • ψ' := by
      rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn]; simp
    obtain ⟨φ, -, hf⟩ := x5cd_pure_fact U hpure ψ' hψ'
    rw [he, x5cd_M_smul, hf]
    exact x5cd_R1_smul _ _ (x5cd_R1_vmv _ _)

theorem x5cd_par_symm {n : ℕ} {p q : Fin n → ℂ} (h : x5cdPar p q) : x5cdPar q p := by
  intro i j; have := h j i; linear_combination this

theorem x5cd_par_trans {n : ℕ} {p q r : Fin n → ℂ} (hq : q ≠ 0) (h1 : x5cdPar p q)
    (h2 : x5cdPar q r) : x5cdPar p r := by
  obtain ⟨k, hk⟩ : ∃ k, q k ≠ 0 := by
    by_contra hc; push_neg at hc; exact hq (funext hc)
  intro i j
  have e1 := h1 i k; have e2 := h1 j k; have e3 := h2 k j; have e4 := h2 k i
  have : (p i * r j - p j * r i) * (q k * q k) = 0 := by
    linear_combination (r j * q k) * e1 - (r i * q k) * e2 + (p k * q i) * e3 - (p k * q j) * e4
  have hqq : q k * q k ≠ 0 := mul_ne_zero hk hk
  have := (mul_eq_zero.mp this).resolve_right hqq
  linear_combination this

theorem x5cd_par_proj {n : ℕ} {p q : Fin n → ℂ} (hp : star p ⬝ᵥ p = 1) (h : x5cdPar p q) :
    ∀ i, q i = p i * (star p ⬝ᵥ q) := by
  intro i
  have e : p i * (star p ⬝ᵥ q) = q i * (star p ⬝ᵥ p) := by
    simp only [dotProduct, Finset.mul_sum, Pi.star_apply]
    exact Finset.sum_congr rfl fun j _ => by linear_combination (star (p j)) * h i j
  rw [e, hp, mul_one]

theorem x5cd_cross {m n : ℕ} (u u' : Fin m → ℂ) (χ χ' : Fin n → ℂ)
    (h : x5cdR1 (vecMulVec u χ + vecMulVec u' χ')) : x5cdPar u u' ∨ x5cdPar χ χ' := by
  by_contra hc
  push_neg at hc
  obtain ⟨hu, hχ⟩ := hc
  simp only [x5cdPar, not_forall] at hu hχ
  obtain ⟨i, j, hij⟩ := hu
  obtain ⟨h', k, hhk⟩ := hχ
  have e := h i j h' k
  simp only [Matrix.add_apply, vecMulVec_apply] at e
  have : (u i * u' j - u j * u' i) * (χ h' * χ' k - χ k * χ' h') = 0 := by
    linear_combination e
  rcases mul_eq_zero.mp this with h1 | h1
  · exact hij (sub_eq_zero.mp h1)
  · exact hhk (sub_eq_zero.mp h1)

theorem x5cd_global {a m n : ℕ} (u : Fin a → Fin m → ℂ) (χ : Fin a → Fin n → ℂ)
    (hu : ∀ x, u x ≠ 0) (hχ : ∀ x, χ x ≠ 0)
    (h : ∀ x y, x5cdPar (u x) (u y) ∨ x5cdPar (χ x) (χ y)) :
    (∀ x y, x5cdPar (u x) (u y)) ∨ (∀ x y, x5cdPar (χ x) (χ y)) := by
  by_contra hc
  push_neg at hc
  obtain ⟨⟨x1, y1, hxy⟩, hχn⟩ := hc
  have hc1 : x5cdPar (χ x1) (χ y1) := (h x1 y1).resolve_left hxy
  have hall : ∀ z, x5cdPar (χ x1) (χ z) := by
    intro z
    by_cases hz1 : x5cdPar (u x1) (u z)
    · have hz2 : ¬ x5cdPar (u y1) (u z) := fun hz2 =>
        hxy (x5cd_par_trans (hu z) hz1 (x5cd_par_symm hz2))
      exact x5cd_par_trans (hχ y1) hc1 ((h y1 z).resolve_left hz2)
    · exact (h x1 z).resolve_left hz1
  obtain ⟨x, y, hn⟩ := hχn
  exact hn (x5cd_par_trans (hχ x1) (x5cd_par_symm (hall x)) (hall y))

theorem x5cd_repl {p q : ℕ} (w : Fin q → ℂ) (hw : star w ⬝ᵥ w = 1) :
    IsChannel (fun Y : Matrix (Fin p) (Fin p) ℂ => Y.trace • vecMulVec w (star w)) := by
  refine ⟨p, fun j => Matrix.of fun h j' => w h * if j = j' then 1 else 0, ?_, ?_⟩
  · unfold IsKrausFamily
    ext j1 j2
    simp only [Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply, of_apply, Matrix.one_apply]
    simp only [star_mul', mul_ite, mul_one, mul_zero, ite_mul, zero_mul, apply_ite star, star_one,
      star_zero]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases hj : j1 = j2
    · subst hj; simp only [if_true]
      rw [← hw]; simp [dotProduct, mul_comm]
    · have hj' : ¬ j2 = j1 := fun h => hj h.symm
      simp only [hj, hj', if_false, Finset.sum_const_zero]
  · intro ρ
    ext h h'
    simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply, of_apply,
      Matrix.smul_apply, vecMulVec_apply, Matrix.trace, Matrix.diag, smul_eq_mul, Pi.star_apply]
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, star_mul', apply_ite star, star_one,
      star_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring

theorem x5cd_vv {n : ℕ} (v : Fin n → ℂ) : star v ⬝ᵥ v = ∑ h, star (v h) * v h := rfl

theorem x5cd_row (U : Matrix (Fin b × Fin e) (Fin a) ℂ) (L : Matrix (Fin b) (Fin a) ℂ)
    (v : Fin e → ℂ) (hv : star v ⬝ᵥ v = 1) (hU : ∀ j h x, U (j, h) x = L j x * v h) :
    (∀ X, receiverChannel U X = L * X * Lᴴ) ∧
    (∀ X, complementaryChannel U X = (L * X * Lᴴ).trace • vecMulVec v (star v)) ∧
    Uᴴ * U = Lᴴ * L := by
  have core : ∀ X : Matrix (Fin a) (Fin a) ℂ, ∀ j h k h',
      (U * X * Uᴴ) (j, h) (k, h') = (L * X * Lᴴ) j k * (v h * star (v h')) := by
    intro X j h k h'
    simp only [Matrix.mul_apply, conjTranspose_apply, hU, star_mul', Finset.sum_mul]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring
  rw [x5cd_vv] at hv
  refine ⟨fun X => ?_, fun X => ?_, ?_⟩
  · ext j k
    simp only [receiverChannel, traceRight, of_apply, core, ← Finset.mul_sum]
    rw [show (∑ h, v h * star (v h)) = 1 by rw [← hv]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _,
      mul_one]
  · ext h h'
    simp only [complementaryChannel, traceLeft, of_apply, core, Matrix.smul_apply, smul_eq_mul,
      vecMulVec_apply, Matrix.trace, Matrix.diag, Finset.sum_mul, Pi.star_apply]
  · ext x y
    simp only [Matrix.mul_apply, conjTranspose_apply, hU, star_mul', Fintype.sum_prod_type]
    rw [← mul_one (∑ j, star (L j x) * L j y), ← hv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ => by ring

theorem x5cd_col (U : Matrix (Fin b × Fin e) (Fin a) ℂ) (R : Matrix (Fin e) (Fin a) ℂ)
    (u : Fin b → ℂ) (hu : star u ⬝ᵥ u = 1) (hU : ∀ j h x, U (j, h) x = u j * R h x) :
    (∀ X, receiverChannel U X = (R * X * Rᴴ).trace • vecMulVec u (star u)) ∧
    (∀ X, complementaryChannel U X = R * X * Rᴴ) ∧
    Uᴴ * U = Rᴴ * R := by
  have core : ∀ X : Matrix (Fin a) (Fin a) ℂ, ∀ j h k h',
      (U * X * Uᴴ) (j, h) (k, h') = (R * X * Rᴴ) h h' * (u j * star (u k)) := by
    intro X j h k h'
    simp only [Matrix.mul_apply, conjTranspose_apply, hU, star_mul', Finset.sum_mul]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring
  rw [x5cd_vv] at hu
  refine ⟨fun X => ?_, fun X => ?_, ?_⟩
  · ext j k
    simp only [receiverChannel, traceRight, of_apply, core, Matrix.smul_apply, smul_eq_mul,
      vecMulVec_apply, Matrix.trace, Matrix.diag, Finset.sum_mul, Pi.star_apply]
  · ext h h'
    simp only [complementaryChannel, traceLeft, of_apply, core, ← Finset.mul_sum]
    rw [show (∑ j, u j * star (u j)) = 1 by rw [← hu]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _,
      mul_one]
  · ext x y
    simp only [Matrix.mul_apply, conjTranspose_apply, hU, star_mul', Fintype.sum_prod_type]
    rw [Finset.sum_comm, ← mul_one (∑ h, star (R h x) * R h y), ← hu, Finset.sum_mul]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

theorem x5cd_unit' {n : ℕ} (ψ : EuclideanSpace ℂ (Fin n))
    (h : star (ψ : Fin n → ℂ) ⬝ᵥ (ψ : Fin n → ℂ) = 1) : ‖ψ‖ = 1 := by
  have h1 : (inner ℂ ψ ψ : ℂ) = 1 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]; exact h
  rw [inner_self_eq_norm_sq_to_K] at h1
  have h2 : ‖ψ‖ ^ 2 = 1 := by
    have h3 := congrArg Complex.re h1
    simpa [← Complex.ofReal_pow] using h3
  have := norm_nonneg ψ
  nlinarith [sq_nonneg (‖ψ‖ - 1), sq_nonneg (‖ψ‖ + 1)]

theorem x5cd_ne_of_unit {n : ℕ} (v : Fin n → ℂ) (h : star v ⬝ᵥ v = 1) : v ≠ 0 := by
  rintro rfl; simp at h

theorem x5cd_rank_pos {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (W : Matrix m n ℂ) (hW : W ≠ 0) : 1 ≤ W.rank := by
  by_contra hc
  have h0 : W.rank = 0 := by omega
  rw [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h0
  apply hW
  ext i x
  have := congrArg (fun f => f (Pi.single x 1) i) h0
  simpa [Matrix.mulVec_single_one] using this

theorem x5cd_classify (ha : 0<a) (hb : 0<b) (he : 0<e)
    (U : Matrix (Fin b × Fin e) (Fin a) ℂ) (hU : Uᴴ * U = 1)
    (hpure : ∀ psi : EuclideanSpace ℂ (Fin a), ‖psi‖ = 1 →
      ∃ phi : EuclideanSpace ℂ (Fin b), ‖phi‖ = 1 ∧
        receiverChannel U (pureDensity psi) = pureDensity phi) :
    (a≤b ∧ (∃ V : Matrix (Fin b) (Fin a) ℂ, Vᴴ * V = 1 ∧
      ∀ X, receiverChannel U X = V * X * Vᴴ) ∧
      (outputFirstChoi (receiverChannel U)).rank = 1 ∧ ConjugateDegradable U) ∨
    (∃ phi : EuclideanSpace ℂ (Fin b), ‖phi‖ = 1 ∧
      (∀ X, receiverChannel U X = X.trace • pureDensity phi) ∧ ConjugateAntidegradable U) := by
  set x0 : Fin a := ⟨0, ha⟩
  have hsingle : ∀ x : Fin a, ‖EuclideanSpace.single x (1 : ℂ)‖ = 1 := by
    intro x; simp
  choose φ hφ1 hφf using fun x => x5cd_pure_fact U hpure _ (hsingle x)
  set χ : Fin a → Fin e → ℂ := fun x => star (φ x) ᵥ* x5cdM U (EuclideanSpace.single x 1)
    with hχdef
  have hA : ∀ x, x5cdM U (EuclideanSpace.single x 1) = vecMulVec (φ x) (χ x) := hφf
  have hUf : ∀ j h x, U (j, h) x = φ x j * χ x h := by
    intro j h x
    have := congrFun (congrFun (hA x) j) h
    rw [x5cd_M_single] at this
    simpa [vecMulVec_apply] using this
  have hχ1 : ∀ x, star (χ x) ⬝ᵥ χ x = 1 := by
    intro x
    have h1 := congrFun (congrFun hU x) x
    simp only [Matrix.mul_apply, conjTranspose_apply, Matrix.one_apply_eq, Fintype.sum_prod_type,
      hUf, star_mul'] at h1
    rw [← h1, x5cd_vv]
    have h2 := hφ1 x
    rw [x5cd_vv] at h2
    rw [← one_mul (∑ h, star (χ x h) * χ x h), ← h2, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ => by ring
  have hpair : ∀ x y, x5cdPar (φ x) (φ y) ∨ x5cdPar (χ x) (χ y) := by
    intro x y
    apply x5cd_cross
    rw [← hA, ← hA, ← x5cd_M_add]
    exact x5cd_R1_all U hpure _
  rcases x5cd_global φ χ (fun x => x5cd_ne_of_unit _ (hφ1 x)) (fun x => x5cd_ne_of_unit _ (hχ1 x))
    hpair with hpar | hpar
  · -- common column: replacement channel
    right
    set u := φ x0
    set R : Matrix (Fin e) (Fin a) ℂ := Matrix.of fun h x => (star u ⬝ᵥ φ x) * χ x h
    have hUc : ∀ j h x, U (j, h) x = u j * R h x := by
      intro j h x
      rw [hUf, x5cd_par_proj (hφ1 x0) (hpar x0 x) j]
      simp only [R, of_apply]; ring
    obtain ⟨r1, r2, r3⟩ := x5cd_col U R u (hφ1 x0) hUc
    have hRR : Rᴴ * R = 1 := r3 ▸ hU
    have htr : ∀ X : Matrix (Fin a) (Fin a) ℂ, (R * X * Rᴴ).trace = X.trace := by
      intro X
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hRR, Matrix.one_mul]
    refine ⟨WithLp.toLp 2 u, x5cd_unit' _ (by simpa using hφ1 x0), fun X => ?_, hU, ?_⟩
    · rw [r1, htr]
      congr 1
    · refine ⟨fun Y => Y.trace • vecMulVec (star u) (star (star u)),
        x5cd_repl (star u) (by rw [star_star, dotProduct_comm]; exact hφ1 x0), fun X => ?_⟩
      simp only [r1, r2, transpose_smul, transpose_vecMulVec, star_star]
  · -- common row: isometric channel
    left
    set v := χ x0
    set L : Matrix (Fin b) (Fin a) ℂ := Matrix.of fun j x => φ x j * (star v ⬝ᵥ χ x)
    have hUr : ∀ j h x, U (j, h) x = L j x * v h := by
      intro j h x
      rw [hUf, x5cd_par_proj (hχ1 x0) (hpar x0 x) h]
      simp only [L, of_apply]; ring
    obtain ⟨r1, r2, r3⟩ := x5cd_row U L v (hχ1 x0) hUr
    have hLL : Lᴴ * L = 1 := r3 ▸ hU
    refine ⟨?_, ⟨L, hLL, r1⟩, ?_, hU, ?_⟩
    · have h1 : (Lᴴ * L).rank ≤ L.rank := Matrix.rank_mul_le_right _ _
      have h2 : L.rank ≤ b := by simpa using Matrix.rank_le_card_height L
      rw [hLL, Matrix.rank_one] at h1
      simp at h1
      omega
    · rw [x5cd_choi, rank_self_mul_conjTranspose]
      have hW : x5cdV U = vecMulVec (fun p : Fin b × Fin a => L p.1 p.2) v := by
        ext p h; simp [x5cdV, vecMulVec_apply, hUr]
      apply le_antisymm
      · rw [hW]; exact Matrix.rank_vecMulVec_le _ _
      · apply x5cd_rank_pos
        intro h0
        have : U = 0 := by
          ext p x
          have := congrFun (congrFun h0 (p.1, x)) p.2
          simpa [x5cdV] using this
        rw [this, conjTranspose_zero, Matrix.zero_mul] at hU
        have := congrFun (congrFun hU x0) x0
        simp at this
    · refine ⟨fun Y => Y.trace • vecMulVec (star v) (star (star v)),
        x5cd_repl (star v) (by rw [star_star, dotProduct_comm]; exact hχ1 x0), fun X => ?_⟩
      simp only [r1, r2, transpose_smul, transpose_vecMulVec, star_star]

end QAlgorithms.Papers.Independent.Support50.P01

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P01

open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel IsDegradable dilationPower maximumCoherentInformation)
open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)
open Matrix

variable {a b e : ℕ}

theorem x5cd_kerincl (U : Matrix (Fin b × Fin e) (Fin a) ℂ) (hU : ConjugateDegradable U)
    (m : ℕ) (psi : Fin m → EuclideanSpace ℂ (Fin a))
    (hspan : (⨆ j, LinearMap.range (receiverChannel U (pureDensity (psi j))).mulVecLin) = ⊤)
    (w : Fin e → ℂ) (h1 : ∀ j, (x5cdM U (psi j)) *ᵥ w = 0) :
    ((x5cdV U)ᴴ * x5cdV U) *ᵥ w = 0 := by
  obtain ⟨-, D, ⟨k, K, -, hDK⟩, hD⟩ := hU
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
  rw [← x5cd_compI, ← hD 1, hDK]
  simp only [krausApply, sum_mulVec]
  exact Finset.sum_eq_zero fun i _ => by rw [← mulVec_mulVec, h2 i, mulVec_zero]

theorem x5cd_rank_mono {n : ℕ} {p q : Type*} [Fintype p] [Fintype q]
    (A : Matrix p (Fin n) ℂ) (B : Matrix q (Fin n) ℂ)
    (h : ∀ w, A *ᵥ w = 0 → B *ᵥ w = 0) : B.rank ≤ A.rank := by
  have hA := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hB := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
  have hk : LinearMap.ker A.mulVecLin ≤ LinearMap.ker B.mulVecLin := by
    intro w hw; simp only [LinearMap.mem_ker, mulVecLin_apply] at hw ⊢; exact h w hw
  have := Submodule.finrank_mono hk
  rw [Matrix.rank, Matrix.rank]
  omega

/-- If one pure output has full support, the Choi rank is at most its rank. -/
theorem x5cd_choi_le (U : Matrix (Fin b × Fin e) (Fin a) ℂ) (hU : ConjugateDegradable U)
    (ψ : EuclideanSpace ℂ (Fin a))
    (hfull : LinearMap.range (receiverChannel U (pureDensity ψ)).mulVecLin = ⊤) :
    (outputFirstChoi (receiverChannel U)).rank ≤ (receiverChannel U (pureDensity ψ)).rank := by
  rw [x5cd_choi, rank_self_mul_conjTranspose, ← rank_conjTranspose_mul_self, x5cd_recv,
    rank_self_mul_conjTranspose]
  apply x5cd_rank_mono
  intro w hw
  exact x5cd_kerincl U hU 1 (fun _ => ψ) (by rw [iSup_const]; exact hfull) w (fun _ => hw)

theorem x5cd_struct (ha : 0 < a) (U : Matrix (Fin b × Fin e) (Fin a) ℂ) (hU : Uᴴ * U = 1)
    (hR1 : ∀ ψ : EuclideanSpace ℂ (Fin a), x5cdR1 (x5cdM U ψ))
    (hfac : ∀ x : Fin a, ∃ φ : Fin b → ℂ, star φ ⬝ᵥ φ = 1 ∧
      x5cdM U (EuclideanSpace.single x 1) =
        vecMulVec φ (star φ ᵥ* x5cdM U (EuclideanSpace.single x 1))) :
    (∃ (L : Matrix (Fin b) (Fin a) ℂ) (v : Fin e → ℂ), star v ⬝ᵥ v = 1 ∧
      ∀ j h x, U (j, h) x = L j x * v h) ∨
    (∃ (u : Fin b → ℂ) (R : Matrix (Fin e) (Fin a) ℂ), star u ⬝ᵥ u = 1 ∧
      ∀ j h x, U (j, h) x = u j * R h x) := by
  set x0 : Fin a := ⟨0, ha⟩
  choose φ hφ1 hφf using hfac
  set χ : Fin a → Fin e → ℂ := fun x => star (φ x) ᵥ* x5cdM U (EuclideanSpace.single x 1)
    with hχdef
  have hA : ∀ x, x5cdM U (EuclideanSpace.single x 1) = vecMulVec (φ x) (χ x) := hφf
  have hUf : ∀ j h x, U (j, h) x = φ x j * χ x h := by
    intro j h x
    have := congrFun (congrFun (hA x) j) h
    rw [x5cd_M_single] at this
    simpa [vecMulVec_apply] using this
  have hχ1 : ∀ x, star (χ x) ⬝ᵥ χ x = 1 := by
    intro x
    have h1 := congrFun (congrFun hU x) x
    simp only [Matrix.mul_apply, conjTranspose_apply, Matrix.one_apply_eq, Fintype.sum_prod_type,
      hUf, star_mul'] at h1
    rw [← h1, x5cd_vv]
    have h2 := hφ1 x
    rw [x5cd_vv] at h2
    rw [← one_mul (∑ h, star (χ x h) * χ x h), ← h2, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ => by ring
  have hpair : ∀ x y, x5cdPar (φ x) (φ y) ∨ x5cdPar (χ x) (χ y) := by
    intro x y
    apply x5cd_cross
    rw [← hA, ← hA, ← x5cd_M_add]
    exact hR1 _
  rcases x5cd_global φ χ (fun x => x5cd_ne_of_unit _ (hφ1 x)) (fun x => x5cd_ne_of_unit _ (hχ1 x))
    hpair with hpar | hpar
  · right
    refine ⟨φ x0, Matrix.of fun h x => (star (φ x0) ⬝ᵥ φ x) * χ x h, hφ1 x0, fun j h x => ?_⟩
    rw [hUf, x5cd_par_proj (hφ1 x0) (hpar x0 x) j]
    simp only [of_apply]; ring
  · left
    refine ⟨Matrix.of fun j x => φ x j * (star (χ x0) ⬝ᵥ χ x), χ x0, hχ1 x0, fun j h x => ?_⟩
    rw [hUf, x5cd_par_proj (hχ1 x0) (hpar x0 x) h]
    simp only [of_apply]; ring

theorem x5cd_rank1_fact {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) (h : M.rank ≤ 1) :
    ∃ (g : Fin m → ℂ) (c : Fin n → ℂ), M = vecMulVec g c := by
  rw [Matrix.rank, finrank_le_one_iff] at h
  obtain ⟨g, hg⟩ := h
  choose c hc using fun k : Fin n => hg ⟨M *ᵥ Pi.single k 1, LinearMap.mem_range_self _ _⟩
  refine ⟨(g : Fin m → ℂ), c, ?_⟩
  ext i k
  have := congrArg (fun z : LinearMap.range M.mulVecLin => (z : Fin m → ℂ) i) (hc k)
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mulVec_single_one] at this
  have h2 : M i k = c k * (g : Fin m → ℂ) i := by rw [this]; rfl
  rw [vecMulVec_apply, h2, mul_comm]

/-- rank ≤ 1 and nonzero gives a unit-vector factorization. -/
theorem x5cd_rank1_unit {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) (h : M.rank ≤ 1) (hM : M ≠ 0) :
    ∃ φ : Fin m → ℂ, star φ ⬝ᵥ φ = 1 ∧ M = vecMulVec φ (star φ ᵥ* M) := by
  obtain ⟨g, c, rfl⟩ := x5cd_rank1_fact M h
  set G : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 g
  have hG0 : G ≠ 0 := by
    intro h0; apply hM
    have : g = 0 := by
      have := congrArg (fun z : EuclideanSpace ℂ (Fin m) => (z : Fin m → ℂ)) h0
      simpa [G] using this
    rw [this]; ext; simp [vecMulVec_apply]
  have hn : ‖G‖ ≠ 0 := norm_ne_zero_iff.mpr hG0
  set Φ : EuclideanSpace ℂ (Fin m) := ((‖G‖⁻¹ : ℝ) : ℂ) • G
  have hΦ : ‖Φ‖ = 1 := by rw [norm_smul]; simp [hn]
  have hΦ1 := x5cd_unit Φ hΦ
  refine ⟨Φ, hΦ1, ?_⟩
  have hg : g = ((‖G‖ : ℝ) : ℂ) • (Φ : Fin m → ℂ) := by
    funext i
    simp only [Φ, G, PiLp.smul_apply, Pi.smul_apply, smul_eq_mul, WithLp.ofLp_smul]
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hn]; simp
  rw [vecMul_vecMulVec, hg, dotProduct_smul, hΦ1]
  ext i k; simp [vecMulVec_apply]; ring

end QAlgorithms.Papers.Independent.Support50.P01

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P01

open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel IsDegradable dilationPower maximumCoherentInformation)
open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)
open Matrix

variable {a e : ℕ}

theorem x5cd_col_ne (U : Matrix (Fin 2 × Fin e) (Fin a) ℂ) (hU : Uᴴ * U = 1) (x : Fin a) :
    x5cdM U (EuclideanSpace.single x 1) ≠ 0 := by
  intro h0
  rw [x5cd_M_single] at h0
  have h1 := congrFun (congrFun hU x) x
  simp only [Matrix.mul_apply, conjTranspose_apply, Matrix.one_apply_eq] at h1
  have : ∀ p : Fin 2 × Fin e, U p x = 0 := fun p => by
    have := congrFun (congrFun h0 p.1) p.2; simpa using this
  simp [this] at h1

theorem x5cd_t4_choi (ha : 0 < a) (U : Matrix (Fin 2 × Fin e) (Fin a) ℂ)
    (hU : ConjugateDegradable U) : (outputFirstChoi (receiverChannel U)).rank ≤ 2 := by
  have hiso := hU.1
  by_cases hA : ∃ ψ : EuclideanSpace ℂ (Fin a), (receiverChannel U (pureDensity ψ)).rank = 2
  · obtain ⟨ψ, hψ⟩ := hA
    have hfull : LinearMap.range (receiverChannel U (pureDensity ψ)).mulVecLin = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [Module.finrank_fin_fun]; exact hψ
    exact (x5cd_choi_le U hU ψ hfull).trans hψ.le
  · push_neg at hA
    have hr1 : ∀ ψ, (x5cdM U ψ).rank ≤ 1 := by
      intro ψ
      have h1 := hA ψ
      rw [x5cd_recv, rank_self_mul_conjTranspose] at h1
      have h2 : (x5cdM U ψ).rank ≤ 2 := by simpa using Matrix.rank_le_card_height (x5cdM U ψ)
      omega
    have hR1 : ∀ ψ, x5cdR1 (x5cdM U ψ) := fun ψ => by
      obtain ⟨g, c, hgc⟩ := x5cd_rank1_fact _ (hr1 ψ); rw [hgc]; exact x5cd_R1_vmv _ _
    have hfac := fun x : Fin a => x5cd_rank1_unit _ (hr1 _) (x5cd_col_ne U hiso x)
    rcases x5cd_struct ha U hiso hR1 hfac with ⟨L, v, hv, hUr⟩ | ⟨u, R, hu, hUc⟩
    · rw [x5cd_choi, rank_self_mul_conjTranspose]
      have hW : x5cdV U = vecMulVec (fun p : Fin 2 × Fin a => L p.1 p.2) v := by
        ext p h; simp [x5cdV, vecMulVec_apply, hUr]
      rw [hW]
      exact (Matrix.rank_vecMulVec_le _ _).trans (by norm_num)
    · obtain ⟨r1, r2, r3⟩ := x5cd_col U R u hu hUc
      have hRR : Rᴴ * R = 1 := r3 ▸ hiso
      have ha1 : a ≤ 1 := by
        by_contra hc
        push_neg at hc
        set x0 : Fin a := ⟨0, ha⟩
        set x1 : Fin a := ⟨1, hc⟩
        have hx : x0 ≠ x1 := by simp [x0, x1, Fin.ext_iff]
        set X : Matrix (Fin a) (Fin a) ℂ := Matrix.single x0 x1 1
        obtain ⟨-, D, ⟨k, K, -, hDK⟩, hD⟩ := hU
        have htr : (R * X * Rᴴ).trace = 0 := by
          rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hRR, Matrix.one_mul]
          exact Matrix.trace_single_eq_of_ne x0 x1 (1 : ℂ) hx
        have h1 := hD X
        rw [r1, r2, htr, zero_smul, hDK] at h1
        have h2 : R * X * Rᴴ = 0 := by
          have : krausApply K (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by simp [krausApply]
          rw [this] at h1
          rw [← transpose_transpose (R * X * Rᴴ), ← h1, transpose_zero]
        have h3 : X = 0 := by
          have : Rᴴ * (R * X * Rᴴ) * R = X := by
            simp only [← Matrix.mul_assoc, hRR, Matrix.one_mul]
            rw [Matrix.mul_assoc, hRR, Matrix.mul_one]
          rw [← this, h2]; simp
        have := congrFun (congrFun h3 x0) x1
        simp [X] at this
      have := Matrix.rank_le_card_height (outputFirstChoi (receiverChannel U))
      simp only [Fintype.card_prod, Fintype.card_fin] at this
      nlinarith

theorem x5cd_par_Y {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (s t : Fin n → ℂ)
    (hs : (s ⬝ᵥ star s) • Y = vecMulVec (star s) s)
    (ht : (t ⬝ᵥ star t) • Y = vecMulVec (star t) t) : x5cdPar s t := by
  by_cases hs0 : s = 0
  · subst hs0; intro i j; simp
  by_cases ht0 : t = 0
  · subst ht0; intro i j; simp
  have hns : s ⬝ᵥ star s ≠ 0 := by
    rw [dotProduct_comm]; exact fun h => hs0 (dotProduct_star_self_eq_zero.mp h)
  have hnt : t ⬝ᵥ star t ≠ 0 := by
    rw [dotProduct_comm]; exact fun h => ht0 (dotProduct_star_self_eq_zero.mp h)
  obtain ⟨h, hh⟩ : ∃ h, s h ≠ 0 := by
    by_contra hc; push_neg at hc; exact hs0 (funext hc)
  have E : ∀ i, (t ⬝ᵥ star t) * (star (s h) * s i) = (s ⬝ᵥ star s) * (star (t h) * t i) := by
    intro i
    have e1 := congrFun (congrFun hs h) i
    have e2 := congrFun (congrFun ht h) i
    simp only [Matrix.smul_apply, smul_eq_mul, vecMulVec_apply, Pi.star_apply] at e1 e2
    rw [← e1, ← e2]; ring
  intro i j
  have hc : (t ⬝ᵥ star t) * star (s h) * (s i * t j - s j * t i) = 0 := by
    linear_combination t j * E i - t i * E j
  have hne : (t ⬝ᵥ star t) * star (s h) ≠ 0 := mul_ne_zero hnt (star_ne_zero.mpr hh)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hc).resolve_left hne)

theorem x5cd_par_finrank {n : ℕ} (S : Submodule ℂ (Fin n → ℂ))
    (h : ∀ s ∈ S, ∀ t ∈ S, x5cdPar s t) : Module.finrank ℂ S ≤ 1 := by
  by_cases hS : ∃ s ∈ S, s ≠ 0
  · obtain ⟨s, hsS, hs0⟩ := hS
    obtain ⟨k, hk⟩ : ∃ k, s k ≠ 0 := by
      by_contra hc; push_neg at hc; exact hs0 (funext hc)
    rw [finrank_le_one_iff]
    refine ⟨⟨s, hsS⟩, fun w => ⟨(w : Fin n → ℂ) k / s k, ?_⟩⟩
    ext i
    simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul]
    have := h s hsS w w.2 i k
    field_simp
    linear_combination this
  · push_neg at hS
    have : S = ⊥ := (Submodule.eq_bot_iff S).mpr hS
    subst this; simp

theorem x5cd_t4_dim (U : Matrix (Fin 2 × Fin e) (Fin a) ℂ) (hU : ConjugateDegradable U)
    (hr : (outputFirstChoi (receiverChannel U)).rank ≤ 2) : a ≤ 3 := by
  have hiso := hU.1
  obtain ⟨-, D, ⟨k, K, -, hDK⟩, hD⟩ := hU
  set U0 : Matrix (Fin e) (Fin a) ℂ := Matrix.of fun h x => U (0, h) x
  set U1 : Matrix (Fin e) (Fin a) ℂ := Matrix.of fun h x => U (1, h) x
  -- (1) rank U1 ≤ 2
  have hV : (x5cdV U).rank ≤ 2 := by
    rwa [x5cd_choi, rank_self_mul_conjTranspose] at hr
  have hU1 : U1.rank ≤ 2 := by
    rw [← Matrix.rank_transpose]
    refine le_trans (x5cd_rank_mono (x5cdV U) U1ᵀ fun w hw => ?_) hV
    funext x
    have := congrFun hw (1, x)
    simpa [mulVec, dotProduct, x5cdV, U1] using this
  -- (2) kernel of U1 is large
  have hrn := LinearMap.finrank_range_add_finrank_ker U1.mulVecLin
  rw [Module.finrank_fin_fun] at hrn
  have hU1' : Module.finrank ℂ (LinearMap.range U1.mulVecLin) ≤ 2 := hU1
  -- (3) U0 is injective on ker U1
  set f := U0.mulVecLin.comp (LinearMap.ker U1.mulVecLin).subtype
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨ψ, hψ⟩ h0
    simp only [LinearMap.mem_ker, mulVecLin_apply] at hψ
    have h0' : U0 *ᵥ ψ = 0 := by simpa [f] using h0
    have hUψ : U *ᵥ ψ = 0 := by
      funext p
      obtain ⟨j, h⟩ := p
      fin_cases j
      · have := congrFun h0' h; simpa [mulVec, dotProduct, U0] using this
      · have := congrFun hψ h; simpa [mulVec, dotProduct, U1] using this
    have : ψ = 0 := by
      rw [← Matrix.one_mulVec ψ, ← hiso, ← Matrix.mulVec_mulVec, hUψ, mulVec_zero]
    simp [this]
  have hfr := LinearMap.finrank_range_of_inj hf
  -- (4) all of range f is pairwise parallel
  set E0 : Fin 2 → ℂ := Pi.single 0 1
  set Y := D (vecMulVec E0 (star E0))
  have hDlin : ∀ (c : ℂ) (Z : Matrix (Fin 2) (Fin 2) ℂ), D (c • Z) = c • D Z := by
    intro c Z
    rw [hDK, hDK]
    simp only [krausApply, Finset.smul_sum, Matrix.mul_smul, Matrix.smul_mul]
  have hkey : ∀ ψ ∈ LinearMap.ker U1.mulVecLin,
      ((U0 *ᵥ ψ) ⬝ᵥ star (U0 *ᵥ ψ)) • Y = vecMulVec (star (U0 *ᵥ ψ)) (U0 *ᵥ ψ) := by
    intro ψ hψ
    simp only [LinearMap.mem_ker, mulVecLin_apply] at hψ
    set s := U0 *ᵥ ψ
    have hM : x5cdM U (WithLp.toLp 2 ψ) = vecMulVec E0 s := by
      ext j h
      fin_cases j
      · simp [x5cdM, E0, s, vecMulVec_apply, mulVec, dotProduct, U0]
      · have := congrFun hψ h
        simp [mulVec, dotProduct, U1] at this
        simp [x5cdM, E0, vecMulVec_apply, this]
    have h1 := hD (pureDensity (WithLp.toLp 2 ψ))
    rw [x5cd_recv, x5cd_comp, transpose_transpose, hM, conjTranspose_vecMulVec,
      vecMulVec_mul_vecMulVec, vecMulVec_mul_vecMulVec] at h1
    have hE : star E0 ⬝ᵥ E0 = 1 := by simp [E0, dotProduct]
    rw [hE, one_smul] at h1
    rw [← h1, ← hDlin]
    congr 1
    ext i j; simp [vecMulVec_apply]; ring
  have hpar : ∀ s ∈ LinearMap.range f, ∀ t ∈ LinearMap.range f, x5cdPar s t := by
    rintro _ ⟨⟨ψ, hψ⟩, rfl⟩ _ ⟨⟨φ, hφ⟩, rfl⟩
    exact x5cd_par_Y Y _ _ (hkey ψ hψ) (hkey φ hφ)
  have := x5cd_par_finrank _ hpar
  omega

end QAlgorithms.Papers.Independent.Support50.P01

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P01
open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel IsDegradable dilationPower maximumCoherentInformation)
open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)
open scoped Matrix ComplexConjugate ComplexOrder

theorem solution {a : ℕ} {e : ℕ} (ha : 0<a) (he : 0<e)
    (U : Matrix (Fin 2 × Fin e) (Fin a) ℂ) (hU : ConjugateDegradable U) :
    (outputFirstChoi (receiverChannel U)).rank ≤ 2 ∧ a≤3 :=
  ⟨x5cd_t4_choi ha U hU, x5cd_t4_dim U hU (x5cd_t4_choi ha U hU)⟩
