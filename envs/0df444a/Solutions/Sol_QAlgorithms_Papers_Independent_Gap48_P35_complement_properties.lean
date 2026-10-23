-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P35.complement_properties
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T04:16:26.809954+00:00
-- url     : https://prove2.me/submissions/4c9ed81b-e226-428d-adf3-bd2f51323d81

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P35


/-! X6: two matrices with the same Gram matrix `X Xᴴ = Y Yᴴ` differ by a unitary on the right. -/

open scoped Matrix ComplexConjugate InnerProductSpace
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6GU
open Matrix

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

lemma nsq (X : Matrix m n ℂ) (u : m → ℂ) :
    star (Xᴴ *ᵥ u) ⬝ᵥ (Xᴴ *ᵥ u) = star u ⬝ᵥ ((X * Xᴴ) *ᵥ u) := by
  rw [star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec, mulVec_mulVec]

lemma norm_sq_eq_dot (v : EuclideanSpace ℂ n) : (‖v‖ ^ 2 : ℝ) = (star (v : n → ℂ) ⬝ᵥ (v : n → ℂ)).re := by
  rw [EuclideanSpace.norm_sq_eq, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.star_apply, Complex.star_def]
  rw [mul_comm, Complex.mul_conj']; norm_cast

theorem gram_unitary (X Y : Matrix m n ℂ) (h : X * Xᴴ = Y * Yᴴ) :
    ∃ U : Matrix n n ℂ, Uᴴ * U = 1 ∧ X = Y * U := by
  let TX : EuclideanSpace ℂ m →ₗ[ℂ] EuclideanSpace ℂ n := toEuclideanLin Xᴴ
  let TY : EuclideanSpace ℂ m →ₗ[ℂ] EuclideanSpace ℂ n := toEuclideanLin Yᴴ
  have hTX : ∀ u, (TX u : n → ℂ) = Xᴴ *ᵥ (u : m → ℂ) := fun u => rfl
  have hTY : ∀ u, (TY u : n → ℂ) = Yᴴ *ᵥ (u : m → ℂ) := fun u => rfl
  have hn : ∀ u, ‖TX u‖ = ‖TY u‖ := fun u => by
    have h1 := norm_sq_eq_dot (TX u)
    have h2 := norm_sq_eq_dot (TY u)
    rw [hTX, nsq, h] at h1
    rw [hTY, nsq] at h2
    have : ‖TX u‖ ^ 2 = ‖TY u‖ ^ 2 := by rw [h1, h2]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this
  have hker : LinearMap.ker TY ≤ LinearMap.ker TX := fun u hu => by
    rw [LinearMap.mem_ker] at hu ⊢
    rw [← norm_eq_zero, hn, hu, norm_zero]
  let L0 : LinearMap.range TY →ₗ[ℂ] EuclideanSpace ℂ n :=
    (Submodule.liftQ _ TX hker).comp (TY.quotKerEquivRange.symm : _ →ₗ[ℂ] _)
  have hL0 : ∀ u, L0 ⟨TY u, LinearMap.mem_range_self _ _⟩ = TX u := fun u => by
    simp only [L0, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  let L : LinearMap.range TY →ₗᵢ[ℂ] EuclideanSpace ℂ n :=
    { L0 with
      norm_map' := by
        rintro ⟨_, u, rfl⟩
        change ‖L0 ⟨TY u, _⟩‖ = _
        rw [hL0, hn]; rfl }
  let G := L.extend
  have hG : ∀ u, G (TY u) = TX u := fun u => by
    have := LinearIsometry.extend_apply L ⟨TY u, LinearMap.mem_range_self _ _⟩
    exact this.trans (hL0 u)
  let Gm : Matrix n n ℂ := Matrix.of fun i j => (G (EuclideanSpace.single j 1)) i
  have hGv : ∀ v : EuclideanSpace ℂ n, ∀ i, (G v) i = ∑ j, Gm i j * v j := fun v i => by
    have hv : v = ∑ j, v j • EuclideanSpace.single j (1 : ℂ) := by
      ext k; simp [Pi.single_apply]
    conv_lhs => rw [hv]
    rw [map_sum]
    simp only [map_smul, PiLp.smul_apply, smul_eq_mul, Gm, of_apply]
    rw [WithLp.ofLp_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [mul_comm]
  have h1 : Gm * Yᴴ = Xᴴ := by
    ext i k
    have := congrArg (fun w : EuclideanSpace ℂ n => w i) (hG (EuclideanSpace.single k 1))
    simp only at this
    rw [hGv, hTX] at this
    have e : ∀ j, (TY (EuclideanSpace.single k 1)) j = Yᴴ j k := fun j => by
      rw [hTY]; simp [mulVec, dotProduct, PiLp.single_apply]
    simp only [e] at this
    rw [Matrix.mul_apply, this]
    simp [mulVec, dotProduct, PiLp.single_apply]
  have h2 : Gmᴴ * Gm = 1 := by
    ext j j'
    have := G.inner_map_map (EuclideanSpace.single j 1) (EuclideanSpace.single j' 1)
    rw [EuclideanSpace.inner_single_left] at this
    simp only [map_one, one_mul, PiLp.single_apply] at this
    rw [Matrix.mul_apply, Matrix.one_apply]
    have e : ⟪G (EuclideanSpace.single j 1), G (EuclideanSpace.single j' 1)⟫_ℂ =
        ∑ i, conj (Gm i j) * Gm i j' := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [dotProduct, Gm, mul_comm]
    rw [e] at this
    simp only [conjTranspose_apply, Complex.star_def]
    rw [this]
  refine ⟨Gmᴴ, ?_, ?_⟩
  · rw [conjTranspose_conjTranspose]; exact mul_eq_one_comm.1 h2
  · have := congrArg conjTranspose h1
    rw [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_conjTranspose] at this
    exact this.symm

end X6GU


open scoped Matrix ComplexConjugate ComplexOrder Kronecker
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6CP
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Gap48.P35
open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)
open QAlgorithms.Papers.Independent.Dependency50.P19 (marginalRA marginalRB)

variable {A B C : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]

lemma mRA (v : EuclideanSpace ℂ (A × (B × C))) (a a' : A) (b b' : B) :
    marginalRA (pureDensity v) (a, b) (a', b') = ∑ c, v (a, (b, c)) * conj (v (a', (b', c))) := by
  simp [marginalRA, idTensorSuperop, traceRight, pureDensity]

lemma mRB (v : EuclideanSpace ℂ (A × (B × C))) (a a' : A) (c c' : C) :
    marginalRB (pureDensity v) (a, c) (a', c') = ∑ b, v (a, (b, c)) * conj (v (a', (b, c'))) := by
  simp [marginalRB, idTensorSuperop, traceLeft, pureDensity]

lemma swap_comp (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix (A × C) (A × C) ℂ)
    (h : BComplement rho sigma) : BComplement sigma rho := by
  obtain ⟨omega, ⟨v, hv, rfl⟩, h1, h2⟩ := h
  let e : A × (C × B) ≃ A × (B × C) :=
    Equiv.prodCongr (Equiv.refl A) (Equiv.prodComm C B)
  let v' : EuclideanSpace ℂ (A × (C × B)) := WithLp.toLp 2 fun x => v (e x)
  refine ⟨pureDensity v', ⟨v', ?_, rfl⟩, ?_, ?_⟩
  · rw [← hv, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    exact Fintype.sum_equiv e _ _ (fun x => rfl)
  · rw [← h2]; ext ⟨a, c⟩ ⟨a', c'⟩
    rw [mRA, mRB]; rfl
  · rw [← h1]; ext ⟨a, b⟩ ⟨a', b'⟩
    rw [mRA, mRB]; rfl

lemma uniq (rho : Matrix (A × B) (A × B) ℂ) (sigma sigma2 : Matrix (A × C) (A × C) ℂ)
    (h : BComplement rho sigma) (h2 : BComplement rho sigma2) :
    ∃ U : Matrix.unitaryGroup C ℂ,
      sigma = Matrix.kronecker (1 : Matrix A A ℂ) (U : Matrix C C ℂ) * sigma2 *
        (Matrix.kronecker (1 : Matrix A A ℂ) (U : Matrix C C ℂ))ᴴ := by
  obtain ⟨omega, ⟨v, -, rfl⟩, h1, rfl⟩ := h
  obtain ⟨omega2, ⟨w, -, rfl⟩, h3, rfl⟩ := h2
  let V : Matrix (A × B) C ℂ := Matrix.of fun p c => v (p.1, (p.2, c))
  let W : Matrix (A × B) C ℂ := Matrix.of fun p c => w (p.1, (p.2, c))
  have hVV : V * Vᴴ = W * Wᴴ := by
    ext ⟨a, b⟩ ⟨a', b'⟩
    have e1 := mRA v a a' b b'
    have e2 := mRA w a a' b b'
    rw [h1] at e1; rw [h3] at e2
    simp only [V, W, Matrix.mul_apply, conjTranspose_apply, of_apply, Complex.star_def]
    rw [← e1, ← e2]
  obtain ⟨U', hU', hVW⟩ := X6GU.gram_unitary V W hVV
  have hU'' : U' * U'ᴴ = 1 := mul_eq_one_comm.1 hU'
  have hv : ∀ a b c, v (a, (b, c)) = ∑ d, w (a, (b, d)) * U' d c := fun a b c => by
    have := congrFun (congrFun hVW (a, b)) c
    simpa [V, W, Matrix.mul_apply] using this
  have hU : U'ᵀ ∈ Matrix.unitaryGroup C ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    change (U'ᵀ)ᴴ * U'ᵀ = 1
    rw [conjTranspose_transpose_eq_transpose_conjTranspose, ← transpose_mul, hU'', transpose_one]
  refine ⟨⟨U'ᵀ, hU⟩, ?_⟩
  ext ⟨a, c⟩ ⟨a', c'⟩
  rw [mRB]
  simp only [hv]
  simp only [Matrix.mul_apply, conjTranspose_apply, kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, transpose_apply, mRB, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, star_mul', star_one, kronecker_apply, star_zero, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Complex.star_def]
  simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  simp only [Matrix.kronecker, kroneckerMap_apply, Matrix.one_apply, transpose_apply, ite_mul,
    one_mul, zero_mul, map_one, map_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp only [apply_ite (starRingEnd ℂ), map_zero, mul_ite, mul_zero, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

end X6CP


open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Gap48.P35
open Information100.P21 (Op)
open Information100.P08 (IsPure formation measuredCorrelation)
open Dependency50.P19 (marginalRA marginalRB)

noncomputable section

theorem solution {A : Type} {B : Type} {C : Type}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B] [Fintype C] [DecidableEq C] [Nonempty C]
    (rho : Op (A × B)) (sigma : Op (A × C))
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    (BComplement rho sigma ↔ BComplement sigma rho) ∧
      (BComplement rho sigma →
        traceRight rho = traceRight sigma ∧
        ∀ sigma2 : Op (A × C), BComplement rho sigma2 →
          ∃ U : Matrix.unitaryGroup C ℂ,
            sigma = Matrix.kronecker (1 : Op A) (U : Op C) * sigma2 *
              (Matrix.kronecker (1 : Op A) (U : Op C))ᴴ) := by
  refine ⟨⟨X6CP.swap_comp rho sigma, X6CP.swap_comp sigma rho⟩, fun h => ⟨?_, fun sigma2 h2 =>
    X6CP.uniq rho sigma sigma2 h h2⟩⟩
  obtain ⟨omega, ⟨v, -, rfl⟩, rfl, rfl⟩ := h
  ext a a'
  simp only [traceRight, Matrix.of_apply, X6CP.mRA, X6CP.mRB]
  exact Finset.sum_comm
