-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P43.commonMarginalRealization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T04:49:53.951806+00:00
-- url     : https://prove2.me/submissions/7878f01f-95ce-4031-8517-9e18319b8492

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P43


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


/-! X6: every bipartite density with first marginal `s` is obtained from one fixed
purification of `s` by a channel on the second factor. -/

open scoped Matrix ComplexConjugate ComplexOrder
set_option linter.unusedSectionVars false
noncomputable section
namespace X6CM
open Matrix QAlgorithms

variable {A : Type} [Fintype A] [DecidableEq A]

lemma sqrt_herm {n : Type*} [Fintype n] [DecidableEq n] (ρ : Matrix n n ℂ) : (cfc Real.sqrt ρ)ᴴ = cfc Real.sqrt ρ := by
  have : IsSelfAdjoint (cfc Real.sqrt ρ) := cfc_predicate _ _
  exact this

lemma sqrt_sq {n : Type*} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) :
    cfc Real.sqrt ρ * (cfc Real.sqrt ρ)ᴴ = ρ := by
  open scoped MatrixOrder in
  have h0 : (0 : Matrix n n ℂ) ≤ ρ := Matrix.nonneg_iff_posSemidef.mpr hρ
  rw [sqrt_herm, ← cfc_mul Real.sqrt Real.sqrt ρ]
  conv_rhs => rw [← cfc_id ℝ ρ]
  open scoped MatrixOrder in
  exact cfc_congr fun x hx => Real.mul_self_sqrt (spectrum_nonneg_of_nonneg h0 hx)

/-- the purification vector of `S Sᴴ`. -/
def vec (S : Matrix A A ℂ) : EuclideanSpace ℂ (A × A) := WithLp.toLp 2 fun p => S p.1 p.2

lemma vec_marg (S : Matrix A A ℂ) : traceRight (pureDensity (vec S)) = S * Sᴴ := by
  ext a a'
  simp [traceRight, pureDensity, vec, mul_apply, conjTranspose_apply]

theorem realize [Nonempty A] (S : Matrix A A ℂ) (ρ : Matrix (A × A) (A × A) ℂ)
    (hρ : ρ.PosSemidef) (hm : traceRight ρ = S * Sᴴ) :
    ∃ (m : ℕ) (F : Fin m → Matrix A A ℂ), IsKrausFamily F ∧
      ρ = idTensorSuperop (krausApply F) (pureDensity (vec S)) := by
  set W : Matrix (A × A) (A × A) ℂ := cfc Real.sqrt ρ with hW
  have hρW : ρ = W * Wᴴ := (sqrt_sq hρ).symm
  let k0 : A × A := Classical.arbitrary _
  let X : Matrix A (A × (A × A)) ℂ := of fun a p => W (a, p.1) p.2
  let Y : Matrix A (A × (A × A)) ℂ := of fun a p => if p.2 = k0 then S a p.1 else 0
  have hX : X * Xᴴ = S * Sᴴ := by
    rw [← hm, hρW]
    ext a a'
    simp [X, traceRight, mul_apply, conjTranspose_apply, Fintype.sum_prod_type]
  have hY : Y * Yᴴ = S * Sᴴ := by
    ext a a'
    simp [Y, mul_apply, conjTranspose_apply, Fintype.sum_prod_type]
  obtain ⟨U, hU, hXY⟩ := X6GU.gram_unitary X Y (by rw [hX, hY])
  have hU' : U * Uᴴ = 1 := mul_eq_one_comm.1 hU
  -- Kraus operators indexed by `A × A`
  let G : (A × A) → Matrix A A ℂ := fun k => of fun b c => U (c, k0) (b, k)
  have hXe : ∀ a b k, W (a, b) k = ∑ c, S a c * U (c, k0) (b, k) := by
    intro a b k
    have := congrFun (congrFun hXY a) (b, k)
    simp only [X, Y, of_apply, mul_apply, Fintype.sum_prod_type, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    exact this
  have hG : ∑ k, (G k)ᴴ * G k = 1 := by
    ext c c'
    have h1 := congrFun (congrFun hU' (c', k0)) (c, k0)
    rw [mul_apply, Fintype.sum_prod_type] at h1
    simp only [conjTranspose_apply] at h1
    simp only [Matrix.sum_apply, mul_apply, conjTranspose_apply, G, of_apply]
    rw [Finset.sum_comm]
    have e1 : (1 : Matrix (A × (A × A)) (A × (A × A)) ℂ) (c', k0) (c, k0) = (1 : Matrix A A ℂ) c c' := by
      by_cases h : c = c'
      · subst h; simp
      · rw [one_apply_ne (by simpa [eq_comm] using h), one_apply_ne h]
    rw [← e1, ← h1]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _
  let e := Fintype.equivFin (A × A)
  refine ⟨Fintype.card (A × A), fun j => G (e.symm j), ?_, ?_⟩
  · show ∑ j, (G (e.symm j))ᴴ * G (e.symm j) = 1
    rw [Equiv.sum_comp e.symm (fun k => (G k)ᴴ * G k), hG]
  ext p q
  rw [hρW]
  simp only [idTensorSuperop, krausApply, of_apply, Matrix.sum_apply, mul_apply, conjTranspose_apply]
  rw [Equiv.sum_comp e.symm (fun k => ∑ x, (∑ x_1, G k p.2 x_1 *
    pureDensity (vec S) (p.1, x_1) (q.1, x)) * star (G k q.2 x))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hXe, hXe, star_sum, Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
  simp only [G, of_apply, pureDensity, vec, star_mul', RCLike.star_def]
  ring

theorem cmr {I : Type*} [Nonempty A] (s : Matrix A A ℂ) (hs : IsDensityMatrix s)
    (rho : I → Matrix (A × A) (A × A) ℂ) (hrho : ∀ i, IsDensityMatrix (rho i))
    (hmarg : ∀ i, traceRight (rho i) = s) :
    ∃ psi : EuclideanSpace ℂ (A × A), ‖psi‖ = 1 ∧ traceRight (pureDensity psi) = s ∧
      ∃ E : I → Superop A A, ∀ i, IsChannel (E i) ∧
        rho i = idTensorSuperop (E i) (pureDensity psi) := by
  set S := cfc Real.sqrt s
  have hS : S * Sᴴ = s := sqrt_sq hs.1
  have hr : ∀ i, ∃ (m : ℕ) (F : Fin m → Matrix A A ℂ), IsKrausFamily F ∧
      rho i = idTensorSuperop (krausApply F) (pureDensity (vec S)) := fun i =>
    realize S (rho i) (hrho i).1 (by rw [hmarg, hS])
  choose m F hF hρ using hr
  refine ⟨vec S, ?_, by rw [vec_marg, hS], fun i => krausApply (F i), fun i =>
    ⟨⟨m i, F i, hF i, fun _ => rfl⟩, hρ i⟩⟩
  have htr : trace (pureDensity (vec S)) = 1 := by
    rw [← hs.2, ← hS, ← vec_marg]
    simp [trace, traceRight, Fintype.sum_prod_type]
  have h2 := EuclideanSpace.norm_sq_eq (vec S)
  have h3 : ∑ p, ‖vec S p‖ ^ 2 = 1 := by
    have := congrArg Complex.re htr
    simp only [trace, diag_apply, pureDensity, of_apply, Complex.mul_conj, Complex.re_sum,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq] at this
    simpa using this
  rw [h3] at h2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2

end X6CM


noncomputable section

open scoped Matrix ComplexConjugate

open Filter

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P43

open QAlgorithms.Papers.Independent.Dependency50.P45

attribute [local instance] Classical.propDecidable

theorem solution {A : Type} {I : Type*} [Fintype A]
    [DecidableEq A] [Nonempty A] (s : Matrix A A ℂ) (hs : IsDensityMatrix s)
    (rho : I → Matrix (A × A) (A × A) ℂ) (hrho : ∀ i, IsDensityMatrix (rho i))
    (hmarg : ∀ i, traceRight (rho i) = s) :
    ∃ psi : EuclideanSpace ℂ (A × A), ‖psi‖ = 1 ∧ traceRight (pureDensity psi) = s ∧
      ∃ E : I → Superop A A, ∀ i, IsChannel (E i) ∧
        rho i = idTensorSuperop (E i) (pureDensity psi) :=
  X6CM.cmr s hs rho hrho hmarg
