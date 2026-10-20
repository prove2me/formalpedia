-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P48.privateInformationDominates
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T02:46:29.601885+00:00
-- url     : https://prove2.me/submissions/08dc0237-ac1e-4cd3-9542-d6a26bb981b3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P48

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P48

open scoped BigOperators Matrix ComplexConjugate

open scoped ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P67 (dilationPower)

attribute [local instance] Classical.propDecidable

variable {P Q E X H : Type*}

variable [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]

variable [Fintype E] [DecidableEq E] [Fintype X] [DecidableEq X]

variable [Fintype H] [DecidableEq H]


/-- rank-one matrix of a vector -/
lemma g53c_proj_sq {I : Type*} [Fintype I] (w : I → ℂ) (hw : ∑ i, conj (w i) * w i = 1) :
    (Matrix.of fun a b => w a * conj (w b)) * (Matrix.of fun a b => w a * conj (w b)) =
      Matrix.of fun a b => w a * conj (w b) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.of_apply]
  have : ∑ x, w a * conj (w x) * (w x * conj (w b)) = w a * conj (w b) * ∑ x, conj (w x) * w x := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => ?_; ring
  rw [this, hw, mul_one]

lemma g53c_proj_herm {I : Type*} [Fintype I] (w : I → ℂ) :
    (Matrix.of fun a b => w a * conj (w b))ᴴ = Matrix.of fun a b => w a * conj (w b) := by
  ext a b
  simp [Matrix.conjTranspose_apply, mul_comm]

lemma g53c_proj_sqrt {I : Type*} [Fintype I] [DecidableEq I] (w : I → ℂ)
    (hw : ∑ i, conj (w i) * w i = 1) :
    cfc Real.sqrt (Matrix.of fun a b => w a * conj (w b)) = Matrix.of fun a b => w a * conj (w b) := by
  set M : Matrix I I ℂ := Matrix.of fun a b => w a * conj (w b) with hM
  have hsa : IsSelfAdjoint M := g53c_proj_herm w
  have h0 : cfc (fun x : ℝ => x * x) M = cfc (fun x : ℝ => x) M := by
    rw [cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) M, cfc_id' ℝ M, g53c_proj_sq w hw]
  have h1 := eqOn_of_cfc_eq_cfc h0
  conv_rhs => rw [← cfc_id' ℝ M]
  apply cfc_congr
  intro x hx
  have hx2 : x * x = x := h1 hx
  have : x = 0 ∨ x = 1 := by
    have : x * (x - 1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · left; exact h
    · right; linarith
  rcases this with rfl | rfl <;> simp

/-- the kronecker map by a projector as a non-unital star algebra hom -/
def g53c_kronHom {R I : Type*} [Fintype R] [Fintype I] [DecidableEq R] [DecidableEq I]
    (Pc : Matrix R R ℂ) (hsq : Pc * Pc = Pc) (hh : Pcᴴ = Pc) :
    Matrix I I ℂ →⋆ₙₐ[ℂ] Matrix (R × I) (R × I) ℂ where
  toFun Y := Matrix.kronecker Pc Y
  map_smul' c Y := by
    simp only [MonoidHom.id_apply]
    exact Matrix.kronecker_smul c Pc Y
  map_zero' := Matrix.kronecker_zero _
  map_add' Y Z := Matrix.kronecker_add Pc Y Z
  map_mul' Y Z := by
    show Matrix.kronecker Pc (Y * Z) = Matrix.kronecker Pc Y * Matrix.kronecker Pc Z
    have := Matrix.mul_kronecker_mul Pc Pc Y Z
    rw [hsq] at this
    exact this
  map_star' Y := by
    have hpc : ∀ a c, Pc a c = star (Pc c a) := fun a c => by
      have := congrFun (congrFun hh a) c
      rw [Matrix.conjTranspose_apply] at this
      exact this.symm
    ext ⟨a, b⟩ ⟨c, d⟩
    show Pc a c * (star Y) b d = star (Pc c a * Y d b)
    rw [Matrix.star_apply, star_mul', hpc a c]

lemma g53c_entropy_kron {R I : Type*} [Fintype R] [Fintype I] [DecidableEq R] [DecidableEq I]
    (Pc : Matrix R R ℂ) (hsq : Pc * Pc = Pc) (hh : Pcᴴ = Pc) (htr : Pc.trace = 1)
    (sigma : Matrix I I ℂ) (hs : sigma.IsHermitian) :
    vnEntropy (Matrix.kronecker Pc sigma) = vnEntropy sigma := by
  have hcont : Continuous (fun x : ℝ => x * Real.logb 2 x) := by
    have : (fun x : ℝ => x * Real.logb 2 x) = fun x => (x * Real.log x) / Real.log 2 := by
      funext x; rw [Real.logb]; ring
    rw [this]; exact Real.continuous_mul_log.div_const _
  have hsa : IsSelfAdjoint sigma := hs
  let φ := g53c_kronHom (I := I) Pc hsq hh
  have hφ : Continuous φ := by
    show Continuous fun Y : Matrix I I ℂ => Matrix.kronecker Pc Y
    exact continuous_pi fun i => continuous_pi fun j =>
      continuous_const.mul ((continuous_apply j.2).comp (continuous_apply i.2))
  have hφa : IsSelfAdjoint (φ sigma) := by
    show star (φ sigma) = φ sigma
    rw [← map_star, hsa.star_eq]
  have key := NonUnitalStarAlgHom.map_cfcₙ φ (fun x : ℝ => x * Real.logb 2 x) sigma
    hcont.continuousOn (by simp) hφ hsa hφa
  rw [cfcₙ_eq_cfc hcont.continuousOn (by simp), cfcₙ_eq_cfc hcont.continuousOn (by simp)] at key
  unfold vnEntropy
  have : φ sigma = Matrix.kronecker Pc sigma := rfl
  rw [← this, ← key]
  show -(Matrix.kronecker Pc (cfc (fun x : ℝ => x * Real.logb 2 x) sigma)).trace.re = _
  erw [Matrix.trace_kronecker]
  rw [htr, one_mul]


lemma g53c_receiver_smul (U : Matrix (Q × E) P ℂ) (c : ℂ) (M : Matrix P P ℂ) :
    receiver U (c • M) = c • receiver U M := by
  unfold receiver
  rw [Matrix.mul_smul, Matrix.smul_mul]
  ext a b
  simp [traceRight, Finset.mul_sum]

lemma g53c_receiver_herm (U : Matrix (Q × E) P ℂ) (M : Matrix P P ℂ) (hM : M.IsHermitian) :
    (receiver U M).IsHermitian := by
  have h2 : (U * M * Uᴴ).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hM.eq,
      Matrix.mul_assoc]
  unfold receiver
  ext a b
  have : ∀ x y, star ((U * M * Uᴴ) y x) = (U * M * Uᴴ) x y := by
    intro x y
    have := congrFun (congrFun h2 x) y
    rw [Matrix.conjTranspose_apply] at this
    exact this
  simp only [Matrix.conjTranspose_apply, traceRight, Matrix.of_apply, star_sum, this]

lemma g53c_coh_pure (U : Matrix (Q × E) P ℂ) (w : P → ℂ) (hw : ∑ i, conj (w i) * w i = 1) :
    coherentInformation (receiver U) (Matrix.of fun a b => w a * conj (w b)) = 0 := by
  set rho : Matrix P P ℂ := Matrix.of fun a b => w a * conj (w b) with hrho
  set w' : P → ℂ := fun i => conj (w i) with hw'
  have hw'1 : ∑ i, conj (w' i) * w' i = 1 := by
    rw [← hw]; refine Finset.sum_congr rfl fun i _ => ?_; simp [hw', mul_comm]
  set Pc : Matrix P P ℂ := Matrix.of fun a b => w' a * conj (w' b) with hPc
  have htr : Pc.trace = 1 := by
    rw [← hw'1]; simp only [Matrix.trace, Matrix.diag, hPc, Matrix.of_apply]
    refine Finset.sum_congr rfl fun i _ => ?_; ring
  have hrh : rho.IsHermitian := g53c_proj_herm w
  have hsq := g53c_proj_sqrt w hw
  have hT : idTensorSuperop (R := P) (receiver U)
      (pureDensity (QAlgorithms.Papers.Independent.Information100.P22.densityPurification rho)) =
      Matrix.kronecker Pc (receiver U rho) := by
    ext p q
    have hblock : (Matrix.of fun i i' =>
        pureDensity (QAlgorithms.Papers.Independent.Information100.P22.densityPurification rho)
          (p.1, i) (q.1, i')) = (conj (w p.1) * w q.1) • rho := by
      ext i i'
      simp only [pureDensity, QAlgorithms.Papers.Independent.Information100.P22.densityPurification,
        hsq, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, hrho, map_mul, Complex.conj_conj]
      ring
    simp only [idTensorSuperop, Matrix.of_apply, hblock, g53c_receiver_smul, Matrix.smul_apply,
      smul_eq_mul, hPc, hw', Complex.conj_conj]
    rfl
  unfold QAlgorithms.Papers.Independent.Information100.P22.coherentInformation
  rw [hT, g53c_entropy_kron Pc (g53c_proj_sq w' hw'1) (g53c_proj_herm w') htr _
    (g53c_receiver_herm U rho hrh), sub_self]

/-- Inequality after (31), PDF p.9. Pure decomposition and vanishing component
coherent information are proved content, not assumptions of this statement. -/
theorem solution [Nonempty P] [Nonempty Q] [Nonempty E]
    (U : Matrix (Q × E) P ℂ) (hU : IsDilation U)
    (rho : Matrix P P ℂ) (hrho : IsDensityMatrix rho) :
    coherentInformation (receiver U) rho ≤ privateInformation U rho := by
  unfold privateInformation
  suffices h : sInf (coherentDecompositionCosts U rho) ≤ 0 by linarith
  have hH : rho.IsHermitian := hrho.1.1
  let e := Fintype.equivFin P
  let v : P → EuclideanSpace ℂ P := fun k => hH.eigenvectorBasis k
  have hv : ∀ k, ∑ i, conj (v k i) * v k i = 1 := by
    intro k
    have h1 : ‖v k‖ = 1 := hH.eigenvectorBasis.orthonormal.1 k
    have h2 : inner ℂ (v k) (v k) = 1 := by
      rw [inner_self_eq_norm_sq_to_K, h1]; simp
    rw [← h2, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RCLike.inner_apply, mul_comm]
  have hden : ∀ k, IsDensityMatrix (pureDensity (v k)) := by
    intro k
    have hpd : pureDensity (v k) = Matrix.vecMulVec (v k) (star (v k)) := by
      ext a b; simp [pureDensity, Matrix.vecMulVec_apply]
    refine ⟨?_, ?_⟩
    · rw [hpd]; exact Matrix.posSemidef_vecMulVec_self_star _
    · rw [← hv k]; simp only [Matrix.trace, Matrix.diag, pureDensity, Matrix.of_apply]
      refine Finset.sum_congr rfl fun i _ => ?_; ring
  have hsum : ∑ j, hH.eigenvalues (e.symm j) = 1 := by
    rw [Equiv.sum_comp e.symm (fun k => hH.eigenvalues k)]
    have := hH.trace_eq_sum_eigenvalues
    rw [hrho.2] at this
    have h3 := congrArg Complex.re this
    simp only [Complex.one_re, Complex.re_sum, Complex.ofReal_re] at h3
    exact h3.symm
  let D : Decomposition P :=
    { size := Fintype.card P
      positive := Fintype.card_pos
      probability := fun j => hH.eigenvalues (e.symm j)
      nonnegative := fun j => hrho.1.eigenvalues_nonneg _
      normalized := hsum
      state := fun j => pureDensity (v (e.symm j))
      density := fun j => hden _ }
  have havg : D.average = rho := by
    show ∑ j, ((hH.eigenvalues (e.symm j) : ℝ) : ℂ) • pureDensity (v (e.symm j)) = rho
    rw [Equiv.sum_comp e.symm (fun k => ((hH.eigenvalues k : ℝ) : ℂ) • pureDensity (v k))]
    conv_rhs => rw [hH.spectral_theorem]
    ext a b
    simp only [Unitary.conjStarAlgAut_apply, Matrix.sum_apply, Matrix.smul_apply, pureDensity, Matrix.of_apply,
      smul_eq_mul, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply,
      Matrix.IsHermitian.eigenvectorUnitary_apply, Function.comp_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [v, RCLike.star_def]
    rw [mul_assoc]; exact mul_left_comm _ _ _
  have hmem : (0 : ℝ) ∈ coherentDecompositionCosts U rho := by
    refine ⟨D, havg, ?_⟩
    symm
    apply Finset.sum_eq_zero
    intro j _
    show hH.eigenvalues (e.symm j) * coherentInformation (receiver U) (pureDensity (v (e.symm j))) = 0
    rw [show pureDensity (v (e.symm j)) = Matrix.of fun a b => v (e.symm j) a * conj (v (e.symm j) b)
      from rfl, g53c_coh_pure U _ (hv _), mul_zero]
  by_cases hb : BddBelow (coherentDecompositionCosts U rho)
  · exact csInf_le hb hmem
  · rw [Real.sInf_of_not_bddBelow hb]


end

