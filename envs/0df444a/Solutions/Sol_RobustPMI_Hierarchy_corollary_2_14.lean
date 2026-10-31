-- Prove2me | solution 1 for RobustPMI.Hierarchy.corollary_2_14
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T00:04:59.581195+00:00
-- url     : https://prove2.me/submissions/adc8f054-037f-4c95-b0f2-d579655f6dbc

import Mathlib
import Definitions.Def_RobustPMI_Hierarchy_Model

set_option linter.unusedSectionVars false

namespace RobustPMI.Hierarchy.C214aux
open MvPolynomial Matrix RobustPMI.Hierarchy

section Basic
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- moments of the Dirac measure at `y`. -/
noncomputable def dirac (y : σ → ℝ) : (σ →₀ ℕ) → ℝ := fun α => eval y (monomial α (1 : ℝ))

lemma Hs_eq_of_subset (v : (σ →₀ ℕ) → ℝ) (h : MvPolynomial σ ℝ) (B : Finset (σ →₀ ℕ))
    (hB : h.support ⊆ B) : Hs v h = ∑ α ∈ B, coeff α h * v α := by
  unfold Hs
  refine Finset.sum_subset hB ?_
  intro α _ hα
  rw [notMem_support_iff.mp hα, zero_mul]

lemma Hs_dirac (y : σ → ℝ) (h : MvPolynomial σ ℝ) : Hs (dirac y) h = eval y h := by
  conv_rhs => rw [h.as_sum]
  rw [map_sum]
  unfold Hs dirac
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [show monomial α (coeff α h) = C (coeff α h) * monomial α 1 by
    rw [C_mul_monomial, mul_one]]
  rw [map_mul, eval_C]

lemma dirac_add (y : σ → ℝ) (α β : σ →₀ ℕ) : dirac y (α + β) = dirac y α * dirac y β := by
  unfold dirac
  rw [← map_mul, monomial_mul, one_mul]

end Basic

lemma mem_suppMat {σ ι R : Type*} [CommSemiring R] [DecidableEq σ] [Fintype ι]
    (F : Matrix ι ι (MvPolynomial σ R)) (α : σ →₀ ℕ) (i j : ι) (h : α ∈ (F i j).support) :
    α ∈ suppMat F :=
  Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_univ _, h⟩


variable {n m q : ℕ}

lemma moments_apply {G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)} (μ : AtomicMeasure m G)
    (α : Fin n →₀ ℕ) (a b : Fin m) :
    μ.moments α a b = ∑ i, dirac (μ.pts i) α * μ.W i a b := by
  simp [AtomicMeasure.moments, Matrix.sum_apply, dirac]

lemma moments_symm {G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)} (μ : AtomicMeasure m G)
    (α : Fin n →₀ ℕ) : (μ.moments α).IsSymm := by
  ext a b
  rw [transpose_apply, moments_apply, moments_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := (μ.psd i).isHermitian
  have : μ.W i b a = μ.W i a b := by
    have := congrFun (congrFun h a) b
    simpa [conjTranspose_apply] using this
  rw [this]

lemma momentMat_atomic_psd {G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)}
    (μ : AtomicMeasure m G) (k : ℕ) : (momentMat k μ.moments).PosSemidef := by
  classical
  set B : Fin μ.r → Matrix (Fin m) ((monos (σ := Fin n) k) × Fin m) ℝ := fun i =>
    Matrix.of fun c p => if p.2 = c then dirac (μ.pts i) p.1.1 else 0
  have key : momentMat k μ.moments = ∑ i, (B i)ᴴ * μ.W i * B i := by
    ext p p'
    simp only [momentMat, of_apply, moments_apply, Matrix.sum_apply, dirac_add, mul_apply,
      conjTranspose_apply, star_trivial, B, ite_mul, zero_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [key]
  exact posSemidef_sum _ fun i _ => (μ.psd i).conjTranspose_mul_mul_same (B i)

lemma locMat_atomic_psd {G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)}
    (μ : AtomicMeasure m G) (d : ℕ) : (locMat d G μ.moments).PosSemidef := by
  classical
  set B : Fin μ.r → Matrix (Fin m × Fin q) ((monos (σ := Fin n) d) × (Fin m × Fin q)) ℝ :=
    fun i => Matrix.of fun e p => if p.2 = e then dirac (μ.pts i) p.1.1 else 0
  have key : locMat d G μ.moments =
      ∑ i, (B i)ᴴ * (kroneckerMap (· * ·) (μ.W i) (G.map (eval (μ.pts i)))) * B i := by
    ext p p'
    have e : ∀ (i : Fin μ.r) (c c' : Fin q),
        ∑ γ ∈ suppMat G, dirac (μ.pts i) (p.1.1 + p'.1.1 + γ) * coeff γ (G c c') =
        dirac (μ.pts i) p.1.1 * dirac (μ.pts i) p'.1.1 * eval (μ.pts i) (G c c') := by
      intro i c c'
      rw [← Hs_dirac, Hs_eq_of_subset _ _ (suppMat G) (fun γ hγ => mem_suppMat G γ c c' hγ),
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun γ _ => ?_
      rw [dirac_add, dirac_add]; ring
    simp only [locMat, of_apply, moments_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [Matrix.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e' := e i p.2.2 p'.2.2
    simp only [mul_assoc, ← Finset.mul_sum] at e' ⊢
    rw [show ∑ γ ∈ suppMat G, dirac (μ.pts i) (p.1.1 + p'.1.1 + γ) *
        (μ.W i p.2.1 p'.2.1 * coeff γ (G p.2.2 p'.2.2)) =
        μ.W i p.2.1 p'.2.1 * ∑ γ ∈ suppMat G, dirac (μ.pts i) (p.1.1 + p'.1.1 + γ) *
          coeff γ (G p.2.2 p'.2.2) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun γ _ => by ring]
    rw [e']
    simp only [mul_apply, conjTranspose_apply, star_trivial, B, of_apply, ite_mul, zero_mul,
      mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      kroneckerMap_apply, map_apply]
    ring
  rw [key]
  exact posSemidef_sum _ fun i _ =>
    ((μ.psd i).kronecker (μ.mem i)).conjTranspose_mul_mul_same (B i)

end RobustPMI.Hierarchy.C214aux

open RobustPMI.Hierarchy RobustPMI.Hierarchy.C214aux in
theorem solution {n m q : ℕ} (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ))
    (μ : AtomicMeasure m G) : μ.moments ∈ MMall G :=
  fun k _ => ⟨fun α _ => moments_symm μ α, momentMat_atomic_psd μ k,
    locMat_atomic_psd μ (k - dG G)⟩
