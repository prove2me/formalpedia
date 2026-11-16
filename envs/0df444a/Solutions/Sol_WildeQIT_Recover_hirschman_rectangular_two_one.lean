-- Prove2me | solution 1 for WildeQIT.Recover.hirschman_rectangular_two_one
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-16T01:13:03.448923+00:00
-- url     : https://prove2.me/submissions/bbf7c198-d784-4aeb-9717-c878e3e51ab2

import Theorems.Thm_WildeQIT_Recover_hirschman_two_one
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi

noncomputable section
open Matrix
open QAlgorithms.Papers.Independent.Information100.P50
open scoped ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RecoveryBlockCFC
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def cornerHom : Matrix n n ℂ →⋆ₙₐ[ℂ] Matrix (Sum m n) (Sum m n) ℂ where
  toFun A := fromBlocks 0 0 0 A
  map_zero' := by ext i j; cases i <;> cases j <;> simp
  map_add' := by intro A B; ext i j; cases i <;> cases j <;> simp
  map_mul' := by intro A B; simp [fromBlocks_multiply]
  map_smul' := by intro z A; ext i j; cases i <;> cases j <;> simp
  map_star' := by
    intro A
    change fromBlocks 0 0 0 (star A)=star (fromBlocks 0 0 0 A)
    simp only [Matrix.star_eq_conjTranspose,fromBlocks_conjTranspose,conjTranspose_zero]

lemma cfc_corner (A : Matrix n n ℂ) (hA : IsSelfAdjoint A)
    (f : ℝ → ℝ) (hf : Continuous f) (hf0 : f 0=0) :
    cfc f (fromBlocks (0 : Matrix m m ℂ) 0 0 A) = fromBlocks 0 0 0 (cfc f A) := by
  let φ := cornerHom (m := m) (n := n)
  let L : Matrix n n ℂ →ₗ[ℂ] Matrix (Sum m n) (Sum m n) ℂ :=
    { toFun := φ, map_add' := map_add φ, map_smul' := map_smul φ }
  have hφ : Continuous φ := L.toContinuousLinearMap.continuous
  have hφA : IsSelfAdjoint (φ A) := hA.map φ
  have he := φ.map_cfcₙ f A hf.continuousOn hf0 hφ hA hφA
  simp_rw [cfcₙ_eq_cfc hf.continuousOn hf0] at he
  exact he.symm

def pad (A : Matrix m n ℂ) : Matrix (Sum m n) (Sum m n) ℂ := fromBlocks 0 A 0 0

lemma pad_gram (A : Matrix m n ℂ) : (pad A)ᴴ*pad A=fromBlocks 0 0 0 (Aᴴ*A) := by
  simp [pad,fromBlocks_conjTranspose,fromBlocks_multiply]

lemma trace_cfc_pad_gram (A : Matrix m n ℂ) (f : ℝ → ℝ) (hf : Continuous f) (hf0 : f 0=0) :
    (cfc f ((pad A)ᴴ*pad A)).trace = (cfc f (Aᴴ*A)).trace := by
  rw [pad_gram,cfc_corner _ (posSemidef_conjTranspose_mul_self A).isHermitian f hf hf0]
  simp [Matrix.trace,Matrix.diag,Fintype.sum_sum_type]

lemma schatten_pad (A : Matrix m n ℂ) (p : ℝ) (hp : 0 < p) :
    schattenNorm (ENNReal.ofReal p) (pad A) =
      ((cfc (fun x : ℝ => x^(p/2)) (Aᴴ*A)).trace.re)^(1/p) := by
  rw [QAlgorithms.Papers.Independent.Information100.P50.schattenNorm,if_neg ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le]
  simp only [Real.rpow_eq_pow]
  rw [trace_cfc_pad_gram A (fun x : ℝ => x^(p/2))
    (Real.continuous_rpow_const (by positivity)) (Real.zero_rpow (by positivity))]

end RecoveryBlockCFC

noncomputable section
open Matrix Set Filter MeasureTheory
open QAlgorithms.Papers.Independent.Information100.P50
open QAlgorithms.Papers.Independent.Dependency50.P21
open RecoveryBlockCFC
open scoped Topology ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RecoveryRectInterpolation
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def rSchatten (p : ℝ) (A : Matrix m n ℂ) : ℝ :=
  ((cfc (fun x : ℝ => x^(p/2)) (Aᴴ*A)).trace.re)^(1/p)

def padLM : Matrix m n ℂ →ₗ[ℂ] Matrix (Sum m n) (Sum m n) ℂ where
  toFun := pad
  map_add' := by intro A B; ext i j; cases i <;> cases j <;> simp [pad]
  map_smul' := by intro z A; ext i j; cases i <;> cases j <;> simp [pad]

def padCLM : Matrix m n ℂ →L[ℂ] Matrix (Sum m n) (Sum m n) ℂ := padLM.toContinuousLinearMap

theorem rectangular_two_one (G : ℂ → Matrix m n ℂ)
    (hbounded : Bornology.IsBounded (G '' {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1}))
    (hholomorphic : DifferentiableOn ℂ G {z : ℂ | 0 < z.re ∧ z.re < 1})
    (hcontinuous : ContinuousOn G {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1})
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    extendedLog (rSchatten (2/(1+θ)) (G θ)) ≤ upperLogIntegral (fun t =>
      (alphaDensity θ t : EReal)*extendedLog ((rSchatten 2 (G ((t : ℂ)*Complex.I)))^(1-θ)) +
      (betaDensity θ t : EReal)*extendedLog ((rSchatten 1 (G (1+(t : ℂ)*Complex.I)))^θ)) := by
  have hpadB : Bornology.IsBounded ((fun z => pad (G z)) '' {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1}) := by
    change Bornology.IsBounded (((padCLM (m := m) (n := n)) ∘ G) '' _)
    simpa only [Set.image_image,Function.comp_def] using (padCLM (m := m) (n := n)).lipschitz.isBounded_image hbounded
  have hpadD : DifferentiableOn ℂ (fun z => pad (G z)) {z : ℂ | 0 < z.re ∧ z.re < 1} :=
    (padCLM (m := m) (n := n)).differentiable.comp_differentiableOn hholomorphic
  have hpadC : ContinuousOn (fun z => pad (G z)) {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1} :=
    (padCLM (m := m) (n := n)).continuous.comp_continuousOn hcontinuous
  have hh := WildeQIT.Recover.hirschman_two_one (fun z => pad (G z)) hpadB hpadD hpadC θ hθ0 hθ1
  have hp : 0 < 2/(1+θ) := by positivity
  have hP (z : ℂ) : schattenNorm (ENNReal.ofReal (2/(1+θ))) (pad (G z))=rSchatten (2/(1+θ)) (G z) :=
    schatten_pad (G z) _ hp
  have h2 (z : ℂ) : schattenNorm 2 (pad (G z))=rSchatten 2 (G z) := by
    simpa only [rSchatten,ENNReal.ofReal_ofNat] using schatten_pad (G z) 2 (by norm_num)
  have h1 (z : ℂ) : schattenNorm 1 (pad (G z))=rSchatten 1 (G z) := by
    simpa only [rSchatten,ENNReal.ofReal_one] using schatten_pad (G z) 1 (by norm_num)
  rw [hP] at hh
  simp_rw [h2,h1] at hh
  exact hh

end RecoveryRectInterpolation

set_option autoImplicit false


theorem solution {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (G : ℂ → Matrix m n ℂ)
    (hbounded : Bornology.IsBounded (G '' {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1}))
    (hholomorphic : DifferentiableOn ℂ G {z : ℂ | 0 < z.re ∧ z.re < 1})
    (hcontinuous : ContinuousOn G {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1})
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    let normp : ℝ → Matrix m n ℂ → ℝ := fun p A =>
      ((cfc (fun x : ℝ => x^(p/2)) (Aᴴ*A)).trace.re)^(1/p)
    extendedLog (normp (2/(1+θ)) (G θ)) ≤ upperLogIntegral (fun t =>
      (alphaDensity θ t : EReal)*extendedLog ((normp 2 (G ((t : ℂ)*Complex.I)))^(1-θ)) +
      (betaDensity θ t : EReal)*extendedLog ((normp 1 (G (1+(t : ℂ)*Complex.I)))^θ)) := by
  exact RecoveryRectInterpolation.rectangular_two_one G hbounded hholomorphic hcontinuous θ hθ0 hθ1