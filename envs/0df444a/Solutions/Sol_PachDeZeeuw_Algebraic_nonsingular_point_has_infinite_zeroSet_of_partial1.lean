-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.nonsingular_point_has_infinite_zeroSet_of_partial1
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:43:53.607448+00:00
-- url     : https://prove2.me/submissions/7919354d-3a83-4706-aec8-8ad8b37ddfae

import Mathlib
import Definitions.Def_PdzBezout
import Definitions.Def_PdzPrelim
import Theorems.Thm_PachDeZeeuw_Algebraic_eval_eq_specialized_eval

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve
variable {𝕜 E₁ E₂ F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {f : E₁ × E₂ → F} {f' : E₁ × E₂ →L[𝕜] F} {a : E₁ × E₂} {n : WithTop ℕ∞}

namespace PachDeZeeuw.Algebraic

/-- Near the base point the implicit function satisfies the implicit equation. -/
theorem cdApplyImplicitFunction (hf : ContDiffAt 𝕜 n f a) (hn : n ≠ 0)
    (hinv : ((fderiv 𝕜 f a) ∘L (ContinuousLinearMap.inr 𝕜 E₁ E₂)).IsInvertible) :
    ∀ᶠ x in 𝓝 a.1, f (x, cdImplicitFunction hf hn hinv x) = f a :=
  hf.eventually_apply_implicitFunction hn hinv

/-- Plane polynomial evaluation is smooth. -/
lemma evalPlane_contDiff (p : PlanePoly) :
    ContDiff ℝ ⊤ (evalPlane p) := by
  change ContDiff ℝ ⊤ (fun xy : ℝ × ℝ =>
    MvPolynomial.eval (fun i => if i = 0 then xy.1 else xy.2) p)
  refine MvPolynomial.induction_on
    (motive := fun p => ContDiff ℝ ⊤ (fun xy : ℝ × ℝ =>
      MvPolynomial.eval (fun i => if i = 0 then xy.1 else xy.2) p)) p ?_ ?_ ?_
  · intro a
    simpa [MvPolynomial.eval_C] using
      (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ × ℝ => a))
  · intro p q hp hq
    simpa [MvPolynomial.eval_add] using hp.add hq
  · intro p i hp
    fin_cases i
    · simpa [MvPolynomial.eval_mul, MvPolynomial.eval_X] using hp.mul contDiff_fst
    · simpa [MvPolynomial.eval_mul, MvPolynomial.eval_X] using hp.mul contDiff_snd

/-- `x ↦ x • b` is bijective on `ℝ` when `b ≠ 0`. -/
lemma toSpanSingleton_bijective_of_ne_zero (b : ℝ) (hb : b ≠ 0) :
    Function.Bijective (ContinuousLinearMap.toSpanSingleton ℝ b) := by
  constructor
  · intro x y hxy
    have hxy' : x * b = y * b := by
      simpa [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] using hxy
    exact mul_right_cancel₀ hb hxy'
  · intro y
    refine ⟨y / b, ?_⟩
    simp [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    field_simp [hb]

/-- Currying in the first coordinate turns `pderiv 0` into univariate differentiation. -/
lemma curry0_pderiv0 (p : PlanePoly) :
    Curry0 (MvPolynomial.pderiv (0 : Fin 2) p) = Polynomial.derivative (Curry0 p) := by
  refine MvPolynomial.induction_on
    (motive := fun p =>
      Curry0 (MvPolynomial.pderiv (0 : Fin 2) p) = Polynomial.derivative (Curry0 p)) p ?_ ?_ ?_
  · intro a
    simp [Curry0, MvPolynomial.finSuccEquiv_apply]
  · intro p q hp hq
    simpa [Curry0, map_add] using congrArg₂ (fun a b => a + b) hp hq
  · intro p i hp
    have hp' :
        MvPolynomial.eval₂ (Polynomial.C.comp MvPolynomial.C)
            (fun i ↦ Fin.cases Polynomial.X (fun k ↦ Polynomial.C (MvPolynomial.X k)) i)
            (MvPolynomial.pderiv (0 : Fin 2) p) =
          Polynomial.derivative
            (MvPolynomial.eval₂ (Polynomial.C.comp MvPolynomial.C)
              (fun i ↦ Fin.cases Polynomial.X (fun k ↦ Polynomial.C (MvPolynomial.X k)) i) p) := by
      simpa [Curry0, MvPolynomial.finSuccEquiv_apply] using hp
    fin_cases i
    · simp [Curry0, MvPolynomial.finSuccEquiv_apply, map_add, map_mul,
        MvPolynomial.pderiv_X, Polynomial.derivative_mul]
      rw [hp']
      ring
    · simp [Curry0, MvPolynomial.finSuccEquiv_apply, map_mul,
        MvPolynomial.pderiv_X, Polynomial.derivative_mul]
      rw [hp']
      change Polynomial.C (MvPolynomial.X 0) *
            Polynomial.derivative
              (MvPolynomial.eval₂ (Polynomial.C.comp MvPolynomial.C)
                (fun i ↦ Fin.cases Polynomial.X (fun k ↦ Polynomial.C (MvPolynomial.X k)) i) p) =
          Polynomial.derivative
              (MvPolynomial.eval₂ (Polynomial.C.comp MvPolynomial.C)
                (fun i ↦ Fin.cases Polynomial.X (fun k ↦ Polynomial.C (MvPolynomial.X k)) i) p) *
            Polynomial.C (MvPolynomial.X 0) +
              MvPolynomial.eval₂ (Polynomial.C.comp MvPolynomial.C)
                (fun i ↦ Fin.cases Polynomial.X (fun k ↦ Polynomial.C (MvPolynomial.X k)) i) p *
              Polynomial.derivative (Polynomial.C (MvPolynomial.X 0))
      simp [mul_comm]

omit [CompleteSpace E₁] in
/-- The second-variable partial derivative `f' ∘ inr` is invertible (as a
continuous linear map) given the derivative identity and bijectivity input. -/
theorem hasFDerivAt_isInvertible_partial (hf : HasFDerivAt f f' a)
    (hbij : Function.Bijective (f'.comp (ContinuousLinearMap.inr 𝕜 E₁ E₂))) :
    ((fderiv 𝕜 f a) ∘L (ContinuousLinearMap.inr 𝕜 E₁ E₂)).IsInvertible := by
  have hfderiv : fderiv 𝕜 f a = f' := hf.fderiv
  have hker : (f'.comp (ContinuousLinearMap.inr 𝕜 E₁ E₂)).ker = ⊥ := by
    rw [LinearMap.ker_eq_bot]; exact hbij.1
  have hrange : (f'.comp (ContinuousLinearMap.inr 𝕜 E₁ E₂)).range = ⊤ := by
    rw [LinearMap.range_eq_top]; exact hbij.2
  have hinv : (f'.comp (ContinuousLinearMap.inr 𝕜 E₁ E₂)).IsInvertible :=
    ⟨ContinuousLinearEquiv.ofBijective _ hker hrange,
      ContinuousLinearEquiv.coe_ofBijective _ hker hrange⟩
  rwa [hfderiv]

end PachDeZeeuw.Algebraic

open PachDeZeeuw.Algebraic in
theorem solution (h : PlanePoly) {z : Point2}
    (hz : z ∈ PlaneCurveZeroSet h)
    (hnonsing :
      MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (1 : Fin 2) h) ≠ 0) :
    (PlaneCurveZeroSet h).Infinite := by
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
  let a : ℝ × ℝ := (z 0, z 1)
  have hcoords : (fun i : Fin 2 => if i = 0 then a.1 else a.2) = fun i => z i := by
    funext i
    fin_cases i <;> simp [a]
  have hcont : ContDiffAt ℝ ⊤ (evalPlane h) a := (evalPlane_contDiff h).contDiffAt
  rcases (show ∃ f' : (ℝ × ℝ) →L[ℝ] ℝ, HasFDerivAt (evalPlane h) f' a by
      simpa [DifferentiableAt] using hcont.differentiableAt) with ⟨f', hfd⟩
  let g : ℝ → ℝ := fun y => evalPlane h (a.1, y)
  let hswap : PlanePoly := MvPolynomial.rename (Equiv.swap 0 1) h
  let q : Polynomial ℝ := Specialized0 a.1 hswap
  have hg_eq : g = fun y => Polynomial.eval y q := by
    funext y
    have hslice := eval_eq_specialized_eval hswap (mkPoint2 y a.1)
    have hswapCoords :
        ((fun i => mkPoint2 y a.1 i) ∘ (Equiv.swap 0 1)) =
          (fun i : Fin 2 => if i = 0 then a.1 else y) := by
      funext i
      fin_cases i <;> simp [Function.comp, mkPoint2]
    dsimp [hswap] at hslice
    rw [MvPolynomial.eval_rename] at hslice
    rw [hswapCoords] at hslice
    simpa [g, q, evalPlane, elimCoord, coeffCoord, mkPoint2] using hslice
  have hinr : HasFDerivAt (fun y : ℝ => (a.1, y))
      (ContinuousLinearMap.inr ℝ ℝ ℝ) a.2 := by
    simpa [ContinuousLinearMap.inr] using
      (hasFDerivAt_const a.1 a.2).prodMk (hasFDerivAt_id a.2)
  have hgfd : HasFDerivAt g (f'.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) a.2 := by
    convert hfd.comp a.2 hinr using 1
    funext y
    rfl
  have hq_deriv : Polynomial.derivative q =
      Specialized0 a.1 (MvPolynomial.pderiv (0 : Fin 2) hswap) := by
    unfold q Specialized0
    rw [Polynomial.derivative_map, curry0_pderiv0]
  have hslice_deriv :
      Polynomial.eval a.2 (Polynomial.derivative q) =
        MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (1 : Fin 2) h) := by
    rw [hq_deriv]
    have hslice :=
      eval_eq_specialized_eval (MvPolynomial.pderiv (0 : Fin 2) hswap) (swapPoint z)
    have hrename :
        MvPolynomial.pderiv (0 : Fin 2) hswap =
          MvPolynomial.rename (Equiv.swap 0 1) (MvPolynomial.pderiv (1 : Fin 2) h) := by
      dsimp [hswap]
      simpa using
        (MvPolynomial.pderiv_rename (Equiv.swap 0 1).injective (x := (1 : Fin 2)) (p := h))
    have hswapCoords :
        ((fun i => swapPoint z i) ∘ (Equiv.swap 0 1)) = fun i => z i := by
      funext i
      fin_cases i <;> simp [Function.comp, swapPoint, mkPoint2]
    calc
      Polynomial.eval a.2 (Specialized0 a.1 (MvPolynomial.pderiv (0 : Fin 2) hswap)) =
          MvPolynomial.eval (fun i => swapPoint z i) (MvPolynomial.pderiv (0 : Fin 2) hswap) := by
            simpa [a, swapPoint, mkPoint2, elimCoord, coeffCoord] using hslice.symm
      _ = MvPolynomial.eval ((fun i => swapPoint z i) ∘ (Equiv.swap 0 1))
            (MvPolynomial.pderiv (1 : Fin 2) h) := by
              rw [hrename, MvPolynomial.eval_rename]
      _ = MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (1 : Fin 2) h) := by
            simp [hswapCoords]
  have hpoly : HasFDerivAt g
      (ContinuousLinearMap.toSpanSingleton ℝ (Polynomial.eval a.2 (Polynomial.derivative q))) a.2 := by
    have hq' :
        HasFDerivAt (fun y => Polynomial.eval y q)
          (ContinuousLinearMap.toSpanSingleton ℝ (Polynomial.eval a.2 (Polynomial.derivative q))) a.2 := by
      simpa [Polynomial.aeval_def] using (Polynomial.hasDerivAt_aeval q a.2).hasFDerivAt
    simpa [hg_eq] using hq'
  have hscalar_ne : Polynomial.eval a.2 (Polynomial.derivative q) ≠ 0 := by
    simpa [hslice_deriv] using hnonsing
  have hcomp :
      Function.Bijective (f'.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) := by
    have hcomp_eq :
        f'.comp (ContinuousLinearMap.inr ℝ ℝ ℝ) =
          ContinuousLinearMap.toSpanSingleton ℝ
            (Polynomial.eval a.2 (Polynomial.derivative q)) :=
      HasFDerivAt.unique hgfd hpoly
    simpa [hcomp_eq] using
      toSpanSingleton_bijective_of_ne_zero
        (Polynomial.eval a.2 (Polynomial.derivative q)) hscalar_ne
  have hn : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  have hinv :
      ((fderiv ℝ (evalPlane h) a) ∘L (ContinuousLinearMap.inr ℝ ℝ ℝ)).IsInvertible :=
    hasFDerivAt_isInvertible_partial hfd hcomp
  let ψ : ℝ → ℝ := cdImplicitFunction hcont hn hinv
  have ha : evalPlane h a = 0 := by
    simpa [PlaneCurveZeroSet, evalPlane, hcoords] using hz
  have hevent : ∀ᶠ x in 𝓝 a.1, evalPlane h (x, ψ x) = 0 := by
    simpa [ha, ψ] using cdApplyImplicitFunction hcont hn hinv
  have hnhds : {x | evalPlane h (x, ψ x) = 0} ∈ 𝓝 a.1 := by
    simpa [Filter.Eventually] using hevent
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨ε, hε, hball⟩
  have hball_infinite : (Metric.ball a.1 ε).Infinite := by
    simpa [Real.ball_eq_Ioo] using Set.Ioo_infinite (show a.1 - ε < a.1 + ε by linarith)
  let g : ℝ → Point2 := fun x => mkPoint2 x (ψ x)
  have hg_inj : Set.InjOn g (Metric.ball a.1 ε) := by
    intro x hx y hy hxy
    have h0 := congrArg (fun p : Point2 => p 0) hxy
    simp [g, mkPoint2] at h0
    exact h0
  have hsubset : g '' Metric.ball a.1 ε ⊆ PlaneCurveZeroSet h := by
    intro z' hz'
    rcases hz' with ⟨x, hx, rfl⟩
    have hx' : evalPlane h (x, ψ x) = 0 := hball hx
    change MvPolynomial.eval (fun i => g x i) h = 0
    dsimp [g]
    convert hx' using 1
    show MvPolynomial.eval (fun i => mkPoint2 x (ψ x) i) h =
      MvPolynomial.eval (fun i : Fin 2 => if i = 0 then x else ψ x) h
    apply congrArg (fun f => MvPolynomial.eval f h)
    funext i
    fin_cases i <;> simp [mkPoint2]
  exact Set.Infinite.mono hsubset (Set.Infinite.image hg_inj hball_infinite)
