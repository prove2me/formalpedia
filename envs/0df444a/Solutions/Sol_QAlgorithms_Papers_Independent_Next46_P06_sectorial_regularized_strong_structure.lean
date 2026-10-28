-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P06.sectorial_regularized_strong_structure
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:22:00.282421+00:00
-- url     : https://prove2.me/submissions/cf732e9a-931a-4646-8b8c-4322c98639ed

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P06
noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter

open scoped Topology

set_option linter.unusedSectionVars false

namespace QAlgorithms.Papers.Independent.Next46.P06

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem S200S_mem1 (R S : X →L[ℂ] X) :
    S ∈ operatorCommutant {R} ↔ S.comp R = R.comp S := by
  simp [operatorCommutant]

theorem S200S_bi_sub (R d : X →L[ℂ] X) (hd : d ∈ operatorCommutant (operatorCommutant {R})) :
    d ∈ operatorCommutant {R} := by
  have : R ∈ operatorCommutant {R} := (S200S_mem1 R R).2 rfl
  exact (S200S_mem1 R d).2 (hd R this)

theorem S200S_comm (R d T : X →L[ℂ] X) (hd : d ∈ operatorCommutant (operatorCommutant {R}))
    (hT : T ∈ operatorCommutant {R}) (x : X) : d (T x) = T (d x) := by
  have := hd T hT
  exact congrArg (fun L : X →L[ℂ] X => L x) this

theorem S200S_bi_mul (R d1 d2 : X →L[ℂ] X)
    (h1 : d1 ∈ operatorCommutant (operatorCommutant {R}))
    (h2 : d2 ∈ operatorCommutant (operatorCommutant {R})) :
    d1.comp d2 ∈ operatorCommutant (operatorCommutant {R}) := by
  intro T hT
  rw [ContinuousLinearMap.comp_assoc, h2 T hT, ← ContinuousLinearMap.comp_assoc, h1 T hT,
    ContinuousLinearMap.comp_assoc]

theorem S200S_sub (R : X →L[ℂ] X) : SubalgebraSet (operatorCommutant {R}) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [S200S_mem1]; simp
  · intro f hf g hg
    rw [S200S_mem1] at hf hg
    refine ⟨?_, ?_⟩
    · rw [S200S_mem1, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, hf, hg]
    · rw [S200S_mem1]
      change (f.comp g).comp R = R.comp (f.comp g)
      rw [ContinuousLinearMap.comp_assoc, hg, ← ContinuousLinearMap.comp_assoc, hf,
        ContinuousLinearMap.comp_assoc]
  · intro c f hf
    rw [S200S_mem1] at hf ⊢
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, hf]

/-- product family -/
def S200S_prodSet (D1 D2 : Set (X →L[ℂ] X)) : Set (X →L[ℂ] X) :=
  {d | ∃ d1 ∈ D1, ∃ d2 ∈ D2, d = d1.comp d2}

theorem S200S_prodSet_sub (R : X →L[ℂ] X) (D1 D2 : Set (X →L[ℂ] X))
    (h1 : D1 ⊆ operatorCommutant (operatorCommutant {R}))
    (h2 : D2 ⊆ operatorCommutant (operatorCommutant {R})) :
    S200S_prodSet D1 D2 ⊆ operatorCommutant (operatorCommutant {R}) := by
  rintro d ⟨d1, hd1, d2, hd2, rfl⟩
  exact S200S_bi_mul R d1 d2 (h1 hd1) (h2 hd2)

theorem S200S_prodSet_sep (D1 D2 : Set (X →L[ℂ] X))
    (h1 : OperatorPointSeparating D1) (h2 : OperatorPointSeparating D2) :
    OperatorPointSeparating (S200S_prodSet D1 D2) := by
  intro x hx
  apply h2 x
  intro d2 hd2
  apply h1 (d2 x)
  intro d1 hd1
  exact hx (d1.comp d2) ⟨d1, hd1, d2, hd2, rfl⟩

theorem S200S_bound (d : X →L[ℂ] X) (a : ℕ → X →L[ℂ] X) (f : X →L[ℂ] X)
    (h : ∀ x : X, Tendsto (fun n => d (a n x)) atTop (𝓝 (d (f x)))) :
    ∃ C, ∀ n, ‖d.comp (a n)‖ ≤ C := by
  apply banach_steinhaus
  intro x
  obtain ⟨C, hC⟩ := (h x).norm.bddAbove_range
  exact ⟨C, fun n => hC ⟨n, rfl⟩⟩

theorem S200S_mul_tend (d : X →L[ℂ] X) (a : ℕ → X →L[ℂ] X) (f : X →L[ℂ] X)
    (h : ∀ x : X, Tendsto (fun n => d (a n x)) atTop (𝓝 (d (f x))))
    (y : ℕ → X) (y0 : X) (hy : Tendsto y atTop (𝓝 y0)) :
    Tendsto (fun n => d (a n (y n))) atTop (𝓝 (d (f y0))) := by
  obtain ⟨C, hC⟩ := S200S_bound d a f h
  have hdiff : Tendsto (fun n => d (a n (y n)) - d (a n y0)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hy' : Tendsto (fun n => C * ‖y n - y0‖) atTop (𝓝 0) := by
      have := (tendsto_iff_norm_sub_tendsto_zero.1 hy).const_mul C
      simpa using this
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hy'
    have e : d (a n (y n)) - d (a n y0) = (d.comp (a n)) (y n - y0) := by simp
    rw [e]
    exact ((d.comp (a n)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _))
  have := hdiff.add (h y0)
  simpa using this

theorem S200S_main (R : X →L[ℂ] X) :
    AlgebraicConvergenceOn (regularizedStrong R) (operatorCommutant {R}) ∧
    HausdorffConvergence (regularizedStrong R) := by
  refine ⟨⟨S200S_sub R, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro a f h
    exact ⟨h.1, h.2.1⟩
  · intro f hf
    refine ⟨fun _ => hf, hf, {ContinuousLinearMap.id ℂ X}, ?_, ?_, ?_⟩
    · intro d hd
      rw [Set.mem_singleton_iff] at hd
      subst hd
      intro T _
      simp
    · intro x hx
      simpa using hx _ (Set.mem_singleton _)
    · intro d _ x
      exact tendsto_const_nhds
  · intro a b f g ha hb
    obtain ⟨ha1, hf, D1, hD1, hS1, hT1⟩ := ha
    obtain ⟨hb1, hg, D2, hD2, hS2, hT2⟩ := hb
    have hsub := S200S_sub R
    refine ⟨⟨fun n => (hsub.2.1 _ (ha1 n) _ (hb1 n)).1, (hsub.2.1 _ hf _ hg).1,
      S200S_prodSet D1 D2, S200S_prodSet_sub R D1 D2 hD1 hD2,
      S200S_prodSet_sep D1 D2 hS1 hS2, ?_⟩,
      ⟨fun n => (hsub.2.1 _ (ha1 n) _ (hb1 n)).2, (hsub.2.1 _ hf _ hg).2,
      S200S_prodSet D1 D2, S200S_prodSet_sub R D1 D2 hD1 hD2,
      S200S_prodSet_sep D1 D2 hS1 hS2, ?_⟩⟩
    · rintro d ⟨d1, hd1, d2, hd2, rfl⟩ x
      have e1 : ∀ z : X, (d1.comp d2) z = d2 (d1 z) := by
        intro z
        have := congrArg (fun L : X →L[ℂ] X => L z)
          (hD1 hd1 d2 (S200S_bi_sub R d2 (hD2 hd2)))
        simpa using this
      have t1 : Tendsto (fun n => d2 (d1 (a n x))) atTop (𝓝 (d2 (d1 (f x)))) :=
        ((d2.continuous.tendsto _).comp (hT1 d1 hd1 x))
      have t2 : Tendsto (fun n => d1 (d2 (b n x))) atTop (𝓝 (d1 (d2 (g x)))) :=
        ((d1.continuous.tendsto _).comp (hT2 d2 hd2 x))
      have := t1.add t2
      convert this using 1
      · funext n
        simp only [ContinuousLinearMap.add_apply, map_add]
        rw [e1]; simp
      · simp only [ContinuousLinearMap.add_apply, map_add]
        rw [e1]; simp
    · rintro d ⟨d1, hd1, d2, hd2, rfl⟩ x
      have hy : Tendsto (fun n => d2 (b n x)) atTop (𝓝 (d2 (g x))) := hT2 d2 hd2 x
      have := S200S_mul_tend d1 a f (hT1 d1 hd1) _ _ hy
      convert this using 1
      · funext n
        change d1 (d2 (a n (b n x))) = d1 (a n (d2 (b n x)))
        rw [S200S_comm R d2 (a n) (hD2 hd2) (ha1 n)]
      · change 𝓝 (d1 (d2 (f (g x)))) = 𝓝 (d1 (f (d2 (g x))))
        rw [S200S_comm R d2 f (hD2 hd2) hf]
  · intro c a f ha
    obtain ⟨ha1, hf, D, hD, hS, hT⟩ := ha
    have hsub := S200S_sub R
    refine ⟨fun n => hsub.2.2 c _ (ha1 n), hsub.2.2 c _ hf, D, hD, hS, ?_⟩
    intro d hd x
    have := (hT d hd x).const_smul c
    simpa using this
  · intro a f g hf hg
    obtain ⟨ha1, hf1, D1, hD1, hS1, hT1⟩ := hf
    obtain ⟨-, hg1, D2, hD2, hS2, hT2⟩ := hg
    ext x
    rw [← sub_eq_zero]
    apply hS2
    intro d2 hd2
    apply hS1
    intro d1 hd1
    have e1 : ∀ z : X, d1 (d2 z) = d2 (d1 z) :=
      fun z => S200S_comm R d1 d2 (hD1 hd1) (S200S_bi_sub R d2 (hD2 hd2)) z
    have t1 : Tendsto (fun n => d2 (d1 (a n x))) atTop (𝓝 (d2 (d1 (f x)))) :=
      ((d2.continuous.tendsto _).comp (hT1 d1 hd1 x))
    have t2 : Tendsto (fun n => d1 (d2 (a n x))) atTop (𝓝 (d1 (d2 (g x)))) :=
      ((d1.continuous.tendsto _).comp (hT2 d2 hd2 x))
    simp_rw [e1] at t2
    have := tendsto_nhds_unique t1 t2
    rw [map_sub, map_sub, e1, e1, this, sub_self]

end QAlgorithms.Papers.Independent.Next46.P06

open QAlgorithms.Papers.Independent.Next46.P06 in
theorem solution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [CompleteSpace X] (A : Graph X) (hA : Sectorial A) :
    AlgebraicConvergenceOn (regularizedStrong (onePlusInverse A)) (operatorCommutant {onePlusInverse A}) ∧
    HausdorffConvergence (regularizedStrong (onePlusInverse A)) :=
  S200S_main (onePlusInverse A)


end
