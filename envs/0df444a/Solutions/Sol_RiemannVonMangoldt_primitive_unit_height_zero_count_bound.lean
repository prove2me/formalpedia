-- Prove2me | solution 1 for RiemannVonMangoldt.primitive_unit_height_zero_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @phi9t
-- created : 2026-11-23T05:51:15.780752+00:00
-- url     : https://prove2.me/submissions/1eddc378-fd7b-4afb-858d-35c057644953

import Definitions.Def_RiemannVonMangoldt_ZeroCounts
import Theorems.Thm_Helfgott_regularized_primitive_strip_band_multiplicity_logarithmic_bound
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Analytic.Order
import Mathlib.Algebra.BigOperators.Finprod

/-! P2M-16C integrated public-definition proof candidate.

The count is imported from its genuine published module. The support, shell
and monotonicity proofs retain their checked mathematical bodies. The actual
accepted Helfgott supplier discharges the intermediate band premise. -/

set_option autoImplicit false

open Complex Metric Filter Set
open scoped Topology

namespace RiemannVonMangoldt

/-- Analytic orders with the convention that infinite order contributes zero
have finite nonzero weight support on each compact closed ball. -/
private theorem finite_analytic_order_weight_support (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (R : ℝ) :
    (closedBall (0 : ℂ) R ∩
      Function.support (fun s : ℂ => (analyticOrderNatAt f s : ℝ))).Finite := by
  have hfinite :
      (MeromorphicOn.divisor f (closedBall (0 : ℂ) R)).support.Finite :=
    (MeromorphicOn.divisor f (closedBall (0 : ℂ) R)).finiteSupport
      (isCompact_closedBall (0 : ℂ) R)
  apply hfinite.subset
  rintro s ⟨hs, hw⟩
  have ha : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R) :=
    fun z _ => hf.analyticAt z
  rw [Function.mem_support] at hw ⊢
  rw [MeromorphicOn.divisor_apply ha.meromorphicOn hs,
    (ha s hs).meromorphicOrderAt_eq]
  cases ho : analyticOrderAt f s with
  | top =>
    simp [analyticOrderNatAt, ho] at hw
  | coe n =>
    simpa [analyticOrderNatAt, ho] using hw

private theorem in_closedBall_of_strip_height (s : ℂ) (U : ℝ)
    (hre0 : 0 < s.re) (hre1 : s.re < 1) (him : |s.im| ≤ U) :
    s ∈ closedBall (0 : ℂ) (|U| + 2) := by
  have hRe : |s.re| ≤ 1 := by
    rw [abs_of_pos hre0]
    exact le_of_lt hre1
  have hIm : |s.im| ≤ |U| := le_trans him (le_abs_self U)
  rw [mem_closedBall, dist_zero_right]
  calc
    ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
    _ ≤ 1 + |U| := add_le_add hRe hIm
    _ ≤ |U| + 2 := by linarith

/-- Exact support required by the platform's Dirichlet zero count, with
both signs of the imaginary part, closed height cutoff, no primitivity
restriction, and no finite-support assumption. -/
theorem dirichlet_weighted_zero_support_finite
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (U : ℝ) :
    ({s : ℂ | 0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ U ∧ χ.LFunction s = 0} ∩
      Function.support (fun s : ℂ => (analyticOrderNatAt χ.LFunction s : ℝ))).Finite := by
  by_cases hχ : χ = 1
  · subst χ
    have hfin := finite_analytic_order_weight_support
      (DirichletCharacter.LFunctionTrivChar₁ q)
      (DirichletCharacter.differentiable_LFunctionTrivChar₁ q) (|U| + 2)
    apply hfin.subset
    rintro s ⟨⟨h0, h1, hU, hz⟩, hw⟩
    have hs1 : s ≠ (1 : ℂ) := by
      intro hs
      subst s
      norm_num at h1
    have hAna :
        AnalyticAt ℂ ((1 : DirichletCharacter ℂ q).LFunction) s := by
      have hOpen : IsOpen ({(1 : ℂ)}ᶜ) := isOpen_compl_singleton
      have hDiff : DifferentiableOn ℂ ((1 : DirichletCharacter ℂ q).LFunction)
          ({(1 : ℂ)}ᶜ) := by
        intro z hz'
        have hz1 : z ≠ (1 : ℂ) := by simpa using hz'
        exact (DirichletCharacter.differentiableAt_LFunction _ z
          (Or.inl hz1)).differentiableWithinAt
      exact hDiff.analyticAt (hOpen.mem_nhds (by simpa using hs1))
    have hNear :
        DirichletCharacter.LFunctionTrivChar₁ q =ᶠ[𝓝 s]
          (fun z : ℂ => (z - 1) * (1 : DirichletCharacter ℂ q).LFunction z) := by
      have hnbhd : ({(1 : ℂ)}ᶜ : Set ℂ) ∈ 𝓝 s :=
        isOpen_compl_singleton.mem_nhds (by simpa using hs1)
      filter_upwards [hnbhd] with z hz1
      have hne : z ≠ (1 : ℂ) := by simpa using hz1
      simp [DirichletCharacter.LFunctionTrivChar₁,
        DirichletCharacter.LFunctionTrivChar, hne]
    have hOrder :
        analyticOrderAt (DirichletCharacter.LFunctionTrivChar₁ q) s =
          analyticOrderAt ((1 : DirichletCharacter ℂ q).LFunction) s := by
      calc
        _ = analyticOrderAt
            (fun z : ℂ => (z - 1) * (1 : DirichletCharacter ℂ q).LFunction z) s :=
              analyticOrderAt_congr hNear
        _ = analyticOrderAt (fun z : ℂ => z - 1) s +
            analyticOrderAt ((1 : DirichletCharacter ℂ q).LFunction) s :=
              analyticOrderAt_mul (by fun_prop) hAna
        _ = _ := by simp [analyticOrderAt_id_sub_const_of_ne hs1]
    have hWeight :
        analyticOrderNatAt (DirichletCharacter.LFunctionTrivChar₁ q) s =
          analyticOrderNatAt ((1 : DirichletCharacter ℂ q).LFunction) s := by
      simpa only [analyticOrderNatAt] using congrArg ENat.toNat hOrder
    refine ⟨in_closedBall_of_strip_height s U h0 h1 hU, ?_⟩
    change (analyticOrderNatAt (DirichletCharacter.LFunctionTrivChar₁ q) s : ℝ) ≠ 0
    rw [hWeight]
    exact hw
  · have hfin := finite_analytic_order_weight_support
      χ.LFunction (DirichletCharacter.differentiable_LFunction hχ) (|U| + 2)
    apply hfin.subset
    rintro s ⟨⟨h0, h1, hU, hz⟩, hw⟩
    exact ⟨in_closedBall_of_strip_height s U h0 h1 hU, hw⟩


private def stripZeroSet {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (T : ℝ) : Set ℂ :=
  {s | 0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ T ∧ χ.LFunction s = 0}

private noncomputable def zeroWeight {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ℂ → ℝ :=
  fun s => (analyticOrderNatAt χ.LFunction s : ℝ)

/-- The algebraic finite-support shell subtraction needed before using the
accepted Helfgott unit-band bound. Finiteness remains an explicit premise. -/
theorem finsum_shell_sub {α : Type*} (f : α → ℝ)
    {A B : Set α} (hAB : A ⊆ B)
    (hfin : (B ∩ Function.support f).Finite) :
    (∑ᶠ x ∈ B, f x) - (∑ᶠ x ∈ A, f x) =
      ∑ᶠ x ∈ B \ A, f x := by
  have h := finsum_mem_add_sdiff' (f := f) hAB hfin
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using h.symm)

/-- Exact unconditional strict-left, closed-right signed-height shell of the
original platform zero-count definition, using the kernel-checked finite support theorem. -/
theorem dirichlet_zero_count_sub_eq_signed_shell
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (T U : ℝ) (hTU : T ≤ U) :
    dirichletZeroCount χ U - dirichletZeroCount χ T =
      ∑ᶠ s ∈ {s : ℂ | 0 < s.re ∧ s.re < 1 ∧
           T < |s.im| ∧ |s.im| ≤ U ∧ χ.LFunction s = 0},
         (analyticOrderNatAt χ.LFunction s : ℝ) := by
  have hfinite : (stripZeroSet χ U ∩
      Function.support (zeroWeight χ)).Finite := by
    change ({s : ℂ | 0 < s.re ∧ s.re < 1 ∧
       |s.im| ≤ U ∧ χ.LFunction s = 0} ∩
       Function.support (fun s : ℂ =>
         (analyticOrderNatAt χ.LFunction s : ℝ))).Finite
    exact dirichlet_weighted_zero_support_finite q χ U
  have hsub : stripZeroSet χ T ⊆ stripZeroSet χ U := by
    intro s hs
    rcases hs with ⟨h0, h1, h2, h3⟩
    exact ⟨h0, h1, le_trans h2 hTU, h3⟩
  have h := finsum_shell_sub (zeroWeight χ) hsub hfinite
  have hset : (stripZeroSet χ U) \ (stripZeroSet χ T) =
      {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ T < |s.im| ∧ |s.im| ≤ U ∧
        χ.LFunction s = 0} := by
    ext s
    simp only [stripZeroSet, Set.mem_diff, Set.mem_setOf_eq]
    constructor
    · intro ⟨⟨h0, h1, hU, hz⟩, hn⟩
      have hT : T < |s.im| := by
        by_contra h
        exact hn ⟨h0, h1, le_of_not_gt h, hz⟩
      exact ⟨h0, h1, hT, hU, hz⟩
    · intro ⟨h0, h1, hT, hU, hz⟩
      refine ⟨⟨h0, h1, hU, hz⟩, ?_⟩
      intro hsmall
      exact (not_le_of_gt hT) hsmall.2.2.1
  rw [hset] at h
  simpa only [dirichletZeroCount, stripZeroSet, zeroWeight] using h


#print axioms RiemannVonMangoldt.dirichlet_weighted_zero_support_finite
#print axioms RiemannVonMangoldt.dirichlet_zero_count_sub_eq_signed_shell
#check RiemannVonMangoldt.dirichlet_zero_count_sub_eq_signed_shell

/-- Unconditional monotonicity of the original signed Dirichlet zero count,
for arbitrary real heights and all characters, by nonnegative multiplicities. -/
theorem dirichlet_zero_count_mono (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) {T U : ℝ} (hTU : T ≤ U) :
    dirichletZeroCount χ T ≤ dirichletZeroCount χ U := by
  apply sub_nonneg.mp
  rw [dirichlet_zero_count_sub_eq_signed_shell q χ T U hTU]
  apply finsum_nonneg
  intro s
  apply finsum_nonneg
  intro hs
  exact Nat.cast_nonneg _

#print axioms RiemannVonMangoldt.dirichlet_zero_count_mono
#check RiemannVonMangoldt.dirichlet_zero_count_mono


/-! P2M-16C: exact accepted primitive signed-height band inequality
to original Dirichlet zero count. The hband parameter has precisely the
instantiated content of the accepted Helfgott theorem. This intermediate bridge takes
the band premise explicitly; the final theorem below discharges it using the
actual accepted proof module. -/

open scoped Classical

private theorem primitive_regularized_weight_eq
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) (s : ℂ) (hs1 : s ≠ (1 : ℂ)) :
    analyticOrderNatAt
      (if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ 1 else χ.LFunction) s =
    analyticOrderNatAt χ.LFunction s := by
  by_cases hχ : χ = 1
  · have hq : q = 1 := by
      have hp' : DirichletCharacter.conductor χ = q := hp
      rw [hχ, DirichletCharacter.conductor_one] at hp'
      exact hp'.symm
    subst q
    subst χ
    simp only [if_pos rfl]
    have hAna : AnalyticAt ℂ ((1 : DirichletCharacter ℂ 1).LFunction) s := by
      have hOpen : IsOpen ({(1 : ℂ)}ᶜ) := isOpen_compl_singleton
      have hDiff : DifferentiableOn ℂ ((1 : DirichletCharacter ℂ 1).LFunction)
          ({(1 : ℂ)}ᶜ) := by
        intro z hz'
        have hz1 : z ≠ (1 : ℂ) := by simpa using hz'
        exact (DirichletCharacter.differentiableAt_LFunction _ z
          (Or.inl hz1)).differentiableWithinAt
      exact hDiff.analyticAt (hOpen.mem_nhds (by simpa using hs1))
    have hNear :
        DirichletCharacter.LFunctionTrivChar₁ 1 =ᶠ[𝓝 s]
          (fun z : ℂ => (z - 1) * (1 : DirichletCharacter ℂ 1).LFunction z) := by
      have hnbhd : ({(1 : ℂ)}ᶜ : Set ℂ) ∈ 𝓝 s :=
        isOpen_compl_singleton.mem_nhds (by simpa using hs1)
      filter_upwards [hnbhd] with z hz1
      have hne : z ≠ (1 : ℂ) := by simpa using hz1
      simp [DirichletCharacter.LFunctionTrivChar₁,
        DirichletCharacter.LFunctionTrivChar, hne]
    have hOrder :
        analyticOrderAt (DirichletCharacter.LFunctionTrivChar₁ 1) s =
          analyticOrderAt ((1 : DirichletCharacter ℂ 1).LFunction) s := by
      calc
        _ = analyticOrderAt
            (fun z : ℂ => (z - 1) * (1 : DirichletCharacter ℂ 1).LFunction z) s :=
              analyticOrderAt_congr hNear
        _ = analyticOrderAt (fun z : ℂ => z - 1) s +
            analyticOrderAt ((1 : DirichletCharacter ℂ 1).LFunction) s :=
              analyticOrderAt_mul (by fun_prop) hAna
        _ = _ := by simp [analyticOrderAt_id_sub_const_of_ne hs1]
    simpa [analyticOrderNatAt] using congrArg ENat.toNat hOrder
  · simp only [if_neg hχ]

theorem primitive_unit_height_zero_count_bound_of_band
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) (T : ℝ) (hT : 8 ≤ T)
    (hband : ∀ (Z : Finset ℂ),
      (∀ ρ ∈ Z, -(1/2 : ℝ) ≤ ρ.re ∧ ρ.re ≤ 2 ∧
        T ≤ |ρ.im| ∧ |ρ.im| ≤ T + 1) →
      (∑ ρ ∈ Z,
        (analyticOrderNatAt
          (if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ 1
           else χ.LFunction) ρ : ℝ))
        ≤ 1900 + 50 * Real.log (q : ℝ) + 110 * Real.log (T + 2)) :
    0 ≤ dirichletZeroCount χ (T + 1) - dirichletZeroCount χ T ∧
    dirichletZeroCount χ (T + 1) - dirichletZeroCount χ T ≤
      1900 + 50 * Real.log (q : ℝ) + 110 * Real.log (T + 2) := by
  classical
  let S : Set ℂ :=
    {s | 0 < s.re ∧ s.re < 1 ∧ T < |s.im| ∧
      |s.im| ≤ T + 1 ∧ χ.LFunction s = 0}
  let w : ℂ → ℝ := fun s => (analyticOrderNatAt χ.LFunction s : ℝ)
  have hfinite : (S ∩ Function.support w).Finite := by
    apply (dirichlet_weighted_zero_support_finite q χ (T + 1)).subset
    rintro s ⟨⟨h0, h1, hLower, hUpper, hz⟩, hw⟩
    exact ⟨⟨h0, h1, hUpper, hz⟩, hw⟩
  let Z : Finset ℂ := hfinite.toFinset
  have hZ (s : ℂ) (hs : s ∈ Z) :
      -(1/2 : ℝ) ≤ s.re ∧ s.re ≤ 2 ∧
        T ≤ |s.im| ∧ |s.im| ≤ T + 1 := by
    obtain ⟨h0, h1, hLower, hUpper, hz⟩ :=
      (hfinite.mem_toFinset.mp hs).1
    exact ⟨by linarith, by linarith, le_of_lt hLower, hUpper⟩
  have hsum : (∑ᶠ s ∈ S, w s) = ∑ s ∈ Z, w s := by
    exact finsum_mem_eq_sum w hfinite
  have hweight (s : ℂ) (hs : s ∈ Z) :
      w s =
        (analyticOrderNatAt
          (if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ 1
           else χ.LFunction) s : ℝ) := by
    have h1 : s.re < 1 := (hfinite.mem_toFinset.mp hs).1.2.1
    have hs1 : s ≠ (1 : ℂ) := by
      intro he
      subst s
      norm_num at h1
    simpa only [w] using congrArg (fun n : ℕ => (n : ℝ))
      (primitive_regularized_weight_eq q χ hp s hs1).symm
  have hTplus : T ≤ T + 1 := by linarith
  constructor
  · exact sub_nonneg.mpr (dirichlet_zero_count_mono q χ hTplus)
  · calc
      dirichletZeroCount χ (T + 1) - dirichletZeroCount χ T =
          ∑ᶠ s ∈ S, w s := by
            simpa only [S, w] using
              dirichlet_zero_count_sub_eq_signed_shell q χ T (T + 1) hTplus
      _ = ∑ s ∈ Z, w s := hsum
      _ = ∑ s ∈ Z,
          (analyticOrderNatAt
            (if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ 1
             else χ.LFunction) s : ℝ) := by
              apply Finset.sum_congr rfl
              exact hweight
      _ ≤ _ := hband Z hZ

#print axioms RiemannVonMangoldt.primitive_unit_height_zero_count_bound_of_band
#check RiemannVonMangoldt.primitive_unit_height_zero_count_bound_of_band


/-- The original signed zero count increases by at most the accepted explicit
primitive band estimate over one unit of height. -/
theorem primitive_unit_height_zero_count_bound
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) (T : ℝ) (hT : 8 ≤ T) :
    0 ≤ dirichletZeroCount χ (T + 1) - dirichletZeroCount χ T ∧
    dirichletZeroCount χ (T + 1) - dirichletZeroCount χ T ≤
      1900 + 50 * Real.log (q : ℝ) + 110 * Real.log (T + 2) := by
  apply primitive_unit_height_zero_count_bound_of_band q χ hp T hT
  intro Z hZ
  have haccepted :=
    Helfgott.regularized_primitive_strip_band_multiplicity_logarithmic_bound
      q χ hp T hT Z hZ
  by_cases hχ : χ = 1
  · simpa only [if_pos hχ] using haccepted
  · simpa only [if_neg hχ] using haccepted

end RiemannVonMangoldt

theorem solution
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) (T : ℝ) (hT : 8 ≤ T) :
    0 ≤ RiemannVonMangoldt.dirichletZeroCount χ (T + 1) -
      RiemannVonMangoldt.dirichletZeroCount χ T ∧
    RiemannVonMangoldt.dirichletZeroCount χ (T + 1) -
      RiemannVonMangoldt.dirichletZeroCount χ T ≤
        1900 + 50 * Real.log (q : ℝ) + 110 * Real.log (T + 2) := by
  exact RiemannVonMangoldt.primitive_unit_height_zero_count_bound q χ hp T hT

#print axioms RiemannVonMangoldt.primitive_unit_height_zero_count_bound
#check RiemannVonMangoldt.primitive_unit_height_zero_count_bound
#print axioms solution
#check solution
