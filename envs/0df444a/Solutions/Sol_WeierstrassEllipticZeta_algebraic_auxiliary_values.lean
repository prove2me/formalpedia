-- Prove2me | solution 1 for WeierstrassEllipticZeta.algebraic_auxiliary_values
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-05T11:24:09.081272+00:00
-- url     : https://prove2.me/submissions/21b6111c-1e34-4c97-acdb-6c8737865b23

import Theorems.Thm_WeierstrassEllipticZeta_frobenius_stickelberger
import Theorems.Thm_WeierstrassEllipticZeta_hasDerivAt_derivWeierstrassP
import Theorems.Thm_WeierstrassEllipticZeta_hasDerivAt_weierstrassZeta
import Theorems.Thm_WeierstrassEllipticZeta_zeta_addition_formula
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

open Polynomial Filter
open scoped Topology

noncomputable section

namespace WeierstrassEllipticZeta

private theorem zeta_duplication_multiplied (L : PeriodPair) (z : ℂ)
    (hz : z ∉ L.lattice) (h2z : z + z ∉ L.lattice) :
    2 * L.derivWeierstrassP z *
      (weierstrassZeta L (z + z) - 2 * weierstrassZeta L z) =
        6 * L.weierstrassP z ^ 2 - L.g₂ / 2 := by
  have hopen := L.isClosed_lattice.isOpen_compl
  have hP : HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
    simpa using (L.differentiableOn_weierstrassP.differentiableAt
      (hopen.mem_nhds hz)).hasDerivAt
  have hD := hasDerivAt_derivWeierstrassP L z hz
  have hZ := hasDerivAt_weierstrassZeta L z hz
  have hZ2 : HasDerivAt (fun w ↦ weierstrassZeta L (z + w))
      (-L.weierstrassP (z + z)) z := by
    convert! (hasDerivAt_weierstrassZeta L (z + z) h2z).comp z
      ((hasDerivAt_const z z).add (hasDerivAt_id z)) using 1
    simp
  have hnear : ∀ᶠ w in 𝓝 z, w ∉ L.lattice := hopen.mem_nhds hz
  have hnear2 : ∀ᶠ w in 𝓝 z, z + w ∉ L.lattice :=
    (continuousAt_const.add continuousAt_id).eventually (hopen.mem_nhds h2z)
  have heq : (fun w ↦
      2 * (L.weierstrassP w - L.weierstrassP z) * weierstrassZeta L (z + w))
      =ᶠ[𝓝 z] (fun w ↦
      2 * (weierstrassZeta L z + weierstrassZeta L w) *
        (L.weierstrassP w - L.weierstrassP z) +
      L.derivWeierstrassP w - L.derivWeierstrassP z) := by
    filter_upwards [hnear, hnear2] with w hw hzw
    exact zeta_addition_formula L z w hz hw hzw
  have hleft := ((hP.sub_const (L.weierstrassP z)).const_mul 2).mul hZ2
  have hright := (((((hasDerivAt_const z (weierstrassZeta L z)).add hZ).const_mul 2).mul
    (hP.sub_const (L.weierstrassP z))).add hD).sub_const (L.derivWeierstrassP z)
  have hdiff := (hleft.congr_of_eventuallyEq heq.symm).unique hright
  simp only [Pi.add_apply] at hdiff
  linear_combination hdiff

private theorem wp_duplication_quartic (L : PeriodPair) (z : ℂ)
    (hz : z ∉ L.lattice) (h2z : z + z ∉ L.lattice) :
    16 * L.weierstrassP z ^ 4 -
      64 * L.weierstrassP (z + z) * L.weierstrassP z ^ 3 +
      8 * L.g₂ * L.weierstrassP z ^ 2 +
      (32 * L.g₃ + 16 * L.weierstrassP (z + z) * L.g₂) * L.weierstrassP z +
      16 * L.weierstrassP (z + z) * L.g₃ + L.g₂ ^ 2 = 0 := by
  have hd := zeta_duplication_multiplied L z hz h2z
  have hf := frobenius_stickelberger L z z hz hz h2z
  have hc := L.derivWeierstrassP_sq z hz
  linear_combination
    -4 * (2 * L.derivWeierstrassP z *
      (weierstrassZeta L (z + z) - 2 * weierstrassZeta L z) +
        (6 * L.weierstrassP z ^ 2 - L.g₂ / 2)) * hd +
    16 * L.derivWeierstrassP z ^ 2 * hf +
    16 * (2 * L.weierstrassP z + L.weierstrassP (z + z)) * hc

private theorem algebraic_of_duplication_quartic
    (R : Type*) [CommRing R] [IsDomain R] [Algebra R ℂ]
    (x a g₂ g₃ : ℂ) (ha : IsAlgebraic R a)
    (hg₂ : IsAlgebraic R g₂) (hg₃ : IsAlgebraic R g₃)
    (hx : 16*x^4 - 64*a*x^3 + 8*g₂*x^2 + (32*g₃+16*a*g₂)*x +
      16*a*g₃ + g₂^2 = 0) : IsAlgebraic R x := by
  let S := Subalgebra.algebraicClosure R ℂ
  let aS : S := ⟨a, ha⟩
  let g₂S : S := ⟨g₂, hg₂⟩
  let g₃S : S := ⟨g₃, hg₃⟩
  let p : S[X] := C 16 * X^4 - C (64*aS) * X^3 + C (8*g₂S) * X^2 +
    C (32*g₃S+16*aS*g₂S) * X + C (16*aS*g₃S+g₂S^2)
  have hp : p ≠ 0 := by
    intro h
    have hc := congrArg (fun q : S[X] => q.coeff 4) h
    simp only [p, coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X,
      coeff_C, coeff_zero] at hc
    norm_num at hc
  have halg : IsAlgebraic S x := by
    refine ⟨p, hp, ?_⟩
    have h16 : ((16 : S) : ℂ) = 16 := rfl
    have h64 : ((64 : S) : ℂ) = 64 := rfl
    have h8 : ((8 : S) : ℂ) = 8 := rfl
    have h32 : ((32 : S) : ℂ) = 32 := rfl
    convert hx using 1
    norm_num [p, aS, g₂S, g₃S, h16, h64, h8, h32]
    ring
  exact halg.restrictScalars R

private theorem algebraic_half_values
    (R : Type*) [CommRing R] [IsDomain R] [Algebra R ℂ]
    (L : PeriodPair) (u : ℂ) (hu : u ∉ L.lattice)
    (hg₂ : IsAlgebraic R L.g₂) (hg₃ : IsAlgebraic R L.g₃)
    (hp : IsAlgebraic R (L.weierstrassP u))
    (hz : IsAlgebraic R (weierstrassZeta L u)) :
    IsAlgebraic R (L.weierstrassP (u/2)) ∧
      IsAlgebraic R (L.derivWeierstrassP (u/2)) ∧
      IsAlgebraic R (weierstrassZeta L (u/2)) := by
  have hadd : u/2 + u/2 = u := by ring
  have hhalf : u/2 ∉ L.lattice := fun h => hu (hadd ▸ L.lattice.add_mem h h)
  have h2half : u/2 + u/2 ∉ L.lattice := by simpa only [hadd] using hu
  have hquartic := wp_duplication_quartic L (u/2) hhalf h2half
  rw [hadd] at hquartic
  have hphalf := algebraic_of_duplication_quartic R _ _ _ _ hp hg₂ hg₃ hquartic
  have hderiv : IsAlgebraic R (L.derivWeierstrassP (u/2)) := by
    apply IsAlgebraic.of_pow (n := 2) (by decide)
    rw [L.derivWeierstrassP_sq (u/2) hhalf]
    exact (((isAlgebraic_natCast (R := R) 4).mul (hphalf.pow 3)).sub (hg₂.mul hphalf)).sub hg₃
  have hf := frobenius_stickelberger L (u/2) (u/2) hhalf hhalf h2half
  rw [hadd] at hf
  have hdiff : IsAlgebraic R
      (weierstrassZeta L u - weierstrassZeta L (u/2) - weierstrassZeta L (u/2)) := by
    apply IsAlgebraic.of_pow (n := 2) (by decide)
    rw [hf]
    exact (hphalf.add hphalf).add hp
  refine ⟨hphalf, hderiv, ?_⟩
  have he : weierstrassZeta L (u/2) =
      (weierstrassZeta L u -
        (weierstrassZeta L u - weierstrassZeta L (u/2) - weierstrassZeta L (u/2))) / 2 := by ring
  rw [he]
  exact (hz.sub hdiff).mul (isAlgebraic_natCast (R := R) 2).inv


end WeierstrassEllipticZeta

open WeierstrassEllipticZeta

theorem solution
    (L : PeriodPair) (ω u₁ u₂ θ : ℂ)
    (hu₁ : u₁ ∉ L.lattice) (hu₂ : u₂ ∉ L.lattice)
    (h_values : ∀ i, IsAlgebraic (Algebra.adjoin ℚ {θ})
      (theoremOneValues L ω u₁ u₂ i)) :
    ∀ i : Fin 18, IsAlgebraic (Algebra.adjoin ℚ {θ})
      (![L.g₂/4, L.g₃/4, ω, zetaQuasiPeriod L ω, u₁/2, u₂,
        weierstrassZeta L (u₁/2), L.weierstrassP (u₁/2),
        L.derivWeierstrassP (u₁/2), deriv L.derivWeierstrassP (u₁/2),
        L.weierstrassP u₁, L.derivWeierstrassP u₁, deriv L.derivWeierstrassP u₁,
        weierstrassZeta L u₁, L.weierstrassP u₂, L.derivWeierstrassP u₂,
        deriv L.derivWeierstrassP u₂, weierstrassZeta L u₂] i) := by
  let R := Algebra.adjoin ℚ {θ}
  have hg₂ : IsAlgebraic R L.g₂ := h_values 0
  have hg₃ : IsAlgebraic R L.g₃ := h_values 1
  have hp₁ : IsAlgebraic R (L.weierstrassP u₁) := h_values 6
  have hz₁ : IsAlgebraic R (weierstrassZeta L u₁) := h_values 7
  have hp₂ : IsAlgebraic R (L.weierstrassP u₂) := h_values 8
  have hz₂ : IsAlgebraic R (weierstrassZeta L u₂) := h_values 9
  obtain ⟨hphalf, hdhalf, hzhalf⟩ := algebraic_half_values R L u₁ hu₁ hg₂ hg₃ hp₁ hz₁
  have hhalf : u₁/2 ∉ L.lattice := by
    intro h
    have := L.lattice.add_mem h h
    exact hu₁ (by convert this using 1; ring)
  have hd (z : ℂ) (hreg : z ∉ L.lattice) (hp : IsAlgebraic R (L.weierstrassP z)) :
      IsAlgebraic R (L.derivWeierstrassP z) := by
    apply IsAlgebraic.of_pow (n := 2) (by decide)
    rw [L.derivWeierstrassP_sq z hreg]
    exact (((isAlgebraic_natCast (R := R) 4).mul (hp.pow 3)).sub (hg₂.mul hp)).sub hg₃
  have hdd (z : ℂ) (hreg : z ∉ L.lattice) (hp : IsAlgebraic R (L.weierstrassP z)) :
      IsAlgebraic R (deriv L.derivWeierstrassP z) := by
    rw [(hasDerivAt_derivWeierstrassP L z hreg).deriv]
    exact ((isAlgebraic_natCast (R := R) 6).mul (hp.pow 2)).sub
      (hg₂.mul (isAlgebraic_natCast (R := R) 2).inv)
  have htwo : IsAlgebraic R (2 : ℂ) := isAlgebraic_natCast 2
  have hfour : IsAlgebraic R (4 : ℂ) := isAlgebraic_natCast 4
  intro i
  fin_cases i
  · exact hg₂.mul hfour.inv
  · exact hg₃.mul hfour.inv
  · exact h_values 2
  · exact h_values 3
  · exact (h_values 4).mul htwo.inv
  · exact h_values 5
  · exact hzhalf
  · exact hphalf
  · exact hdhalf
  · exact hdd (u₁/2) hhalf hphalf
  · exact hp₁
  · exact hd u₁ hu₁ hp₁
  · exact hdd u₁ hu₁ hp₁
  · exact hz₁
  · exact hp₂
  · exact hd u₂ hu₂ hp₂
  · exact hdd u₂ hu₂ hp₂
  · exact hz₂

