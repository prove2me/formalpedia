-- Prove2me | solution 1 for PrimePairSieve_reciprocal_weighted_sifted_bound
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T18:38:17.556727+00:00
-- url     : https://prove2.me/submissions/a1e59a5b-4c03-45e0-9d72-2d12f1bbacf2

import Theorems.Thm_WeightedHilbert_nonuniform_large_sieve_sixteen
import Theorems.Thm_PrimePairSieve_squarefree_primitive_fourier_energy
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.ZMod.Units
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Positivity

set_option autoImplicit false

open scoped BigOperators
namespace WeightedFourier

theorem rational_circle_spacing (x y : ℚ)
    (hx : (x : ℝ) ∈ Set.Ico 0 1) (hy : (y : ℝ) ∈ Set.Ico 0 1)
    (hxy : x ≠ y) (m : ℤ) :
    1 / ((x.den : ℝ) * (y.den : ℝ)) ≤ |(x : ℝ) - (y : ℝ) + m| := by
  have hd : (x : ℝ) - (y : ℝ) + m ≠ 0 := by
    intro h
    have hlo : (-1 : ℝ) < m := by linarith [hx.1, hx.2, hy.1, hy.2]
    have hhi : (m : ℝ) < 1 := by linarith [hx.1, hx.2, hy.1, hy.2]
    have hlo' : (-1 : ℤ) < m := by exact_mod_cast hlo
    have hhi' : m < (1 : ℤ) := by exact_mod_cast hhi
    have hm : m = 0 := by omega
    have he : (x : ℝ) = (y : ℝ) := by simpa [hm, sub_eq_zero] using h
    apply hxy
    exact_mod_cast he
  have hxd : (0 : ℝ) < x.den := by exact_mod_cast x.den_pos
  have hyd : (0 : ℝ) < y.den := by exact_mod_cast y.den_pos
  let L : ℤ := x.num * y.den - y.num * x.den + m * x.den * y.den
  have he : (L : ℝ) = ((x : ℝ) - (y : ℝ) + m) * ((x.den : ℝ) * y.den) := by
    dsimp [L]
    push_cast
    rw [Rat.cast_def, Rat.cast_def]
    field_simp [ne_of_gt hxd, ne_of_gt hyd]
  have hL : L ≠ 0 := by
    intro hz
    rw [hz, Int.cast_zero] at he
    exact hd ((mul_eq_zero.mp he.symm).resolve_right (ne_of_gt (mul_pos hxd hyd)))
  have habs : (1 : ℤ) ≤ |L| := by
    have hp : 0 < |L| := abs_pos.mpr hL
    omega
  have habsR : (1 : ℝ) ≤ |(L : ℝ)| := by exact_mod_cast habs
  rw [he, abs_mul, abs_of_pos (mul_pos hxd hyd)] at habsR
  exact (div_le_iff₀ (mul_pos hxd hyd)).mpr habsR

theorem rational_circle_spacing_level (x y : ℚ) (z : ℝ)
    (hx : (x : ℝ) ∈ Set.Ico 0 1) (hy : (y : ℝ) ∈ Set.Ico 0 1)
    (hxy : x ≠ y) (hyz : (y.den : ℝ) ≤ z) (m : ℤ) :
    1 / ((x.den : ℝ) * z) ≤ |(x : ℝ) - (y : ℝ) + m| := by
  have hxd : (0 : ℝ) < x.den := by exact_mod_cast x.den_pos
  have hyd : (0 : ℝ) < y.den := by exact_mod_cast y.den_pos
  exact (one_div_le_one_div_of_le (mul_pos hxd hyd)
    (mul_le_mul_of_nonneg_left hyz hxd.le)).trans (rational_circle_spacing x y hx hy hxy m)


theorem rational_family_large_sieve
    (hLS : ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (N : ℕ) (θ δ : ι → ℝ) (a : ℕ → ℂ),
      (∀ r, 0 < δ r) → (∀ r, δ r ≤ 1) →
      (∀ r s, r ≠ s → ∀ m : ℤ, δ r ≤ |θ r-θ s+m|) →
      (∑ r, ‖∑ n ∈ Finset.range N,
        a n * Complex.exp (2*(Real.pi : ℂ)*Complex.I*(n : ℂ)*(θ r : ℂ))‖^2 /
        ((N : ℝ)+16/δ r)) ≤ ∑ n ∈ Finset.range N, ‖a n‖^2)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → ℚ) (hf : Function.Injective f) (N : ℕ) (z : ℝ) (hz : 1 ≤ z)
    (hS : ∀ r, (f r : ℝ) ∈ Set.Ico 0 1 ∧ ((f r).den : ℝ) ≤ z)
    (a : ℕ → ℂ) :
    (∑ r, ‖∑ n ∈ Finset.range N,
      a n * Complex.exp (2*(Real.pi : ℂ)*Complex.I*(n : ℂ)*(f r : ℂ))‖^2 /
      ((N : ℝ)+16*((f r).den : ℝ)*z)) ≤ ∑ n ∈ Finset.range N, ‖a n‖^2 := by
  have hpos (r : ι) : 0 < 1 / (((f r).den : ℝ)*z) := by
    have hr : (0 : ℝ) < (f r).den := by exact_mod_cast (f r).den_pos
    exact div_pos (by norm_num) (mul_pos hr (by linarith))
  have hunit (r : ι) : 1 / (((f r).den : ℝ)*z) ≤ 1 := by
    have hr : (1 : ℝ) ≤ (f r).den := by exact_mod_cast (f r).den_pos
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (f r).den*z)).mpr
    nlinarith
  have hgap (r s : ι) (hrs : r ≠ s) (m : ℤ) :
      1 / (((f r).den : ℝ)*z) ≤ |(f r : ℝ)-(f s : ℝ)+m| := by
    exact rational_circle_spacing_level (f r) (f s) z
      (hS r).1 (hS s).1 (fun h => hrs (hf h)) (hS s).2 m
  have h := hLS ι N (fun r => (f r : ℝ)) (fun r => 1/(((f r).den : ℝ)*z)) a
    hpos hunit hgap
  have hden (q : ℚ) : (16 : ℝ) / (1 / ((q.den : ℝ)*z)) = 16*(q.den : ℝ)*z := by
    simp only [one_div, div_inv_eq_mul]
    ring
  simpa only [hden, Complex.ofReal_ratCast] using h

end WeightedFourier

set_option autoImplicit false

namespace WeightedFourier

abbrev ReducedUnitFrequency := Σ q : ℕ+, (ZMod (q : ℕ))ˣ

noncomputable def unitFraction (r : ReducedUnitFrequency) : ℚ :=
  (r.2.val.val : ℚ) / (r.1 : ℕ)

theorem unitFraction_den (r : ReducedUnitFrequency) :
    (unitFraction r).den = (r.1 : ℕ) := by
  have h := Rat.den_div_eq_of_coprime
    (a := (r.2.val.val : ℤ)) (b := ((r.1 : ℕ) : ℤ))
    (by exact_mod_cast r.1.pos)
    (by simpa only [Int.natAbs_natCast] using ZMod.val_coe_unit_coprime r.2)
  simpa only [unitFraction, Int.cast_natCast, Int.natCast_inj] using h

theorem unitFraction_mem_Ico (r : ReducedUnitFrequency) :
    (unitFraction r : ℝ) ∈ Set.Ico 0 1 := by
  have hq : (0 : ℝ) < (r.1 : ℕ) := by exact_mod_cast r.1.pos
  have ha : (r.2.val.val : ℝ) < (r.1 : ℕ) := by exact_mod_cast r.2.val.val_lt
  simp only [unitFraction, Rat.cast_div, Rat.cast_natCast, Set.mem_Ico]
  exact ⟨div_nonneg (Nat.cast_nonneg _) hq.le, (div_lt_one hq).mpr ha⟩

theorem unitFraction_injective : Function.Injective unitFraction := by
  rintro ⟨q,u⟩ ⟨r,v⟩ h
  have hd := congrArg Rat.den h
  rw [unitFraction_den, unitFraction_den] at hd
  have hqr : q = r := Subtype.ext hd
  subst r
  have hq : (q : ℚ) ≠ 0 := by positivity
  change (u.val.val : ℚ)/(q : ℕ) = (v.val.val : ℚ)/(q : ℕ) at h
  have hv : (u.val.val : ℚ) = (v.val.val : ℚ) := (div_left_inj' hq).mp h
  have hn : u.val.val = v.val.val := by exact_mod_cast hv
  have hu : u = v := Units.ext (ZMod.val_injective (q : ℕ) hn)
  subst v
  rfl

end WeightedFourier

namespace WeightedFourier

noncomputable def unitIndex {Q : Finset ℕ+}
    (r : Σ q : Q, (ZMod (q.val : ℕ))ˣ) : ReducedUnitFrequency := ⟨r.1.val,r.2⟩

lemma unitIndex_injective (Q : Finset ℕ+) : Function.Injective (@unitIndex Q) := by
  rintro ⟨⟨q,hq⟩,u⟩ ⟨⟨r,hr⟩,v⟩ h
  have hqr := congrArg Sigma.fst h
  change q = r at hqr
  subst r
  have huv : u = v := eq_of_heq (Sigma.mk.inj h).2
  subst v
  rfl

theorem unit_frequency_weighted_upper
    (hLS : ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (N : ℕ) (θ δ : ι → ℝ) (a : ℕ → ℂ),
      (∀ r, 0 < δ r) → (∀ r, δ r ≤ 1) →
      (∀ r s, r ≠ s → ∀ m : ℤ, δ r ≤ |θ r-θ s+m|) →
      (∑ r, ‖∑ n ∈ Finset.range N,
        a n * Complex.exp (2*(Real.pi : ℂ)*Complex.I*(n : ℂ)*(θ r : ℂ))‖^2 /
        ((N : ℝ)+16/δ r)) ≤ ∑ n ∈ Finset.range N, ‖a n‖^2)
    (Q : Finset ℕ+) (N : ℕ) (z : ℝ) (hz : 1 ≤ z)
    (hQ : ∀ q ∈ Q, ((q : ℕ) : ℝ) ≤ z) (a : ℕ → ℂ) :
    (∑ q : Q, ∑ u : (ZMod (q.val : ℕ))ˣ,
      ‖∑ n ∈ Finset.range N, a n * Complex.exp
        (2*(Real.pi : ℂ)*Complex.I*(n : ℂ)*(unitFraction ⟨q.val,u⟩ : ℂ))‖^2 /
          ((N : ℝ)+16*((q.val : ℕ) : ℝ)*z)) ≤
      ∑ n ∈ Finset.range N, ‖a n‖^2 := by
  classical
  let f (r : Σ q : Q, (ZMod (q.val : ℕ))ˣ) : ℚ := unitFraction (unitIndex r)
  have hf : Function.Injective f := unitFraction_injective.comp (unitIndex_injective Q)
  have h := rational_family_large_sieve hLS f hf N z hz
    (fun r => ⟨unitFraction_mem_Ico (unitIndex r), by
      rw [unitFraction_den]; exact hQ r.1.val r.1.property⟩) a
  simpa only [f, unitFraction_den, Fintype.sum_sigma, unitIndex] using h

end WeightedFourier

namespace WeightedSieve

noncomputable def unitFourier (q : ℕ+) (u : (ZMod (q : ℕ))ˣ) (n : ℕ) : ℂ :=
  Complex.exp (2*(Real.pi : ℂ)*Complex.I*(n : ℂ)*
    (WeightedFourier.unitFraction ⟨q,u⟩ : ℂ))

lemma char_unitFraction (q : ℕ+) (u : (ZMod (q : ℕ))ˣ) (n : ℕ)
    (χ : AddChar (ZMod (q : ℕ)) ℂ)
    (hχ : ∀ m : ℕ, χ (m : ZMod (q : ℕ)) =
      Complex.exp (2*(Real.pi : ℂ)*Complex.I*(m : ℂ)/((q : ℕ) : ℂ))) :
    χ (u.val*(n : ZMod (q : ℕ))) = unitFourier q u n := by
  have he : u.val*(n : ZMod (q : ℕ)) = ((u.val.val*n : ℕ) : ZMod (q : ℕ)) := by
    simp only [Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [he, hχ]
  simp only [unitFourier, WeightedFourier.unitFraction, Rat.cast_div, Rat.cast_natCast,
    Nat.cast_mul]
  congr 1
  ring

lemma indicator_fourier (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.range N)
    (f : ℕ → ℂ) :
    (∑ n ∈ Finset.range N, (if n ∈ A then (1 : ℂ) else 0)*f n) = ∑ n ∈ A, f n := by
  classical
  calc
    _ = ∑ n ∈ A, (if n ∈ A then (1 : ℂ) else 0)*f n :=
      (Finset.sum_subset hA (fun n hn hnot => by simp [hnot])).symm
    _ = _ := Finset.sum_congr rfl (fun n hn => by simp [hn])

lemma indicator_mass (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.range N) :
    (∑ n ∈ Finset.range N, ‖if n ∈ A then (1 : ℂ) else 0‖^2) = (A.card : ℝ) := by
  classical
  calc
    _ = ∑ n ∈ A, ‖if n ∈ A then (1 : ℂ) else 0‖^2 :=
      (Finset.sum_subset hA (fun n hn hnot => by simp [hnot])).symm
    _ = ∑ _n ∈ A, (1 : ℝ) := Finset.sum_congr rfl (fun n hn => by simp [hn])
    _ = _ := by simp

/-- The finite weighted sieve assembly: the analytic upper energy and arithmetic lower
energy are separate inputs, both discharged by accepted theorems in the concrete application. -/
theorem count_le_reciprocal_of_energy
    (Q : Finset ℕ+) (h1 : 1 ∈ Q) (N : ℕ) (z : ℝ) (hz : 1 ≤ z)
    (A : Finset ℕ) (g : ℕ+ → ℝ) (hg : ∀ q ∈ Q, 0 ≤ g q) (hg1 : g 1 = 1)
    (hupper : (∑ q : Q, ∑ u : (ZMod (q.val : ℕ))ˣ,
      ‖∑ n ∈ A, unitFourier q.val u n‖^2 / ((N : ℝ)+16*((q.val : ℕ) : ℝ)*z)) ≤ (A.card : ℝ))
    (hlower : ∀ q ∈ Q, g q*(A.card : ℝ)^2 ≤
      ∑ u : (ZMod (q : ℕ))ˣ, ‖∑ n ∈ A, unitFourier q u n‖^2) :
    (A.card : ℝ) ≤ (∑ q ∈ Q, g q / ((N : ℝ)+16*((q : ℕ) : ℝ)*z))⁻¹ := by
  classical
  let D : ℝ := ∑ q : Q, g q.val / ((N : ℝ)+16*((q.val : ℕ) : ℝ)*z)
  have hd (q : ℕ+) : 0 < (N : ℝ)+16*((q : ℕ) : ℝ)*z := by
    have hq : (0 : ℝ) < (q : ℕ) := by exact_mod_cast q.pos
    positivity
  have hD : 0 < D := by
    apply Finset.sum_pos'
    · intro q hq
      exact div_nonneg (hg q.val q.property) (hd q.val).le
    · refine ⟨⟨1,h1⟩, Finset.mem_univ _, ?_⟩
      change 0 < g 1 / ((N : ℝ)+16*((1 : ℕ+) : ℕ)*z)
      rw [hg1]
      exact div_pos (by norm_num) (hd 1)
  have hbound : (A.card : ℝ)^2 * D ≤ (A.card : ℝ) := by
    calc
      _ = ∑ q : Q, g q.val*(A.card : ℝ)^2 / ((N : ℝ)+16*((q.val : ℕ) : ℝ)*z) := by
        dsimp only [D]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        ring
      _ ≤ ∑ q : Q, (∑ u : (ZMod (q.val : ℕ))ˣ,
          ‖∑ n ∈ A, unitFourier q.val u n‖^2) / ((N : ℝ)+16*((q.val : ℕ) : ℝ)*z) := by
        exact Finset.sum_le_sum (fun q hq =>
          div_le_div_of_nonneg_right (hlower q.val q.property) (hd q.val).le)
      _ ≤ _ := by simpa only [Finset.sum_div] using hupper
  have hc : 0 ≤ (A.card : ℝ) := Nat.cast_nonneg A.card
  have hfinal : (A.card : ℝ) ≤ D⁻¹ := by
    by_cases hzA : (A.card : ℝ) = 0
    · rw [hzA]; positivity
    · have hcpos : 0 < (A.card : ℝ) := lt_of_le_of_ne hc (Ne.symm hzA)
      have hh : (A.card : ℝ)*D ≤ 1 := by
        apply (mul_le_mul_iff_right₀ hcpos).mp
        nlinarith
      rw [← one_div, le_div_iff₀ hD]
      exact hh
  have hsum : D = ∑ q ∈ Q, g q / ((N : ℝ)+16*((q : ℕ) : ℝ)*z) := by
    exact Finset.sum_coe_sort Q (fun q : ℕ+ => g q / ((N : ℝ)+16*((q : ℕ) : ℝ)*z))
  rwa [hsum] at hfinal

end WeightedSieve


namespace WeightedSieve

theorem pair_weight_nonneg (q : ℕ+) (d : ℕ) (hd : 2 ∣ d) :
    0 ≤ ∏ p ∈ (q : ℕ).primeFactors,
      if p ∣ d then 1 / ((p : ℝ)-1) else 2 / ((p : ℝ)-2) := by
  apply Finset.prod_nonneg
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hp2 : 2 ≤ p := hprime.two_le
  split_ifs with hpd
  · have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    exact div_nonneg (by norm_num) (by linarith)
  · have hne : p ≠ 2 := by intro h; subst p; exact hpd hd
    have hp3 : (2 : ℝ) < p := by exact_mod_cast (by omega : 2 < p)
    exact div_nonneg (by norm_num) (by linarith)



theorem pair_weighted_sifted_generic
    (hLS : ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (N : ℕ) (θ δ : ι → ℝ) (a : ℕ → ℂ),
      (∀ r, 0 < δ r) → (∀ r, δ r ≤ 1) →
      (∀ r s, r ≠ s → ∀ m : ℤ, δ r ≤ |θ r-θ s+m|) →
      (∑ r, ‖∑ n ∈ Finset.range N,
        a n * Complex.exp (2*(Real.pi : ℂ)*Complex.I*(n : ℂ)*(θ r : ℂ))‖^2 /
        ((N : ℝ)+16/δ r)) ≤ ∑ n ∈ Finset.range N, ‖a n‖^2)
    (hPrimitive : ∀ (q : ℕ+) (d : ℕ), Squarefree (q : ℕ) → 2 ∣ d →
      ∀ (A : Finset ℕ), (∀ n ∈ A, ∀ p ∈ (q : ℕ).primeFactors, ¬ p ∣ n*(n+d)) →
      (∏ p ∈ (q : ℕ).primeFactors,
        if p ∣ d then 1 / ((p : ℝ)-1) else 2 / ((p : ℝ)-2)) * (A.card : ℝ)^2 ≤
        ∑ u : (ZMod (q : ℕ))ˣ, ‖∑ n ∈ A, unitFourier q u n‖^2)
    (Q : Finset ℕ+) (h1 : 1 ∈ Q) (N d : ℕ) (z : ℝ) (hz : 1 ≤ z)
    (hQ : ∀ q ∈ Q, Squarefree (q : ℕ) ∧ ((q : ℕ) : ℝ) ≤ z)
    (hd : 2 ∣ d) (A : Finset ℕ) (hAN : A ⊆ Finset.range N)
    (hA : ∀ q ∈ Q, ∀ n ∈ A, ∀ p ∈ (q : ℕ).primeFactors, ¬ p ∣ n*(n+d)) :
    (A.card : ℝ) ≤ (∑ q ∈ Q,
      (∏ p ∈ (q : ℕ).primeFactors,
        if p ∣ d then 1 / ((p : ℝ)-1) else 2 / ((p : ℝ)-2)) /
      ((N : ℝ)+16*((q : ℕ) : ℝ)*z))⁻¹ := by
  classical
  let g (q : ℕ+) : ℝ := ∏ p ∈ (q : ℕ).primeFactors,
    if p ∣ d then 1 / ((p : ℝ)-1) else 2 / ((p : ℝ)-2)
  have hu := WeightedFourier.unit_frequency_weighted_upper hLS Q N z hz
    (fun q hq => (hQ q hq).2) (fun n => if n ∈ A then (1 : ℂ) else 0)
  change (∑ q : Q, ∑ u : (ZMod (q.val : ℕ))ˣ,
    ‖∑ n ∈ Finset.range N, (if n ∈ A then (1 : ℂ) else 0)*unitFourier q.val u n‖^2 /
    ((N : ℝ)+16*((q.val : ℕ) : ℝ)*z)) ≤
    ∑ n ∈ Finset.range N, ‖if n ∈ A then (1 : ℂ) else 0‖^2 at hu
  simp_rw [indicator_fourier N A hAN] at hu
  rw [indicator_mass N A hAN] at hu
  exact count_le_reciprocal_of_energy Q h1 N z hz A g
    (fun q _ => pair_weight_nonneg q d hd) (by simp [g]) hu
    (fun q hq => hPrimitive q d (hQ q hq).1 hd A (hA q hq))

end WeightedSieve

theorem solution
    (Q : Finset ℕ+) (h1 : 1 ∈ Q) (N d : ℕ) (z : ℝ) (hz : 1 ≤ z)
    (hQ : ∀ q ∈ Q, Squarefree (q : ℕ) ∧ ((q : ℕ) : ℝ) ≤ z)
    (hd : 2 ∣ d) (A : Finset ℕ) (hAN : A ⊆ Finset.range N)
    (hA : ∀ q ∈ Q, ∀ n ∈ A, ∀ p ∈ (q : ℕ).primeFactors, ¬ p ∣ n*(n+d)) :
    (A.card : ℝ) ≤ (∑ q ∈ Q,
      (∏ p ∈ (q : ℕ).primeFactors,
        if p ∣ d then 1 / ((p : ℝ)-1) else 2 / ((p : ℝ)-2)) /
      ((N : ℝ)+16*((q : ℕ) : ℝ)*z))⁻¹ := by
  classical
  apply WeightedSieve.pair_weighted_sifted_generic
    (fun ι _ _ N θ δ a hpos hunit hgap =>
      WeightedHilbert_nonuniform_large_sieve_sixteen N θ δ a hpos hunit hgap)
    ?_ Q h1 N d z hz hQ hd A hAN hA
  intro q d hsq hd A havoid
  have h := PrimePairSieve_squarefree_primitive_fourier_energy
    (q : ℕ) d hsq hd A havoid
  have he (u : (ZMod (q : ℕ))ˣ) (n : ℕ) :
      ZMod.stdAddChar (u.val*(n : ZMod (q : ℕ))) = WeightedSieve.unitFourier q u n := by
    apply WeightedSieve.char_unitFraction q u n ZMod.stdAddChar
    intro m
    simpa only [Int.cast_natCast] using ZMod.stdAddChar_coe (N := (q : ℕ)) (m : ℤ)
  simpa only [he] using h
