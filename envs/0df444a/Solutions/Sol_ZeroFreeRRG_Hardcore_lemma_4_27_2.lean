-- Prove2me | solution 2 for ZeroFreeRRG.Hardcore.lemma_4_27
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:31:30.77488+00:00
-- url     : https://prove2.me/submissions/e5a38bdc-dbd8-4acd-8a02-40c6c5c1e841

import Theorems.Thm_ZeroFreeRRG_Hardcore_coloring_bethe_degree_convexity
import Theorems.Thm_ZeroFreeRRG_Hardcore_coloring_real_degree_weak_KS
import Theorems.Thm_ZeroFreeRRG_Hardcore_coloring_strictness_from_degree_convexity
import Theorems.Thm_ZeroFreeRRG_Hardcore_coloring_bethe_low_degrees
import Mathlib
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open scoped Classical BigOperators
open MeasureTheory Set ZeroFreeRRG.Hardcore
private lemma potts_pi_real (q : ℕ) (β : ℝ) (i : Fin q)
    (hq : (q:ℝ) ≠ 0) (ht : (q:ℝ) - 1 + β ≠ 0) :
    Model.pi (.potts q) β i = (q:ℝ)⁻¹ := by
  unfold Model.pi Model.P
  change (∑ j : Fin q, ((1:ℝ) + if i = j then β - 1 else 0) /
      ((q:ℝ) * ((q:ℝ) - 1 + β))) = (q:ℝ)⁻¹
  rw [← Finset.sum_div]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hs : (∑ j : Fin q, if i = j then β - 1 else 0) = β - 1 := by simp
  rw [hs]
  field_simp
  ring

private lemma potts_M_formula (q : ℕ) (β : ℝ) (i j : Fin q)
    (hq : (q:ℝ) ≠ 0) (ht : (q:ℝ) - 1 + β ≠ 0) :
    Model.M (.potts q) β i j = (q:ℝ) * ((1:ℝ) + if i=j then β-1 else 0) /
      ((q:ℝ)-1+β) := by
  unfold Model.M
  rw [potts_pi_real q β i hq ht, potts_pi_real q β j hq ht]
  change (((1:ℝ) + if i=j then β-1 else 0) / ((q:ℝ)*((q:ℝ)-1+β))) /
    ((q:ℝ)⁻¹*(q:ℝ)⁻¹) = _
  field_simp

/-- The Potts interaction on a probability vector in centered form. -/
theorem potts_Mmul_centered (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hb : 0 ≤ β)
    (μ : Fin q → ℝ) (hμ : (∑ i, μ i) = 1) (i : Fin q) :
    Mmul (.potts q) β μ i = 1 + (q:ℝ)*((β-1)/((q:ℝ)-1+β))*(μ i-(q:ℝ)⁻¹) := by
  have hq' : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hqn : (q:ℝ) ≠ 0 := by linarith
  have ht : (q:ℝ) - 1 + β ≠ 0 := by linarith
  unfold Mmul
  change (∑ j : Fin q, Model.M (.potts q) β i j * μ j) = _
  simp_rw [potts_M_formula q β i _ hqn ht, div_mul_eq_mul_div, ← Finset.sum_div]
  have hsum : (∑ j : Fin q, (q:ℝ) * ((1:ℝ) + if i=j then β-1 else 0) * μ j) =
      (q:ℝ)*(1+(β-1)*μ i) := by
    have hh : (∑ j : Fin q, (if i=j then β-1 else 0) * μ j) = (β-1)*μ i := by simp
    calc
      _ = (q:ℝ) * ∑ j : Fin q, (((1:ℝ) + if i=j then β-1 else 0) * μ j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by simp only [add_mul, one_mul, Finset.sum_add_distrib]; rw [hμ,hh]
  rw [hsum]
  field_simp
  <;> ring

/-- The centered Potts interaction is invariant under matched message contraction. -/
theorem potts_Mmul_affine (q : ℕ) (hq : 2 ≤ q) (β β' c : ℝ)
    (hb : 0 ≤ β) (hb' : 0 ≤ β')
    (hk : c*((β'-1)/((q:ℝ)-1+β')) = (β-1)/((q:ℝ)-1+β))
    (μ : Fin q → ℝ) (hμ : (∑ i, μ i) = 1) (i : Fin q) :
    Mmul (.potts q) β' (fun j => (1-c)*(q:ℝ)⁻¹+c*μ j) i =
      Mmul (.potts q) β μ i := by
  have hq' : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hqn : (q:ℝ) ≠ 0 := by linarith
  have hs : (∑ j : Fin q, ((1-c)*(q:ℝ)⁻¹+c*μ j)) = 1 := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum, hμ]
    field_simp
    <;> ring
  have h1 := potts_Mmul_centered q hq β' hb' (fun j : Fin q => (1-c)*(q:ℝ)⁻¹+c*μ j) hs i
  have h2 := potts_Mmul_centered q hq β hb μ hμ i
  have hp : (1-c)*(q:ℝ)⁻¹+c*μ i-(q:ℝ)⁻¹ = c*(μ i-(q:ℝ)⁻¹) := by ring
  have h3 : 1+(q:ℝ)*((β'-1)/((q:ℝ)-1+β'))*((1-c)*(q:ℝ)⁻¹+c*μ i-(q:ℝ)⁻¹) =
      1+(q:ℝ)*((β-1)/((q:ℝ)-1+β))*(μ i-(q:ℝ)⁻¹) := by
    rw [hp]
    have hx := congrArg (fun z : ℝ => (q:ℝ)*z*(μ i-(q:ℝ)⁻¹)) hk
    nlinarith [hx]
  exact h1.trans (h3.trans h2.symm)

/-- The Potts vertex factor is unchanged by the source's matched contraction. -/
theorem potts_vertex_affine (q d : ℕ) (hq : 2 ≤ q) (β β' c : ℝ)
    (hb : 0 ≤ β) (hb' : 0 ≤ β')
    (hk : c*((β'-1)/((q:ℝ)-1+β')) = (β-1)/((q:ℝ)-1+β))
    (μs : Fin d → Fin q → ℝ) (hμ : ∀ r, (∑ i, μs r i) = 1) :
    vertexFactor (.potts q) β' d (fun r j => (1-c)*(q:ℝ)⁻¹+c*μs r j) =
      vertexFactor (.potts q) β d μs := by
  have hq' : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hqn : (q:ℝ) ≠ 0 := by linarith
  have ht : (q:ℝ) - 1 + β ≠ 0 := by linarith
  have ht' : (q:ℝ) - 1 + β' ≠ 0 := by linarith
  unfold vertexFactor
  apply Finset.sum_congr rfl
  intro i hi
  rw [potts_pi_real q β' i hqn ht',potts_pi_real q β i hqn ht]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  exact potts_Mmul_affine q hq β β' c hb hb' hk (μs j) (hμ j) i

private theorem potts_Mmul_sum (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hb : 0 ≤ β)
    (μ : Fin q → ℝ) (hμ : (∑ i, μ i) = 1) :
    (∑ i : Fin q, Mmul (.potts q) β μ i) = q := by
  have hq' : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hqn : (q:ℝ) ≠ 0 := by linarith
  simp_rw [potts_Mmul_centered q hq β hb μ hμ]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, ← Finset.mul_sum, Finset.sum_sub_distrib, hμ]
  field_simp
  <;> ring


open MeasureTheory

private theorem vertex_zero (q : ℕ) (hq : 2 ≤ q) :
    vertexFactor (.potts q) 0 0 (fun i => Fin.elim0 i) = 1 := by
  have hq' : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hqn : (q:ℝ) ≠ 0 := by linarith
  have ht : (q:ℝ)-1+(0:ℝ) ≠ 0 := by linarith
  unfold vertexFactor
  simp only [Finset.prod_empty, Finset.univ_eq_empty, mul_one]
  change (∑ i : Fin q, Model.pi (.potts q) (0:ℝ) i) = 1
  simp [potts_pi_real q 0 _ hqn ht, hqn]


namespace ZeroFreeRRG.Hardcore
private lemma potts_pi (q : ℕ) (β : ℂ) (i : Fin q)
    (hq : (q:ℂ) ≠ 0) (ht : (q:ℂ) - 1 + β ≠ 0) :
    Model.pi (.potts q) β i = (q:ℂ)⁻¹ := by
  unfold Model.pi Model.P
  change (∑ j : Fin q, ((1:ℂ) + if i = j then β - 1 else 0) /
      ((q:ℂ) * ((q:ℂ) - 1 + β))) = (q:ℂ)⁻¹
  rw [← Finset.sum_div]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hs : (∑ j : Fin q, if i = j then β - 1 else 0) = β - 1 := by simp
  rw [hs]
  field_simp
  ring
end ZeroFreeRRG.Hardcore
namespace ZeroFreeRRG.Hardcore
private lemma potts_K (q : ℕ) (β : ℂ) (i j : Fin q)
    (hq : (q:ℂ) ≠ 0) (ht : (q:ℂ) - 1 + β ≠ 0) :
    Model.K (.potts q) β i j = ((1:ℂ) + if i = j then β - 1 else 0) /
      ((q:ℂ) - 1 + β) := by
  change Model.P (.potts q) β i j / Model.pi (.potts q) β i = _
  rw [potts_pi q β i hq ht]
  change (((1:ℂ) + if i = j then β - 1 else 0) /
      ((q:ℂ) * ((q:ℂ) - 1 + β))) / (q:ℂ)⁻¹ = _
  field_simp

private lemma potts_eigenvalue (q : ℕ) (β : ℂ) (hq : (q:ℂ) ≠ 0)
    (ht : (q:ℂ) - 1 + β ≠ 0) (κ : ℂ)
    (hκ : κ ∈ Model.nonconstEig (.potts q) β) :
    κ = (β - 1) / ((q:ℂ) - 1 + β) := by
  obtain ⟨f, hf, hmean, hvec⟩ := hκ
  change Fin q → ℂ at f
  change (∑ i : Fin q, Model.pi (.potts q) β i * f i) = 0 at hmean
  have hsum : (∑ i : Fin q, f i) = 0 := by
    simp only [potts_pi q β _ hq ht, ← Finset.mul_sum] at hmean
    exact (mul_eq_zero.mp hmean).resolve_left (inv_ne_zero hq)
  have hpoint : ∀ i : Fin q, ((Model.K (.potts q) β).mulVec f) i =
      ((β - 1) / ((q:ℂ) - 1 + β)) * f i := by
    intro i
    change (∑ j : Fin q, Model.K (.potts q) β i j * f j) = _
    simp only [potts_K q β i _ hq ht, div_mul_eq_mul_div, ← Finset.sum_div]
    congr 1
    have hid : (∑ j : Fin q, ((1:ℂ) + if i = j then β - 1 else 0) * f j) =
        (β - 1) * f i := by
      simp only [add_mul, one_mul, Finset.sum_add_distrib]
      rw [hsum, zero_add]
      simp
    rw [hid]
  obtain ⟨i, hi⟩ : ∃ i : Fin q, f i ≠ 0 := by
    by_contra h
    push Not at h
    apply hf
    funext i
    exact h i
  have hi' := congrFun hvec i
  rw [hpoint i] at hi'
  change ((β - 1) / ((q:ℂ) - 1 + β)) * f i = κ * f i at hi'
  exact (mul_right_cancel₀ hi (hi'.symm))
end ZeroFreeRRG.Hardcore


private theorem betheR_zero (q : ℕ) (hq : 2 ≤ q)
    (ν : ProbabilityMeasure ((.potts q : Model).Spin → ℝ)) :
    betheR (.potts q) 0 0 ν = 0 := by
  change ProbabilityMeasure (Fin q → ℝ) at ν
  have hv0 : (∫ xs, xlogx (vertexFactor (.potts q) 0 0 xs)
      ∂(Measure.pi fun _ : Fin 0 => (ν : Measure (Fin q → ℝ)))) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards with xs
    have hv : vertexFactor (.potts q) 0 0 xs = 1 := by
      convert vertex_zero q hq using 1
      congr 1
      funext i
      exact Fin.elim0 i
    simp [hv, xlogx]
  simp only [betheR, Nat.floor_zero, Nat.cast_zero, sub_zero, add_zero, one_mul, zero_mul, add_zero]
  unfold betheK
  simp only [Nat.cast_zero, zero_div, zero_mul, sub_zero]
  exact hv0

private theorem degree_monotone (q : ℕ) (hq : 3 ≤ q)
    (ν : ProbabilityMeasure ((.potts q : Model).Spin → ℝ)) (hν : ν ∈ cavityLaws (.potts q) 0)
    (r s : ℝ) (hs : 0 ≤ s) (hsr : s ≤ r) (hr : betheR (.potts q) 0 r ν ≤ 0) :
    betheR (.potts q) 0 s ν ≤ 0 := by
  let f : ℝ → ℝ := fun t => betheR (.potts q) 0 t ν
  have hzero : f 0 = 0 := betheR_zero q (by omega) ν
  have hconv := coloring_bethe_degree_convexity q hq ν hν
  by_cases hr0 : r = 0
  · have hs0 : s=0 := by linarith
    simpa [hs0] using hzero.le
  · have hrpos : 0 < r := lt_of_le_of_ne (le_trans hs hsr) (Ne.symm hr0)
    let b := s/r
    let a := 1-b
    have hb0 : 0 ≤ b := div_nonneg hs (le_of_lt hrpos)
    have hb1 : b ≤ 1 := (div_le_one hrpos).2 hsr
    have ha : 0 ≤ a := sub_nonneg.mpr hb1
    have hab : a+b=1 := by dsimp [a]; ring
    have heq : a*0+b*r=s := by
      dsimp [a,b]
      field_simp
      <;> ring
    have hf := hconv.2 (show (0:ℝ) ∈ Ici 0 by norm_num)
      (show r ∈ Ici 0 from le_of_lt hrpos) ha hb0 hab
    change f (a*0+b*r) ≤ a*f 0+b*f r at hf
    rw [heq,hzero] at hf
    have hle : b*f r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb0 hr
    linarith

theorem solution (d q : ℕ) (hd : 3 ≤ d) (hq : 3 ≤ q) :
    ((∃ r : ℝ, (d : ℝ) < r ∧
      ∀ ν ∈ cavityLaws (.potts q) 0, betheR (.potts q) 0 r ν ≤ 0) →
      Condition1 (.potts q) d 0 ∧ Condition2 (.potts q) d 0) ∧
    (∀ r s : ℝ, 0 ≤ s → s ≤ r →
      (∀ ν ∈ cavityLaws (.potts q) 0, betheR (.potts q) 0 r ν ≤ 0) →
      ∀ ν ∈ cavityLaws (.potts q) 0, betheR (.potts q) 0 s ν ≤ 0) ∧
    (∀ ν ∈ cavityLaws (.potts q) 0, ν ≠ diracPi (.potts q) 0 →
      ConvexOn ℝ (Set.Ici 0) (fun s => betheR (.potts q) 0 s ν) ∧
      betheR (.potts q) 0 0 ν = 0 ∧ betheR (.potts q) 0 1 ν < 0) := by
  have hq' : (3:ℝ) ≤ q := by exact_mod_cast hq
  have hd' : (3:ℝ) ≤ d := by exact_mod_cast hd
  have hqpos : (0:ℝ) < q := by linarith
  have hden : 0 < (q:ℝ)-1 := by linarith
  refine ⟨?_,?_,?_⟩
  · rintro ⟨r,hr,hrs⟩
    have hconv : ∀ ν ∈ cavityLaws (.potts q) 0, ν ≠ diracPi (.potts q) 0 →
        ConvexOn ℝ (Ici 0) (fun s => betheR (.potts q) 0 s ν) :=
      fun ν hν _ => coloring_bethe_degree_convexity q hq ν hν
    have hstrict := coloring_strictness_from_degree_convexity d q hd (by omega) r hr hconv hrs
    have hweak := coloring_real_degree_weak_KS q hq r (by linarith) hrs
    refine ⟨hstrict,?_⟩
    intro κ hκ
    have hcq : (q:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hqpos)
    have hct : (q:ℂ)-1+(0:ℂ) ≠ 0 := by
      simp only [add_zero]
      exact_mod_cast (ne_of_gt hden)
    rw [ZeroFreeRRG.Hardcore.potts_eigenvalue q 0 hcq hct κ hκ]
    have hnorm : ‖((0:ℂ)-1)/((q:ℂ)-1+0)‖ = 1/((q:ℝ)-1) := by
      have hden0 : (q:ℂ)-1+(0:ℂ) = (((q:ℝ)-1:ℝ):ℂ) := by push_cast; simp
      rw [hden0,norm_div,Complex.norm_real]
      simp [Real.norm_eq_abs, abs_of_pos hden]
    rw [hnorm]
    have hp : 0 < (1/((q:ℝ)-1))^2 := sq_pos_of_pos (div_pos zero_lt_one hden)
    nlinarith [mul_pos (sub_pos.mpr hr) hp]
  · intro r s hs hsr hrs ν hν
    exact degree_monotone q hq ν hν r s hs hsr (hrs ν hν)
  · intro ν hν hne
    exact ⟨coloring_bethe_degree_convexity q hq ν hν,
      coloring_bethe_low_degrees q (by omega) ν hν hne⟩
