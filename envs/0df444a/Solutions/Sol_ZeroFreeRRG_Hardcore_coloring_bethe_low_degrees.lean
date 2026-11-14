-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.coloring_bethe_low_degrees
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:12:34.872233+00:00
-- url     : https://prove2.me/submissions/5c9f92b8-2292-445a-a6c0-62f51c652424

import Theorems.Thm_ZeroFreeRRG_Hardcore_potts_edge_properties
import Theorems.Thm_ZeroFreeRRG_Hardcore_potts_edge_nonconstant
import Theorems.Thm_ZeroFreeRRG_Hardcore_entropy_positive_mean_one
import Mathlib
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open scoped Classical BigOperators
open ZeroFreeRRG.Hardcore

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

private theorem vertex_one (q : ℕ) (hq : 2 ≤ q) (x : Fin q → ℝ)
    (hx : (∑ i, x i)=1) : vertexFactor (.potts q) 0 1 (fun _ => x) = 1 := by
  have hq' : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hqn : (q:ℝ) ≠ 0 := by linarith
  have ht : (q:ℝ)-1+(0:ℝ) ≠ 0 := by linarith
  unfold vertexFactor
  change (∑ i : Fin q, Model.pi (.potts q) (0:ℝ) i *
    ∏ _j : Fin 1, Mmul (.potts q) 0 x i) = 1
  simp only [Fin.prod_univ_one, potts_pi_real q 0 _ hqn ht, ← Finset.mul_sum]
  rw [potts_Mmul_sum q hq 0 (by norm_num) x hx]
  field_simp

theorem solution (q : ℕ) (hq : 2 ≤ q)
    (ν : ProbabilityMeasure ((.potts q : Model).Spin → ℝ))
    (hν : ν ∈ cavityLaws (.potts q) 0) (hne : ν ≠ diracPi (.potts q) 0) :
    betheR (.potts q) 0 0 ν = 0 ∧ betheR (.potts q) 0 1 ν < 0 := by
  change ProbabilityMeasure (Fin q → ℝ) at ν
  have hs : ∀ᵐ x ∂(ν : Measure (Fin q → ℝ)), x ∈ stdSimplex ℝ (Fin q) := ae_iff.mpr hν.1
  have hpi : ∀ᵐ xs ∂(Measure.pi fun _ : Fin 1 => (ν : Measure (Fin q → ℝ))),
      xs 0 ∈ stdSimplex ℝ (Fin q) := by
    have h := Measure.ae_pi_le_pi (Filter.eventually_pi (fun _ : Fin 1 => hs))
    filter_upwards [h] with xs hx
    exact hx 0
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
  have hv1 : (∫ xs, xlogx (vertexFactor (.potts q) 0 1 xs)
      ∂(Measure.pi fun _ : Fin 1 => (ν : Measure (Fin q → ℝ)))) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hpi] with xs hxs
    have heq : xs = (fun _ => xs 0) := by funext i; fin_cases i; rfl
    rw [heq, vertex_one q hq _ hxs.2]
    simp [xlogx]
  obtain ⟨hm,hE,hI,hEnt,hEntC⟩ := potts_edge_properties q hq 0 0 (by norm_num) ν hν
  have hp := potts_edge_nonconstant q hq 0 (by norm_num) (by norm_num) ν hν hne
  have he := entropy_positive_mean_one ((ν : Measure (Fin q → ℝ)).prod (ν : Measure (Fin q → ℝ)))
      (fun p : (Fin q → ℝ) × (Fin q → ℝ) => edgeFactor (.potts q) 0 p.1 p.2) hE hI hEnt hm hp
  constructor
  · simp only [betheR, Nat.floor_zero, Nat.cast_zero, sub_zero, add_zero, one_mul, zero_mul, add_zero]
    unfold betheK
    simp only [Nat.cast_zero, zero_div, zero_mul, sub_zero]
    exact hv0
  · simp only [betheR, Nat.floor_one, Nat.cast_one, sub_self, add_zero, zero_mul,
      one_mul, zero_add, Nat.cast_zero, Nat.zero_add]
    unfold betheK
    simp only [Nat.cast_one]
    change (∫ xs : Fin 1 → Fin q → ℝ, xlogx (vertexFactor (.potts q) 0 1 xs)
      ∂(Measure.pi fun _ : Fin 1 => (ν : Measure (Fin q → ℝ)))) - (1:ℝ)/2 *
      (∫ p : (Fin q → ℝ) × (Fin q → ℝ), xlogx (edgeFactor (.potts q) 0 p.1 p.2)
        ∂((ν : Measure (Fin q → ℝ)).prod ν)) < 0
    rw [hv1]
    linarith
