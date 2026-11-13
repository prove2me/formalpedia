-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.potts_edge_nonconstant
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:57:16.763811+00:00
-- url     : https://prove2.me/submissions/c5d5b582-7657-4890-97f4-ada0d35d717a

import Theorems.Thm_ZeroFreeRRG_Hardcore_potts_edge_properties
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


private theorem edge_eq_sum_Mmul (q : ℕ) (β : ℝ) (μ ν : Fin q → ℝ) :
    edgeFactor (.potts q) β μ ν = ∑ i : Fin q, μ i * Mmul (.potts q) β ν i := by
  unfold edgeFactor Mmul
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring


open MeasureTheory Set

/-- A continuous kernel that vanishes almost surely under two independent copies
also vanishes on the diagonal almost surely. -/
private theorem ae_diagonal {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] (μ : Measure X)
    [IsFiniteMeasure μ] (F : X × X → ℝ) (hF : Continuous F)
    (hprod : ∀ᵐ p ∂(μ.prod μ), F p = 0) :
    ∀ᵐ x ∂μ, F (x,x) = 0 := by
  have hset : MeasurableSet {p : X × X | F p = 0} :=
    (isClosed_eq hF continuous_const).measurableSet
  have hxy : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, F (x,y) = 0 :=
    (Measure.ae_prod_iff_ae_ae hset).1 hprod
  have hx : ∀ᵐ x ∂μ, ∀ y ∈ μ.support, F (x,y) = 0 := by
    filter_upwards [hxy] with x hx
    intro y hy
    apply μ.support_subset_of_isClosed _ hx hy
    exact isClosed_eq (hF.comp (continuous_const.prodMk continuous_id)) continuous_const
  have hall : ∀ x ∈ μ.support, ∀ y ∈ μ.support, F (x,y) = 0 := by
    intro x hsx y hsy
    have hy : ∀ᵐ x ∂μ, F (x,y) = 0 := by
      filter_upwards [hx] with x hx
      exact hx y hsy
    apply μ.support_subset_of_isClosed _ hy hsx
    exact isClosed_eq (hF.comp (continuous_id.prodMk continuous_const)) continuous_const
  filter_upwards [μ.support_mem_ae] with x hx
  exact hall x hx x hx

private theorem diagonal_edge (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hb : 0 ≤ β)
    (μ : Fin q → ℝ) (hμ : (∑ i, μ i) = 1) :
    edgeFactor (.potts q) β μ μ =
      1 + (q:ℝ)*((β-1)/((q:ℝ)-1+β))* ∑ i, (μ i-(q:ℝ)⁻¹)^2 := by
  have hq' : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hqn : (q:ℝ) ≠ 0 := by linarith
  rw [edge_eq_sum_Mmul]
  simp_rw [potts_Mmul_centered q hq β hb μ hμ]
  have hs : (∑ i : Fin q, μ i * (μ i-(q:ℝ)⁻¹)) =
      ∑ i : Fin q, (μ i-(q:ℝ)⁻¹)^2 := by
    have hz : (∑ i : Fin q, (μ i-(q:ℝ)⁻¹)) = 0 := by
      simp only [Finset.sum_sub_distrib, hμ, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      field_simp
      <;> ring
    calc
      _ = (∑ i : Fin q, ((μ i-(q:ℝ)⁻¹)^2 + (q:ℝ)⁻¹*(μ i-(q:ℝ)⁻¹))) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, hz]; simp
  calc
    _ = (∑ i : Fin q, μ i) + (q:ℝ)*((β-1)/((q:ℝ)-1+β))*
        ∑ i : Fin q, μ i*(μ i-(q:ℝ)⁻¹) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by rw [hμ,hs]

theorem solution (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hb0 : 0 ≤ β) (hb1 : β < 1)
    (ν : ProbabilityMeasure (Fin q → ℝ)) (hν : ν ∈ cavityLaws (.potts q) β)
    (hne : ν ≠ diracPi (.potts q) β) :
    0 < ((ν : Measure (Fin q → ℝ)).prod (ν : Measure (Fin q → ℝ)))
      {p | 0 ≤ edgeFactor (.potts q) β p.1 p.2 ∧ edgeFactor (.potts q) β p.1 p.2 ≠ 1} := by
  classical
  let μ : Measure (Fin q → ℝ) := ν
  let U : Fin q → ℝ := fun _ => (q:ℝ)⁻¹
  have hq' : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hqn : (q:ℝ) ≠ 0 := by linarith
  have ht : (q:ℝ)-1+β ≠ 0 := by linarith
  have hk : (q:ℝ)*((β-1)/((q:ℝ)-1+β)) ≠ 0 :=
    mul_ne_zero hqn (div_ne_zero (by linarith) ht)
  have hsimplex : ∀ᵐ x ∂μ, x ∈ stdSimplex ℝ (Fin q) := ae_iff.mpr hν.1
  have hedgenonneg : ∀ᵐ p ∂μ.prod μ, 0 ≤ edgeFactor (.potts q) β p.1 p.2 := by
    have hp := potts_edge_properties q hq β 0 hb0 ν hν
    exact hp.2.1
  by_contra hn
  have hz : μ.prod μ {p | 0 ≤ edgeFactor (.potts q) β p.1 p.2 ∧
      edgeFactor (.potts q) β p.1 p.2 ≠ 1} = 0 := le_antisymm (not_lt.mp hn) bot_le
  have hae : ∀ᵐ p ∂μ.prod μ, edgeFactor (.potts q) β p.1 p.2 = 1 := by
    have h : ∀ᵐ p ∂μ.prod μ, ¬(0 ≤ edgeFactor (.potts q) β p.1 p.2 ∧
        edgeFactor (.potts q) β p.1 p.2 ≠ 1) := ae_iff.mpr (by simpa only [not_not] using hz)
    filter_upwards [h,hedgenonneg] with p hp hnonneg
    by_contra hne'
    exact hp ⟨hnonneg,hne'⟩
  have hcont : Continuous (fun p : (Fin q → ℝ) × (Fin q → ℝ) =>
      edgeFactor (.potts q) β p.1 p.2 - 1) := by
    unfold edgeFactor
    fun_prop
  have hdiag : ∀ᵐ x ∂μ, edgeFactor (.potts q) β x x = 1 := by
    have hd := ae_diagonal μ _ hcont (by filter_upwards [hae] with p hp; simp [hp])
    filter_upwards [hd] with x hx
    change edgeFactor (.potts q) β x x - 1 = 0 at hx
    linarith
  have hu : ∀ᵐ x ∂μ, x = U := by
    filter_upwards [hdiag,hsimplex] with x hx hs
    change edgeFactor (.potts q) β x x = 1 at hx
    have hsum : (∑ i, x i) = 1 := hs.2
    have hd := diagonal_edge q hq β hb0 x hsum
    have hzero : (∑ i : Fin q, (x i - (q:ℝ)⁻¹)^2) = 0 := by
      have : (q:ℝ)*((β-1)/((q:ℝ)-1+β))*
          (∑ i : Fin q, (x i - (q:ℝ)⁻¹)^2) = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left hk
    funext i
    have hi : (x i - (q:ℝ)⁻¹)^2 = 0 := by
      apply Finset.sum_eq_zero_iff_of_nonneg (fun i hi => sq_nonneg _ ) |>.mp hzero i
      exact Finset.mem_univ i
    dsimp [U]
    nlinarith [sq_nonneg (x i - (q:ℝ)⁻¹)]
  apply hne
  apply ProbabilityMeasure.toMeasure_injective
  change μ = Measure.dirac (Model.pi (.potts q) β)
  have hpi : Model.pi (.potts q) β = U := by
    funext i
    exact potts_pi_real q β i hqn ht
  rw [hpi]
  calc
    μ = Measure.map id μ := Measure.map_id.symm
    _ = Measure.map (fun _ => U) μ := Measure.map_congr hu
    _ = Measure.dirac U := by simp
