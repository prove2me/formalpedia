-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.coloring_vertex_density_mixture
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:36:11.308211+00:00
-- url     : https://prove2.me/submissions/afcf23e3-ccad-4cef-aec6-8052e907080e

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
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



theorem solution (q d : ℕ) (hq : 3 ≤ q) (xs : Fin d → Fin q → ℝ)
    (hs : ∀ j, (∑ i, xs j i) = 1) :
    vertexFactor (.potts q) 0 d xs =
      (q:ℝ)⁻¹ * ∑ i : Fin q, ∏ j : Fin d, (q:ℝ)*(1-xs j i)/((q:ℝ)-1) := by
  have hq' : (3:ℝ) ≤ q := by exact_mod_cast hq
  have hqn : (q:ℝ) ≠ 0 := by linarith
  have ht : (q:ℝ)-1+(0:ℝ) ≠ 0 := by linarith
  have hden : (q:ℝ)-1 ≠ 0 := by linarith
  have hm (j : Fin d) (i : Fin q) : Mmul (.potts q) 0 (xs j) i =
      (q:ℝ)*(1-xs j i)/((q:ℝ)-1) := by
    rw [potts_Mmul_centered q (by omega) 0 (by norm_num) (xs j) (hs j)]
    field_simp [hden]
    <;> ring
  unfold vertexFactor
  change (∑ i : Fin q, Model.pi (.potts q) (0:ℝ) i * ∏ j : Fin d, Mmul (.potts q) 0 (xs j) i) = _
  simp_rw [potts_pi_real q 0 _ hqn ht, hm, ← Finset.mul_sum]
