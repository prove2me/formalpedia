-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.potts_contraction_data
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:41:43.901248+00:00
-- url     : https://prove2.me/submissions/b56f0aaa-df8c-4bc6-b15f-7d3bff055a51

import Mathlib
import Theorems.Thm_ZeroFreeRRG_Hardcore_cavity_affine_nontrivial
import Theorems.Thm_ZeroFreeRRG_Hardcore_cavity_affine_transport
import Theorems.Thm_ZeroFreeRRG_Hardcore_potts_affine_factors
set_option backward.isDefEq.respectTransparency.types false
open scoped Classical BigOperators
open MeasureTheory ZeroFreeRRG.Hardcore

/-- The ratio of two antiferromagnetic Potts eigenvalues is a strict contraction. -/
private theorem potts_scalar (q : ℕ) (hq : 2 ≤ q) (β β' : ℝ) (hb' : 0 ≤ β')
    (hlt : β' < β) (hb : β < 1) :
    let κ := (β-1)/((q:ℝ)-1+β)
    let κ' := (β'-1)/((q:ℝ)-1+β')
    0 < κ/κ' ∧ κ/κ' < 1 ∧ (κ/κ')*κ' = κ := by
  dsimp only
  have hq' : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hb0 : 0 ≤ β := by linarith
  have hb'1 : β' < 1 := by linarith
  have hden : 0 < (q:ℝ)-1+β := by linarith
  have hden' : 0 < (q:ℝ)-1+β' := by linarith
  have hn : (β-1)/((q:ℝ)-1+β) < 0 := div_neg_of_neg_of_pos (by linarith) hden
  have hn' : (β'-1)/((q:ℝ)-1+β') < 0 := div_neg_of_neg_of_pos (by linarith) hden'
  have hltκ : (β'-1)/((q:ℝ)-1+β') < (β-1)/((q:ℝ)-1+β) := by
    apply (div_lt_div_iff₀ hden' hden).2
    have hqpos : (0:ℝ) < q := by linarith
    nlinarith [mul_pos (sub_pos.mpr hlt) hqpos]
  refine ⟨div_pos_of_neg_of_neg hn hn', ?_, div_mul_cancel₀ _ (ne_of_lt hn')⟩
  apply (div_lt_one_of_neg hn').2
  exact hltκ

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


theorem solution (q d : ℕ) (hq : 2 ≤ q) (β β' : ℝ)
    (hb' : 0 ≤ β') (hlt : β' < β) (hb : β < 1)
    (ν : ProbabilityMeasure ((.potts q : Model).Spin → ℝ)) (hν : ν ∈ cavityLaws (.potts q) β) :
    let c := ((β-1)/((q:ℝ)-1+β)) / ((β'-1)/((q:ℝ)-1+β'))
    0 < c ∧ c < 1 ∧ ∃ ν' ∈ cavityLaws (.potts q) β',
      (ν ≠ diracPi (.potts q) β → ν' ≠ diracPi (.potts q) β') ∧
      (ν' : Measure ((.potts q : Model).Spin → ℝ)) =
        Measure.map (fun μ : ((.potts q : Model).Spin → ℝ) => fun i : (.potts q : Model).Spin => (1-c)*(q:ℝ)⁻¹+c*μ i)
          (ν : Measure ((.potts q : Model).Spin → ℝ)) ∧
      (∀ (μs : Fin d → Fin q → ℝ), (∀ r, (∑ i, μs r i) = 1) →
        vertexFactor (.potts q) β' d (fun r j => (1-c)*(q:ℝ)⁻¹+c*μs r j) =
          vertexFactor (.potts q) β d μs) ∧
      (∀ (μ ξ : Fin q → ℝ), (∑ i, μ i) = 1 → (∑ i, ξ i) = 1 →
        edgeFactor (.potts q) β'
          (fun i => (1-c)*(q:ℝ)⁻¹+c*μ i) (fun i => (1-c)*(q:ℝ)⁻¹+c*ξ i) =
          1-c+c*edgeFactor (.potts q) β μ ξ) := by
  classical
  dsimp only
  let c : ℝ := ((β-1)/((q:ℝ)-1+β)) / ((β'-1)/((q:ℝ)-1+β'))
  have hc := potts_scalar q hq β β' hb' hlt hb
  have hc0 : 0 < c := hc.1
  have hc1 : c < 1 := hc.2.1
  have hk : c*((β'-1)/((q:ℝ)-1+β')) = (β-1)/((q:ℝ)-1+β) := hc.2.2
  have hq' : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hqn : (q:ℝ) ≠ 0 := by linarith
  have hb0 : 0 ≤ β := by linarith
  have ht : (q:ℝ)-1+β ≠ 0 := by linarith
  have ht' : (q:ℝ)-1+β' ≠ 0 := by linarith
  let r : Fin q → ℝ := fun _ => (q:ℝ)⁻¹
  have hr : r ∈ stdSimplex ℝ (Fin q) := by
    constructor
    · intro i
      dsimp [r]
      positivity
    · change (∑ _i : Fin q, (q:ℝ)⁻¹) = 1
      simp [hqn]
  have hmean : ∀ i : Fin q, Model.pi (.potts q) β' i = (1-c)*r i+c*Model.pi (.potts q) β i := by
    intro i
    rw [potts_pi_real q β' i hqn ht',potts_pi_real q β i hqn ht]
    dsimp [r]
    ring
  obtain ⟨ν',hν',hmap⟩ := cavity_affine_transport (.potts q) β β' ν hν r hr c hc0.le hc1.le hmean
  refine ⟨hc0,hc1,ν',hν',?_,?_,?_,?_⟩
  · intro hne
    obtain ⟨ξ,hξ,hξne,hξmap⟩ := cavity_affine_nontrivial (.potts q) β β' ν hν r hr c hc0.le hc1.le (ne_of_gt hc0) hmean hne
    have heq : ν' = ξ := by
      apply ProbabilityMeasure.toMeasure_injective
      exact hmap.trans hξmap.symm
    simpa [heq] using hξne
  · simpa [r] using hmap
  · intro μs hμs
    exact (potts_affine_factors q d hq β β' c hb0 hb' hk μs hμs
      (fun _ => (q:ℝ)⁻¹) (fun _ => (q:ℝ)⁻¹) (by simp [hqn]) (by simp [hqn])).1
  · intro μ ξ hμ hξ
    exact (potts_affine_factors q d hq β β' c hb0 hb' hk (fun _ => μ) (fun _ => hμ)
      μ ξ hμ hξ).2
