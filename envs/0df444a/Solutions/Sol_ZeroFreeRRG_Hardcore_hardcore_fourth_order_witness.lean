-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.hardcore_fourth_order_witness
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T04:31:35.14079+00:00
-- url     : https://prove2.me/submissions/cc514e33-7280-4982-ae60-1b46c2104445

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
open scoped Classical ENNReal
open MeasureTheory Set
namespace ZeroFreeRRG.Hardcore

private noncomputable def twoPoint (m : Model) (a b : m.Spin → ℝ) : ProbabilityMeasure (m.Spin → ℝ) :=
  ⟨(1/2:ℝ≥0∞) • Measure.dirac a + (1/2:ℝ≥0∞) • Measure.dirac b, ⟨by simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]; exact ENNReal.add_halves 1⟩⟩

private lemma twoPoint_is_cavity (m : Model) (t : ℝ) (a b : m.Spin → ℝ)
    (ha : a ∈ stdSimplex ℝ m.Spin) (hb : b ∈ stdSimplex ℝ m.Spin)
    (hmeans : ∀ i, (a i + b i)/2 = m.pi t i) : twoPoint m a b ∈ cavityLaws m t := by
  constructor
  · change ((1/2:ℝ≥0∞) • Measure.dirac a + (1/2:ℝ≥0∞) • Measure.dirac b) (stdSimplex ℝ m.Spin)ᶜ = 0
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    have hna : a ∉ (stdSimplex ℝ m.Spin)ᶜ := by simpa using ha
    have hnb : b ∉ (stdSimplex ℝ m.Spin)ᶜ := by simpa using hb
    rw [Measure.dirac_apply, Measure.dirac_apply, Set.indicator_of_notMem hna, Set.indicator_of_notMem hnb]
    simp
  · intro i
    change (∫ x, x i ∂((1/2:ℝ≥0∞) • Measure.dirac a + (1/2:ℝ≥0∞) • Measure.dirac b)) = _
    have hint1 : Integrable (fun x => x i) ((1/2:ℝ≥0∞) • Measure.dirac a) :=
      (integrable_dirac (by simp)).smul_measure (by simp)
    have hint2 : Integrable (fun x => x i) ((1/2:ℝ≥0∞) • Measure.dirac b) :=
      (integrable_dirac (by simp)).smul_measure (by simp)
    rw [integral_add_measure hint1 hint2, integral_smul_measure, integral_smul_measure,
      integral_dirac, integral_dirac]
    simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat, smul_eq_mul]
    linarith [hmeans i]
end ZeroFreeRRG.Hardcore

namespace ZeroFreeRRG.Hardcore
private def hcPoint (α x : ℝ) : Fin 2 → ℝ := ![1-α-x, α+x]

private lemma hc_pi0_real (α : ℝ) : Model.pi .hardcore α (0 : Fin 2) = 1-α := by
  simp [Model.pi, Model.Spin, Model.P, Fin.sum_univ_two] <;> ring
private lemma hc_pi1_real (α : ℝ) : Model.pi .hardcore α (1 : Fin 2) = α := by
  simp [Model.pi, Model.Spin, Model.P, Fin.sum_univ_two]

private lemma hcPoint_simplex (α x : ℝ) (hx1 : |x| ≤ α) (hx2 : |x| ≤ 1-α) :
    hcPoint α x ∈ stdSimplex ℝ (Fin 2) := by
  have hxl : -α ≤ x := (abs_le.mp hx1).1
  have hxu : x ≤ 1-α := (abs_le.mp hx2).2
  constructor
  · intro i
    fin_cases i <;> simp [hcPoint] <;> linarith
  · simp [hcPoint, Fin.sum_univ_two]

private lemma hardcore_symmetric_law (α x : ℝ) (hx1 : |x| ≤ α) (hx2 : |x| ≤ 1-α) :
    twoPoint .hardcore (hcPoint α x) (hcPoint α (-x)) ∈ cavityLaws .hardcore α := by
  apply twoPoint_is_cavity
  · exact hcPoint_simplex α x hx1 hx2
  · apply hcPoint_simplex α (-x)
    · simpa using hx1
    · simpa using hx2
  · intro i
    change (hcPoint α x i + hcPoint α (-x) i)/2 = Model.pi .hardcore α i
    fin_cases i
    · simp [hcPoint, hc_pi0_real]
    · simp [hcPoint, hc_pi1_real]
      ring
end ZeroFreeRRG.Hardcore
namespace ZeroFreeRRG.Hardcore
private lemma hardcore_normalized_two_point_cavity (α : ℝ) (hα : 0 < α) (hα2 : α < 1/2) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      twoPoint .hardcore
        (hcPoint α (ε * Real.sqrt (α*(1-α))))
        (hcPoint α (-(ε * Real.sqrt (α*(1-α))))) ∈ cavityLaws .hardcore α := by
  let s := Real.sqrt (α*(1-α))
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hd : 0 < s+1 := by linarith
  let ε₀ := min (α/(s+1)) ((1-α)/(s+1))
  have hε₀ : 0 < ε₀ := by
    dsimp [ε₀]
    exact lt_min (div_pos hα hd) (div_pos (by linarith) hd)
  refine ⟨ε₀,hε₀,?_⟩
  intro ε hε hε0
  have h1 : ε < α/(s+1) := lt_of_lt_of_le hε0 (min_le_left _ _)
  have h2 : ε < (1-α)/(s+1) := lt_of_lt_of_le hε0 (min_le_right _ _)
  have hm1 : ε*(s+1) < α := (lt_div_iff₀ hd).mp h1
  have hm2 : ε*(s+1) < 1-α := (lt_div_iff₀ hd).mp h2
  apply hardcore_symmetric_law
  · rw [abs_of_nonneg (mul_nonneg hε.le hs)]
    nlinarith
  · rw [abs_of_nonneg (mul_nonneg hε.le hs)]
    nlinarith
end ZeroFreeRRG.Hardcore
namespace ZeroFreeRRG.Hardcore
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

private noncomputable def pottsPoint (q : ℕ) (i j : Fin q) (x : ℝ) : Fin q → ℝ :=
  fun k => (q:ℝ)⁻¹ + (if k=i then x else 0) - (if k=j then x else 0)

private lemma pottsPoint_simplex (q : ℕ) (i j : Fin q) (hij : i ≠ j)
    (hq : (q:ℝ) ≠ 0) (hqpos : 0 < (q:ℝ)) (x : ℝ) (hx : |x| ≤ (q:ℝ)⁻¹) :
    pottsPoint q i j x ∈ stdSimplex ℝ (Fin q) := by
  have hl := (abs_le.mp hx).1
  have hu := (abs_le.mp hx).2
  have hi : 0 ≤ (q:ℝ)⁻¹ := le_of_lt (inv_pos.mpr hqpos)
  constructor
  · intro k
    by_cases hk1 : k = i
    · have hk2 : k ≠ j := by simpa [hk1] using hij
      simp [pottsPoint, hk1, hij]
      linarith
    · by_cases hk2 : k = j
      · simp [pottsPoint, hk2, Ne.symm hij]
        linarith
      · simp [pottsPoint, hk1, hk2, hi]
  · simp [pottsPoint, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    field_simp

private lemma potts_symmetric_law (q : ℕ) (β : ℝ) (i j : Fin q) (hij : i ≠ j)
    (hq : (q:ℝ) ≠ 0) (hqpos : 0 < (q:ℝ)) (ht : (q:ℝ)-1+β ≠ 0)
    (x : ℝ) (hx : |x| ≤ (q:ℝ)⁻¹) :
    twoPoint (.potts q) (pottsPoint q i j x) (pottsPoint q i j (-x)) ∈ cavityLaws (.potts q) β := by
  apply twoPoint_is_cavity
  · exact pottsPoint_simplex q i j hij hq hqpos x hx
  · apply pottsPoint_simplex q i j hij hq hqpos (-x)
    simpa using hx
  · intro k
    change (pottsPoint q i j x k + pottsPoint q i j (-x) k)/2 = Model.pi (.potts q) β k
    rw [potts_pi_real q β k hq ht]
    simp [pottsPoint]
    split_ifs <;> ring
end ZeroFreeRRG.Hardcore
namespace ZeroFreeRRG.Hardcore
private lemma potts_normalized_two_point_cavity (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 ≤ β) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      twoPoint (.potts q)
        (pottsPoint q ⟨0, by omega⟩ ⟨1, by omega⟩ (ε / Real.sqrt (2*(q:ℝ))))
        (pottsPoint q ⟨0, by omega⟩ ⟨1, by omega⟩ (-(ε / Real.sqrt (2*(q:ℝ))))) ∈
          cavityLaws (.potts q) β := by
  have hq' : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0:ℝ) < q := by linarith
  have hqn : (q:ℝ) ≠ 0 := ne_of_gt hqpos
  have ht : (q:ℝ)-1+β ≠ 0 := ne_of_gt (by linarith)
  let s := Real.sqrt (2*(q:ℝ))
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  refine ⟨s/(q:ℝ), div_pos hs hqpos, ?_⟩
  intro ε hε hεlt
  have hmul : ε*(q:ℝ) < s := (lt_div_iff₀ hqpos).mp hεlt
  have hbound : ε/s < 1/(q:ℝ) := by
    apply (div_lt_div_iff₀ hs hqpos).2
    simpa using hmul
  have hx : |ε/s| ≤ (q:ℝ)⁻¹ := by
    rw [abs_of_pos (div_pos hε hs)]
    simpa [one_div] using hbound.le
  apply potts_symmetric_law q β ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp) hqn hqpos ht
  exact hx
end ZeroFreeRRG.Hardcore
namespace ZeroFreeRRG.Hardcore
private lemma hardcore_edge_factor (α x y : ℝ) (hα : α ≠ 0) (hα1 : 1-α ≠ 0) :
    edgeFactor .hardcore α (hcPoint α x) (hcPoint α y) = 1 - x*y/(1-α)^2 := by
  unfold edgeFactor
  change (∑ a : Fin 2, ∑ b : Fin 2, hcPoint α x a * Model.M .hardcore α a b * hcPoint α y b) = _
  simp only [Fin.sum_univ_two, hcPoint, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  simp [Model.M, Model.P, hc_pi0_real, hc_pi1_real]
  field_simp
  ring
end ZeroFreeRRG.Hardcore
namespace ZeroFreeRRG.Hardcore
private lemma hardcore_normalized_edge (α ε σ τ : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    edgeFactor .hardcore α
      (hcPoint α (σ*ε*Real.sqrt (α*(1-α))))
      (hcPoint α (τ*ε*Real.sqrt (α*(1-α)))) =
        1 - σ*τ*ε^2*(α/(1-α)) := by
  have hα0 : α ≠ 0 := ne_of_gt hα
  have hα1' : 1-α ≠ 0 := ne_of_gt (by linarith)
  have hs : (Real.sqrt (α*(1-α)))^2 = α*(1-α) := Real.sq_sqrt (by positivity)
  rw [hardcore_edge_factor α _ _ hα0 hα1']
  field_simp
  rw [hs]
  ring
end ZeroFreeRRG.Hardcore
namespace ZeroFreeRRG.Hardcore
private lemma twoPoint_prod_expectation (m : Model) (a b : m.Spin → ℝ)
    (F : (m.Spin → ℝ) × (m.Spin → ℝ) → ℝ) :
    ∫ p, F p ∂((twoPoint m a b : Measure (m.Spin → ℝ)).prod (twoPoint m a b : Measure (m.Spin → ℝ))) =
      (F (a,a) + F (a,b) + F (b,a) + F (b,b))/4 := by
  change (∫ p, F p ∂(((1/2:ℝ≥0∞) • Measure.dirac a + (1/2:ℝ≥0∞) • Measure.dirac b).prod
      ((1/2:ℝ≥0∞) • Measure.dirac a + (1/2:ℝ≥0∞) • Measure.dirac b))) = _
  rw [Measure.add_prod, Measure.prod_add, Measure.prod_add]
  simp only [Measure.prod_smul_left, Measure.prod_smul_right, Measure.dirac_prod_dirac, smul_smul]
  have hint : ∀ p : (m.Spin → ℝ) × (m.Spin → ℝ),
      Integrable F (((1/2:ℝ≥0∞)*(1/2:ℝ≥0∞)) • Measure.dirac p) := by
    intro p
    exact (integrable_dirac (by simp)).smul_measure (by finiteness)
  rw [integral_add_measure ((hint (a,a)).add_measure (hint (a,b)))
       ((hint (b,a)).add_measure (hint (b,b))),
      integral_add_measure (hint (a,a)) (hint (a,b)),
      integral_add_measure (hint (b,a)) (hint (b,b))]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_mul, ENNReal.toReal_div,
    ENNReal.toReal_one, ENNReal.toReal_ofNat, smul_eq_mul]
  ring
end ZeroFreeRRG.Hardcore
namespace ZeroFreeRRG.Hardcore
private lemma hardcore_edge_expectation (α x : ℝ) (hα : α ≠ 0) (hα1 : 1-α ≠ 0) :
    (∫ p, xlogx (edgeFactor .hardcore α p.1 p.2)
      ∂((twoPoint .hardcore (hcPoint α x) (hcPoint α (-x)) : Measure (Model.hardcore.Spin → ℝ)).prod
        (twoPoint .hardcore (hcPoint α x) (hcPoint α (-x)) : Measure (Model.hardcore.Spin → ℝ)))) =
       (xlogx (1 - x^2/(1-α)^2) + xlogx (1 + x^2/(1-α)^2))/2 := by
  rw [twoPoint_prod_expectation]
  simp only [hardcore_edge_factor α _ _ hα hα1]
  have h1 : 1 - x*x/(1-α)^2 = 1 - x^2/(1-α)^2 := by ring
  have h2 : 1 - x*(-x)/(1-α)^2 = 1 + x^2/(1-α)^2 := by ring
  have h3 : 1 - (-x)*x/(1-α)^2 = 1 + x^2/(1-α)^2 := by ring
  have h4 : 1 - (-x)*(-x)/(1-α)^2 = 1 - x^2/(1-α)^2 := by ring
  rw [h1,h2,h3,h4]
  ring
end ZeroFreeRRG.Hardcore
namespace ZeroFreeRRG.Hardcore
private lemma symmetric_xlogx_upper (t : ℝ) (ht : 0 ≤ t) (ht2 : t ≤ 1/2) :
    (xlogx (1-t) + xlogx (1+t))/2 ≤ t^2/2 + 2*t^3 := by
  have ht1 : |t| < 1 := by rw [abs_of_nonneg ht]; linarith
  have hneg : |-t| < 1 := by simpa using ht1
  have hm := Real.abs_log_sub_add_sum_range_le ht1 2
  have hp := Real.abs_log_sub_add_sum_range_le hneg 2
  norm_num [Finset.sum_range_succ] at hm hp
  rw [abs_of_nonneg ht] at hm
  rw [abs_of_nonneg ht] at hp
  have hd : 0 < 1-t := by linarith
  have h3 : t^3/(1-t) ≤ 2*t^3 := by
    apply (div_le_iff₀ hd).2
    nlinarith [pow_nonneg ht 3, mul_nonneg (pow_nonneg ht 3) (show 0 ≤ 1-2*t by linarith)]
  have hm' : t + t^2/2 + Real.log (1-t) ≤ 2*t^3 := (le_abs_self _).trans (hm.trans h3)
  have hp' : -t + t^2/2 + Real.log (1+t) ≤ 2*t^3 := by
    have hs : -t + t^2/2 + Real.log (1+t) ≤ |-t + t^2/2 + Real.log (1+t)| := le_abs_self _
    apply hs.trans
    convert hp.trans h3 using 1 <;> ring_nf
  unfold xlogx
  have hminus : 0 ≤ (1-t)*(2*t^3 - (t + t^2/2 + Real.log (1-t))) :=
    mul_nonneg (by linarith) (by linarith)
  have hplus : 0 ≤ (1+t)*(2*t^3 - (-t + t^2/2 + Real.log (1+t))) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [hminus,hplus]
end ZeroFreeRRG.Hardcore
namespace ZeroFreeRRG.Hardcore
private lemma hardcore_edge_expansion_upper (α ε : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hε : 0 ≤ ε) (hsmall : ε^2*(α/(1-α)) ≤ 1/2) :
    (∫ p, xlogx (edgeFactor .hardcore α p.1 p.2)
      ∂((twoPoint .hardcore (hcPoint α (ε*Real.sqrt (α*(1-α))))
          (hcPoint α (-(ε*Real.sqrt (α*(1-α))))) : Measure (Model.hardcore.Spin → ℝ)).prod
        (twoPoint .hardcore (hcPoint α (ε*Real.sqrt (α*(1-α))))
          (hcPoint α (-(ε*Real.sqrt (α*(1-α))))) : Measure (Model.hardcore.Spin → ℝ)))) ≤
    (α/(1-α))^2 * ε^4/2 + 2*(α/(1-α))^3 * ε^6 := by
  have hα0 : α ≠ 0 := ne_of_gt hα
  have hα1' : 1-α ≠ 0 := ne_of_gt (by linarith)
  have hratio : 0 < α/(1-α) := div_pos hα (by linarith)
  have hs : (Real.sqrt (α*(1-α)))^2 = α*(1-α) := Real.sq_sqrt (by positivity)
  rw [hardcore_edge_expectation α _ hα0 hα1']
  have hsq : (ε*Real.sqrt (α*(1-α)))^2/(1-α)^2 = ε^2*(α/(1-α)) := by
    field_simp
    rw [hs]
    ring
  rw [hsq]
  have hh := symmetric_xlogx_upper (ε^2*(α/(1-α))) (by positivity) hsmall
  convert hh using 1 <;> ring
end ZeroFreeRRG.Hardcore
namespace ZeroFreeRRG.Hardcore
private lemma hardcore_mmul0 (α x : ℝ) (hα : α ≠ 0) (hα1 : 1-α ≠ 0) :
    Mmul .hardcore α (hcPoint α x) (0 : Fin 2) = 1 + α*x/(1-α)^2 := by
  unfold Mmul
  change (∑ b : Fin 2, Model.M .hardcore α (0 : Fin 2) b * hcPoint α x b) = _
  simp only [Fin.sum_univ_two, hcPoint, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  simp [Model.M, Model.P, hc_pi0_real, hc_pi1_real]
  field_simp
  ring
private lemma hardcore_mmul1 (α x : ℝ) (hα : α ≠ 0) (hα1 : 1-α ≠ 0) :
    Mmul .hardcore α (hcPoint α x) (1 : Fin 2) = 1 - x/(1-α) := by
  unfold Mmul
  change (∑ b : Fin 2, Model.M .hardcore α (1 : Fin 2) b * hcPoint α x b) = _
  simp only [Fin.sum_univ_two, hcPoint, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  simp [Model.M, Model.P, hc_pi0_real, hc_pi1_real]
  field_simp
private lemma hardcore_vertex_factor (α : ℝ) (d : ℕ) (xs : Fin d → ℝ)
    (hα : α ≠ 0) (hα1 : 1-α ≠ 0) :
    vertexFactor .hardcore α d (fun i => hcPoint α (xs i)) =
      (1-α)*(∏ i, (1 + α*(xs i)/(1-α)^2)) + α*(∏ i, (1-(xs i)/(1-α))) := by
  unfold vertexFactor
  change (∑ a : Fin 2, Model.pi .hardcore α a *
      ∏ i, Mmul .hardcore α (hcPoint α (xs i)) a) = _
  simp [Fin.sum_univ_two, hc_pi0_real, hc_pi1_real,
    hardcore_mmul0 α _ hα hα1, hardcore_mmul1 α _ hα hα1]
end ZeroFreeRRG.Hardcore
namespace ZeroFreeRRG.Hardcore
private lemma xlogx_lower_third (u : ℝ) (hu : |u| ≤ 1/2) :
    u + u^2/2 - 4*|u|^3 ≤ xlogx (1+u) := by
  have hu1 : |u| < 1 := by linarith
  have hneg : |-u| < 1 := by simpa using hu1
  have hp := Real.abs_log_sub_add_sum_range_le hneg 2
  norm_num [Finset.sum_range_succ] at hp
  have hden : 0 < 1 - |u| := by linarith
  have h3 : |u|^3/(1-|u|) ≤ 2*|u|^3 := by
    apply (div_le_iff₀ hden).2
    nlinarith [pow_nonneg (abs_nonneg u) 3,
      mul_nonneg (pow_nonneg (abs_nonneg u) 3) (show 0 ≤ 1-2*|u| by linarith)]
  have hrem : -2*|u|^3 ≤ -u + u^2/2 + Real.log (1+u) := by
    have ha := abs_le.mp (hp.trans h3)
    linarith [ha.1]
  have hupper : u ≤ 1/2 := (abs_le.mp hu).2
  have hlower : -(1/2:ℝ) ≤ u := (abs_le.mp hu).1
  have hprod : 0 ≤ (1+u)*(Real.log (1+u) - (u-u^2/2-2*|u|^3)) :=
    mul_nonneg (by linarith) (by linarith)
  have hcube : u^3 ≤ |u|^3 := by
    have h := le_abs_self (u^3)
    simpa [abs_pow] using h
  have habs3 : 0 ≤ |u|^3 := pow_nonneg (abs_nonneg u) _
  have haux : 0 ≤ (1/2-u)*|u|^3 := mul_nonneg (by linarith) habs3
  unfold xlogx
  nlinarith [hprod, hcube, haux]
end ZeroFreeRRG.Hardcore
namespace ZeroFreeRRG.Hardcore
private lemma twoPoint_expectation (m : Model) (a b : m.Spin → ℝ) (F : (m.Spin → ℝ) → ℝ) :
    ∫ x, F x ∂(twoPoint m a b : Measure (m.Spin → ℝ)) = (F a + F b)/2 := by
  change (∫ x, F x ∂((1/2:ℝ≥0∞) • Measure.dirac a + (1/2:ℝ≥0∞) • Measure.dirac b)) = _
  have hint : ∀ p : m.Spin → ℝ, Integrable F ((1/2:ℝ≥0∞) • Measure.dirac p) := by
    intro p
    exact (integrable_dirac (by simp)).smul_measure (by finiteness)
  rw [integral_add_measure (hint a) (hint b), integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac]
  simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

private lemma twoPoint_product_expectation (m : Model) (a b : m.Spin → ℝ)
    (d : ℕ) (F : (m.Spin → ℝ) → ℝ) :
    ∫ xs : Fin d → (m.Spin → ℝ), (∏ i, F (xs i))
      ∂(Measure.pi (fun _ : Fin d => (twoPoint m a b : Measure (m.Spin → ℝ)))) =
      ((F a + F b)/2)^d := by
  rw [integral_fintype_prod_eq_pow]
  rw [twoPoint_expectation]
  simp
end ZeroFreeRRG.Hardcore
namespace ZeroFreeRRG.Hardcore
private lemma twoPoint_integrable (m : Model) (a b : m.Spin → ℝ) (F : (m.Spin → ℝ) → ℝ) :
    Integrable F (twoPoint m a b : Measure (m.Spin → ℝ)) := by
  change Integrable F ((1/2:ℝ≥0∞) • Measure.dirac a + (1/2:ℝ≥0∞) • Measure.dirac b)
  apply Integrable.add_measure
  · exact (integrable_dirac (by simp)).smul_measure (by finiteness)
  · exact (integrable_dirac (by simp)).smul_measure (by finiteness)

private lemma twoPoint_prod_integrable (m : Model) (a b : m.Spin → ℝ)
    (d : ℕ) (F : (m.Spin → ℝ) → ℝ) :
    Integrable (fun xs : Fin d → (m.Spin → ℝ) => ∏ i, F (xs i))
      (Measure.pi (fun _ : Fin d => (twoPoint m a b : Measure (m.Spin → ℝ)))) := by
  apply Integrable.fintype_prod
  intro i
  exact twoPoint_integrable m a b F

private lemma hardcore_vertex_first_moment (α x : ℝ) (d : ℕ) (hα : α ≠ 0) (hα1 : 1-α ≠ 0) :
    ∫ xs : Fin d → (Model.hardcore.Spin → ℝ), vertexFactor .hardcore α d xs
      ∂(Measure.pi (fun _ : Fin d =>
        (twoPoint .hardcore (hcPoint α x) (hcPoint α (-x)) : Measure (Model.hardcore.Spin → ℝ)))) = 1 := by
  let a : Model.hardcore.Spin → ℝ := hcPoint α x
  let b : Model.hardcore.Spin → ℝ := hcPoint α (-x)
  let F0 : (Model.hardcore.Spin → ℝ) → ℝ := fun μ => Mmul .hardcore α μ (0 : Fin 2)
  let F1 : (Model.hardcore.Spin → ℝ) → ℝ := fun μ => Mmul .hardcore α μ (1 : Fin 2)
  have hform : ∀ xs : Fin d → (Model.hardcore.Spin → ℝ), vertexFactor .hardcore α d xs =
      (1-α)*(∏ i, F0 (xs i)) + α*(∏ i, F1 (xs i)) := by
    intro xs
    unfold vertexFactor
    change (∑ j : Fin 2, Model.pi .hardcore α j * ∏ i, Mmul .hardcore α (xs i) j) = _
    simp [Fin.sum_univ_two, hc_pi0_real, hc_pi1_real, F0, F1]
  simp_rw [hform]
  rw [integral_add ((twoPoint_prod_integrable .hardcore a b d F0).const_mul (1-α))
                   ((twoPoint_prod_integrable .hardcore a b d F1).const_mul α)]
  rw [integral_const_mul, integral_const_mul, twoPoint_product_expectation, twoPoint_product_expectation]
  simp [F0, F1, a, b, hardcore_mmul0 α _ hα hα1, hardcore_mmul1 α _ hα hα1]
  ring_nf

private lemma hardcore_vertex_second_moment (α x : ℝ) (d : ℕ) (hα : α ≠ 0) (hα1 : 1-α ≠ 0) :
    ∫ xs : Fin d → (Model.hardcore.Spin → ℝ), (vertexFactor .hardcore α d xs)^2
      ∂(Measure.pi (fun _ : Fin d =>
        (twoPoint .hardcore (hcPoint α x) (hcPoint α (-x)) : Measure (Model.hardcore.Spin → ℝ)))) =
      (1-α)^2*(1+(α*x/(1-α)^2)^2)^d +
        2*α*(1-α)*(1-(α*x/(1-α)^2)*(x/(1-α)))^d +
          α^2*(1+(x/(1-α))^2)^d := by
  let a : Model.hardcore.Spin → ℝ := hcPoint α x
  let b : Model.hardcore.Spin → ℝ := hcPoint α (-x)
  let F0 : (Model.hardcore.Spin → ℝ) → ℝ := fun μ => Mmul .hardcore α μ (0 : Fin 2)
  let F1 : (Model.hardcore.Spin → ℝ) → ℝ := fun μ => Mmul .hardcore α μ (1 : Fin 2)
  let F00 : (Model.hardcore.Spin → ℝ) → ℝ := fun μ => F0 μ * F0 μ
  let F01 : (Model.hardcore.Spin → ℝ) → ℝ := fun μ => F0 μ * F1 μ
  let F11 : (Model.hardcore.Spin → ℝ) → ℝ := fun μ => F1 μ * F1 μ
  have hform : ∀ xs : Fin d → (Model.hardcore.Spin → ℝ), (vertexFactor .hardcore α d xs)^2 =
      (1-α)^2*(∏ i, F00 (xs i)) + 2*α*(1-α)*(∏ i, F01 (xs i)) + α^2*(∏ i, F11 (xs i)) := by
    intro xs
    have hv : vertexFactor .hardcore α d xs =
        (1-α)*(∏ i, F0 (xs i)) + α*(∏ i, F1 (xs i)) := by
      unfold vertexFactor
      change (∑ j : Fin 2, Model.pi .hardcore α j * ∏ i, Mmul .hardcore α (xs i) j) = _
      simp [Fin.sum_univ_two, hc_pi0_real, hc_pi1_real, F0, F1]
    rw [hv]
    simp only [F00, F01, F11, Finset.prod_mul_distrib]
    ring
  simp_rw [hform]
  let G00 : (Fin d → (Model.hardcore.Spin → ℝ)) → ℝ := fun xs => (1-α)^2 * ∏ i, F00 (xs i)
  let G01 : (Fin d → (Model.hardcore.Spin → ℝ)) → ℝ := fun xs => 2*α*(1-α) * ∏ i, F01 (xs i)
  let G11 : (Fin d → (Model.hardcore.Spin → ℝ)) → ℝ := fun xs => α^2 * ∏ i, F11 (xs i)
  change (∫ xs, ((G00 + G01) + G11) xs
      ∂(Measure.pi (fun _ : Fin d => (twoPoint .hardcore a b : Measure (Model.hardcore.Spin → ℝ))))) = _
  have hg00 : Integrable G00 (Measure.pi (fun _ : Fin d => (twoPoint .hardcore a b : Measure (Model.hardcore.Spin → ℝ)))) :=
    (twoPoint_prod_integrable .hardcore a b d F00).const_mul ((1-α)^2)
  have hg01 : Integrable G01 (Measure.pi (fun _ : Fin d => (twoPoint .hardcore a b : Measure (Model.hardcore.Spin → ℝ)))) :=
    (twoPoint_prod_integrable .hardcore a b d F01).const_mul (2*α*(1-α))
  have hg11 : Integrable G11 (Measure.pi (fun _ : Fin d => (twoPoint .hardcore a b : Measure (Model.hardcore.Spin → ℝ)))) :=
    (twoPoint_prod_integrable .hardcore a b d F11).const_mul (α^2)
  change (∫ xs, (G00 + G01) xs + G11 xs ∂(Measure.pi (fun _ : Fin d => (twoPoint .hardcore a b : Measure (Model.hardcore.Spin → ℝ))))) = _
  rw [integral_add (hg00.add hg01) hg11]
  change (∫ xs, G00 xs + G01 xs ∂(Measure.pi (fun _ : Fin d => (twoPoint .hardcore a b : Measure (Model.hardcore.Spin → ℝ))))) + ∫ xs, G11 xs ∂(Measure.pi (fun _ : Fin d => (twoPoint .hardcore a b : Measure (Model.hardcore.Spin → ℝ)))) = _
  rw [integral_add hg00 hg01]
  dsimp only [G00, G01, G11]
  rw [integral_const_mul, integral_const_mul, integral_const_mul,
    twoPoint_product_expectation, twoPoint_product_expectation, twoPoint_product_expectation]
  have hm00 : (F00 a + F00 b)/2 = 1+(α*x/(1-α)^2)^2 := by
    simp [F00, F0, a, b, hardcore_mmul0 α _ hα hα1]
    ring
  have hm01 : (F01 a + F01 b)/2 = 1-(α*x/(1-α)^2)*(x/(1-α)) := by
    simp [F01, F0, F1, a, b, hardcore_mmul0 α _ hα hα1, hardcore_mmul1 α _ hα hα1]
    ring
  have hm11 : (F11 a + F11 b)/2 = 1+(x/(1-α))^2 := by
    simp [F11, F1, a, b, hardcore_mmul1 α _ hα hα1]
    ring
  rw [hm00,hm01,hm11]
end ZeroFreeRRG.Hardcore
namespace ZeroFreeRRG.Hardcore
private lemma binomial_square_mixture (d : ℕ) (p q A B : ℝ) :
    p^2*(1+A^2)^d + 2*p*q*(1+A*B)^d + q^2*(1+B^2)^d =
      ∑ k ∈ Finset.range (d+1), ((d.choose k : ℕ) : ℝ) * (p*A^k + q*B^k)^2 := by
  have hA : (1+A^2)^d = ∑ k ∈ Finset.range (d+1), (A^k)^2*((d.choose k : ℕ):ℝ) := by
    rw [add_comm, add_pow]
    simp only [one_pow, mul_one]
    apply Finset.sum_congr rfl
    intro k hk
    rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 k]
  have hAB : (1+A*B)^d = ∑ k ∈ Finset.range (d+1), (A^k*B^k)*((d.choose k : ℕ):ℝ) := by
    rw [add_comm, add_pow]
    simp [mul_pow]
  have hB : (1+B^2)^d = ∑ k ∈ Finset.range (d+1), (B^k)^2*((d.choose k : ℕ):ℝ) := by
    rw [add_comm, add_pow]
    simp only [one_pow, mul_one]
    apply Finset.sum_congr rfl
    intro k hk
    rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 k]
  rw [hA,hAB,hB, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  ring
end ZeroFreeRRG.Hardcore
namespace ZeroFreeRRG.Hardcore
private lemma binomial_mixture_lower (d : ℕ) (hd : 2 ≤ d) (p q A B : ℝ) :
    (p+q)^2 + ((d.choose 2 : ℕ):ℝ) * (p*A^2 + q*B^2)^2 ≤
      p^2*(1+A^2)^d + 2*p*q*(1+A*B)^d + q^2*(1+B^2)^d := by
  rw [binomial_square_mixture]
  have hsub : ({0,2} : Finset ℕ) ⊆ Finset.range (d+1) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    simp only [Finset.mem_range]
    rcases hk with rfl | rfl <;> omega
  have h : (∑ k ∈ ({0,2} : Finset ℕ), ((d.choose k : ℕ):ℝ) * (p*A^k + q*B^k)^2) ≤
      ∑ k ∈ Finset.range (d+1), ((d.choose k : ℕ):ℝ) * (p*A^k + q*B^k)^2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro k hk hks
    exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  simpa [Finset.sum_pair (show (0:ℕ) ≠ 2 by omega)] using h
end ZeroFreeRRG.Hardcore
namespace ZeroFreeRRG.Hardcore
private lemma hardcore_vertex_second_lower (α x : ℝ) (d : ℕ) (hd : 2 ≤ d)
    (hα : α ≠ 0) (hα1 : 1-α ≠ 0) :
    1 + ((d.choose 2 : ℕ):ℝ) *
      ((1-α)*(α*x/(1-α)^2)^2 + α*(x/(1-α))^2)^2 ≤
    ∫ xs : Fin d → (Model.hardcore.Spin → ℝ), (vertexFactor .hardcore α d xs)^2
      ∂(Measure.pi (fun _ : Fin d =>
        (twoPoint .hardcore (hcPoint α x) (hcPoint α (-x)) : Measure (Model.hardcore.Spin → ℝ)))) := by
  rw [hardcore_vertex_second_moment α x d hα hα1]
  have h := binomial_mixture_lower d hd (1-α) α (α*x/(1-α)^2) (-(x/(1-α)))
  simp only [neg_sq] at h
  convert h using 1 <;> ring
end ZeroFreeRRG.Hardcore
namespace ZeroFreeRRG.Hardcore
private lemma hardcore_normalized_vertex_second_lower (α ε : ℝ) (d : ℕ) (hd : 2 ≤ d)
    (hα : 0 < α) (hα1 : α < 1) :
    1 + ((d:ℝ)*((d:ℝ)-1)/2)*(α/(1-α))^4*ε^4 ≤
    ∫ xs : Fin d → (Model.hardcore.Spin → ℝ), (vertexFactor .hardcore α d xs)^2
      ∂(Measure.pi (fun _ : Fin d =>
        (twoPoint .hardcore (hcPoint α (ε*Real.sqrt (α*(1-α))))
          (hcPoint α (-(ε*Real.sqrt (α*(1-α))))) : Measure (Model.hardcore.Spin → ℝ)))) := by
  have hα0 : α ≠ 0 := ne_of_gt hα
  have hα1' : 1-α ≠ 0 := ne_of_gt (by linarith)
  have hs : (Real.sqrt (α*(1-α)))^2 = α*(1-α) := Real.sq_sqrt (by positivity)
  have hh := hardcore_vertex_second_lower α (ε*Real.sqrt (α*(1-α))) d hd hα0 hα1'
  have hcoef : (1-α)*(α*(ε*Real.sqrt (α*(1-α)))/(1-α)^2)^2 +
       α*((ε*Real.sqrt (α*(1-α)))/(1-α))^2 = (α/(1-α))^2 * ε^2 := by
    field_simp
    rw [hs]
    ring
  rw [hcoef, Nat.cast_choose_two ℝ] at hh
  convert hh using 1 <;> ring
end ZeroFreeRRG.Hardcore
namespace ZeroFreeRRG.Hardcore
private lemma potts_point_sum (q : ℕ) (i j : Fin q) (x : ℝ) (hq : (q:ℝ) ≠ 0) :
    ∑ k, pottsPoint q i j x k = 1 := by
  simp [pottsPoint, Finset.sum_sub_distrib, Finset.sum_add_distrib, hq]

private lemma potts_point_dot (q : ℕ) (i j : Fin q) (hij : i ≠ j)
    (x y : ℝ) (hq : (q:ℝ) ≠ 0) :
    (∑ k, pottsPoint q i j x k * pottsPoint q i j y k) = (q:ℝ)⁻¹ + 2*x*y := by
  simp only [pottsPoint, sub_mul, mul_sub, add_mul, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp [Finset.mul_sum, Finset.sum_mul, hij, Ne.symm hij, hq]
  field_simp
  ring
end ZeroFreeRRG.Hardcore
namespace ZeroFreeRRG.Hardcore
private lemma potts_M_real (q : ℕ) (β : ℝ) (i j : Fin q)
    (hq : (q:ℝ) ≠ 0) (ht : (q:ℝ) - 1 + β ≠ 0) :
    Model.M (.potts q) β i j =
      (q:ℝ)*((1:ℝ) + if i = j then β-1 else 0) / ((q:ℝ)-1+β) := by
  change Model.P (.potts q) β i j / (Model.pi (.potts q) β i * Model.pi (.potts q) β j) = _
  rw [potts_pi_real q β i hq ht, potts_pi_real q β j hq ht]
  change (((1:ℝ) + if i = j then β - 1 else 0) /
      ((q:ℝ) * ((q:ℝ) - 1 + β))) / ((q:ℝ)⁻¹ * (q:ℝ)⁻¹) = _
  field_simp

private lemma potts_edge_factor (q : ℕ) (β : ℝ) (i j : Fin q) (hij : i ≠ j)
    (x y : ℝ) (hq : (q:ℝ) ≠ 0) (ht : (q:ℝ)-1+β ≠ 0) :
    edgeFactor (.potts q) β (pottsPoint q i j x) (pottsPoint q i j y) =
      1 + 2*(q:ℝ)*(β-1)/((q:ℝ)-1+β)*x*y := by
  unfold edgeFactor
  change (∑ a : Fin q, ∑ b : Fin q,
    pottsPoint q i j x a * Model.M (.potts q) β a b * pottsPoint q i j y b) = _
  simp_rw [potts_M_real q β _ _ hq ht]
  have hid (a : Fin q) : (∑ b : Fin q,
      pottsPoint q i j x a * ((q:ℝ)*(1 + if a = b then β-1 else 0) / ((q:ℝ)-1+β)) * pottsPoint q i j y b) =
      (q:ℝ)/((q:ℝ)-1+β) * (pottsPoint q i j x a *
        ((∑ b, pottsPoint q i j y b) + (β-1)*pottsPoint q i j y a)) := by
    calc
      _ = ∑ b : Fin q, ((q:ℝ)/((q:ℝ)-1+β)) * (pottsPoint q i j x a *
          (pottsPoint q i j y b + if a=b then (β-1)*pottsPoint q i j y b else 0)) := by
        apply Finset.sum_congr rfl
        intro b hb
        split_ifs <;> ring
      _ = _ := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib]
        simp
  simp_rw [hid, potts_point_sum q i j y hq]
  rw [← Finset.mul_sum]
  simp only [mul_add, mul_one, Finset.sum_add_distrib]
  rw [potts_point_sum q i j x hq]
  simp_rw [show ∀ a : Fin q, pottsPoint q i j x a * ((β-1)*pottsPoint q i j y a) =
       (β-1)*(pottsPoint q i j x a * pottsPoint q i j y a) by intro a; ring]
  rw [← Finset.mul_sum, potts_point_dot q i j hij x y hq]
  field_simp
  ring
end ZeroFreeRRG.Hardcore
namespace ZeroFreeRRG.Hardcore
private lemma potts_edge_expectation (q : ℕ) (β : ℝ) (i j : Fin q) (hij : i ≠ j)
    (x : ℝ) (hq : (q:ℝ) ≠ 0) (ht : (q:ℝ)-1+β ≠ 0) :
    (∫ p, xlogx (edgeFactor (.potts q) β p.1 p.2)
      ∂((twoPoint (.potts q) (pottsPoint q i j x) (pottsPoint q i j (-x)) : Measure ((.potts q : Model).Spin → ℝ)).prod
        (twoPoint (.potts q) (pottsPoint q i j x) (pottsPoint q i j (-x)) : Measure ((.potts q : Model).Spin → ℝ)))) =
       (xlogx (1 + 2*(q:ℝ)*(β-1)/((q:ℝ)-1+β)*x^2) +
        xlogx (1 - 2*(q:ℝ)*(β-1)/((q:ℝ)-1+β)*x^2))/2 := by
  rw [twoPoint_prod_expectation]
  simp only [potts_edge_factor q β i j hij _ _ hq ht]
  have h1 : 1 + 2*(q:ℝ)*(β-1)/((q:ℝ)-1+β)*x*x =
      1 + 2*(q:ℝ)*(β-1)/((q:ℝ)-1+β)*x^2 := by ring
  have h2 : 1 + 2*(q:ℝ)*(β-1)/((q:ℝ)-1+β)*x*(-x) =
      1 - 2*(q:ℝ)*(β-1)/((q:ℝ)-1+β)*x^2 := by ring
  have h3 : 1 + 2*(q:ℝ)*(β-1)/((q:ℝ)-1+β)*(-x)*x =
      1 - 2*(q:ℝ)*(β-1)/((q:ℝ)-1+β)*x^2 := by ring
  have h4 : 1 + 2*(q:ℝ)*(β-1)/((q:ℝ)-1+β)*(-x)*(-x) =
      1 + 2*(q:ℝ)*(β-1)/((q:ℝ)-1+β)*x^2 := by ring
  rw [h1,h2,h3,h4]
  ring
end ZeroFreeRRG.Hardcore
namespace ZeroFreeRRG.Hardcore
private lemma potts_edge_expansion_upper (q : ℕ) (hq : 2 ≤ q) (β ε : ℝ)
    (hβ : 0 ≤ β) (hβ1 : β < 1) (hε : 0 ≤ ε)
    (hsmall : ε^2*((1-β)/((q:ℝ)-1+β)) ≤ 1/2) :
    (∫ p, xlogx (edgeFactor (.potts q) β p.1 p.2)
      ∂((twoPoint (.potts q)
          (pottsPoint q ⟨0,by omega⟩ ⟨1,by omega⟩ (ε/Real.sqrt (2*(q:ℝ))))
          (pottsPoint q ⟨0,by omega⟩ ⟨1,by omega⟩ (-(ε/Real.sqrt (2*(q:ℝ))))) : Measure ((.potts q : Model).Spin → ℝ)).prod
        (twoPoint (.potts q)
          (pottsPoint q ⟨0,by omega⟩ ⟨1,by omega⟩ (ε/Real.sqrt (2*(q:ℝ))))
          (pottsPoint q ⟨0,by omega⟩ ⟨1,by omega⟩ (-(ε/Real.sqrt (2*(q:ℝ))))) : Measure ((.potts q : Model).Spin → ℝ)))) ≤
      ((1-β)/((q:ℝ)-1+β))^2 * ε^4/2 + 2*((1-β)/((q:ℝ)-1+β))^3 * ε^6 := by
  have hq' : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0:ℝ) < q := by linarith
  have hqn : (q:ℝ) ≠ 0 := ne_of_gt hqpos
  have hden : 0 < (q:ℝ)-1+β := by linarith
  have ht : (q:ℝ)-1+β ≠ 0 := ne_of_gt hden
  have hspos : 0 < Real.sqrt (2*(q:ℝ)) := Real.sqrt_pos.2 (by positivity)
  have hs : (Real.sqrt (2*(q:ℝ)))^2 = 2*(q:ℝ) := Real.sq_sqrt (by positivity)
  have hk : 0 < (1-β)/((q:ℝ)-1+β) := div_pos (by linarith) hden
  rw [potts_edge_expectation q β ⟨0,by omega⟩ ⟨1,by omega⟩ (by simp) _ hqn ht]
  have hsq : 2*(q:ℝ)*(β-1)/((q:ℝ)-1+β)*(ε/Real.sqrt (2*(q:ℝ)))^2 =
      -(ε^2*((1-β)/((q:ℝ)-1+β))) := by
    field_simp
    rw [hs]
    ring
  rw [hsq]
  have hh := symmetric_xlogx_upper (ε^2*((1-β)/((q:ℝ)-1+β))) (by positivity) hsmall
  convert hh using 1 <;> ring
end ZeroFreeRRG.Hardcore
namespace ZeroFreeRRG.Hardcore
private lemma potts_mmul (q : ℕ) (β : ℝ) (i j k : Fin q) (x : ℝ)
    (hq : (q:ℝ) ≠ 0) (ht : (q:ℝ)-1+β ≠ 0) :
    Mmul (.potts q) β (pottsPoint q i j x) k =
      1 + ((q:ℝ)*(β-1)/((q:ℝ)-1+β))*((if k=i then x else 0) - (if k=j then x else 0)) := by
  unfold Mmul
  change (∑ b : Fin q, Model.M (.potts q) β k b * pottsPoint q i j x b) = _
  simp_rw [potts_M_real q β _ _ hq ht]
  calc
    _ = ((q:ℝ)/((q:ℝ)-1+β))*
        ((∑ b : Fin q, pottsPoint q i j x b) + (β-1)*pottsPoint q i j x k) := by
      calc
        _ = ∑ b : Fin q, ((q:ℝ)/((q:ℝ)-1+β)) *
            (pottsPoint q i j x b + if k=b then (β-1)*pottsPoint q i j x b else 0) := by
          apply Finset.sum_congr rfl
          intro b hb
          split_ifs <;> ring
        _ = _ := by rw [← Finset.mul_sum, Finset.sum_add_distrib]; simp
    _ = _ := by
      rw [potts_point_sum q i j x hq]
      unfold pottsPoint
      field_simp
      ring
end ZeroFreeRRG.Hardcore
namespace ZeroFreeRRG.Hardcore
private lemma potts_vertex_factor (q : ℕ) (β : ℝ) (i j : Fin q) (hij : i ≠ j)
    (d : ℕ) (xs : Fin d → ℝ) (hq : (q:ℝ) ≠ 0) (ht : (q:ℝ)-1+β ≠ 0) :
    vertexFactor (.potts q) β d (fun r => pottsPoint q i j (xs r)) =
      (q:ℝ)⁻¹ * ((∏ r, (1 + ((q:ℝ)*(β-1)/((q:ℝ)-1+β))*xs r)) +
        (∏ r, (1 - ((q:ℝ)*(β-1)/((q:ℝ)-1+β))*xs r)) + ((q:ℝ)-2)) := by
  let c := (q:ℝ)*(β-1)/((q:ℝ)-1+β)
  let A : ℝ := ∏ r, (1+c*xs r)
  let B : ℝ := ∏ r, (1-c*xs r)
  have hprod (k : Fin q) : (∏ r, Mmul (.potts q) β (pottsPoint q i j (xs r)) k) =
      1 + (if k=i then A-1 else 0) + (if k=j then B-1 else 0) := by
    by_cases hki : k=i
    · subst k
      simp [potts_mmul q β i j i _ hq ht, hij, A, c]
    · by_cases hkj : k=j
      · subst k
        simp [potts_mmul q β i j j _ hq ht, Ne.symm hij, B, c, sub_eq_add_neg]
      · simp [potts_mmul q β i j k _ hq ht, hki, hkj]
  unfold vertexFactor
  change (∑ k : Fin q, Model.pi (.potts q) β k *
    ∏ r, Mmul (.potts q) β (pottsPoint q i j (xs r)) k) = _
  simp only [potts_pi_real q β _ hq ht, hprod, ← Finset.mul_sum]
  simp [Finset.sum_add_distrib, A, B, c]
  left
  ring
end ZeroFreeRRG.Hardcore
namespace ZeroFreeRRG.Hardcore
private lemma twoPoint_support (m : Model) (a b : m.Spin → ℝ) :
    ∀ᵐ x ∂(twoPoint m a b : Measure (m.Spin → ℝ)), x = a ∨ x = b := by
  rw [ae_iff]
  change ((1/2:ℝ≥0∞) • Measure.dirac a + (1/2:ℝ≥0∞) • Measure.dirac b)
    {x | ¬(x=a ∨ x=b)} = 0
  simp [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply]

private lemma twoPoint_pi_support (m : Model) (a b : m.Spin → ℝ) (d : ℕ) :
    ∀ᵐ xs : Fin d → (m.Spin → ℝ) ∂(Measure.pi (fun _ : Fin d => (twoPoint m a b : Measure (m.Spin → ℝ)))),
      ∀ i, xs i = a ∨ xs i = b := by
  rw [Filter.eventually_all]
  intro i
  exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin d => (twoPoint m a b : Measure (m.Spin → ℝ))) (i := i)).eventually (twoPoint_support m a b)
end ZeroFreeRRG.Hardcore

open Polynomial

private lemma polynomial_quadratic_bound (P : Polynomial ℝ) (h0 : P.eval 0 = 1)
    (h1 : P.derivative.eval 0 = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, |x| ≤ 1 → |P.eval x - 1| ≤ C*x^2 := by
  have hcoeff0 : (P - 1).coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero]
    simp [h0]
  have hcoeff1 : (P - 1).coeff 1 = 0 := by
    have h := h1
    rw [← coeff_zero_eq_eval_zero, coeff_derivative] at h
    simpa [coeff_sub, coeff_one] using h
  have hdiv : (X : Polynomial ℝ)^2 ∣ P - 1 := by
    apply X_pow_dvd_iff.mpr
    intro k hk
    have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl <;> assumption
  obtain ⟨Q, hQ⟩ := hdiv
  have hcont : ContinuousOn (fun x : ℝ => |Q.eval x|) (Icc (-1) 1) :=
    Q.continuous.abs.continuousOn
  obtain ⟨z, hz, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, by norm_num⟩ hcont
  refine ⟨|Q.eval z|+1, by positivity, ?_⟩
  intro x hx
  have hx' : x ∈ Icc (-1:ℝ) 1 := by exact abs_le.mp hx
  have hq := hmax hx'
  change |Q.eval x| ≤ |Q.eval z| at hq
  have heval : P.eval x - 1 = x^2 * Q.eval x := by
    have h := congrArg (Polynomial.eval x) hQ
    simpa only [eval_sub, eval_one, eval_mul, eval_pow, eval_X] using h
  rw [heval, abs_mul, abs_of_nonneg (sq_nonneg x)]
  calc
    x^2 * |Q.eval x| ≤ x^2 * (|Q.eval z|+1) := mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg x)
    _ = (|Q.eval z|+1)*x^2 := by ring

open scoped BigOperators
private noncomputable def mixVertexPoly (d : ℕ) (p q r A B : ℝ) (s : Fin d → ℝ) : Polynomial ℝ :=
  C p * (∏ i, (1 + C (A*s i)*X)) + C q * (∏ i, (1 + C (B*s i)*X)) + C r

private lemma mixVertexPoly_eval_zero (d : ℕ) (p q r A B : ℝ) (s : Fin d → ℝ)
    (hpq : p+q+r=1) : (mixVertexPoly d p q r A B s).eval 0 = 1 := by
  simp [mixVertexPoly, eval_prod, hpq]

private lemma mixVertexPoly_derivative_zero (d : ℕ) (p q r A B : ℝ) (s : Fin d → ℝ)
    (hcancel : p*A+q*B=0) : (mixVertexPoly d p q r A B s).derivative.eval 0 = 0 := by
  simp [mixVertexPoly, derivative_prod_finset, eval_finsetSum, eval_prod]
  simp_rw [← Finset.mul_sum]
  nlinarith [mul_eq_zero_of_left hcancel (∑ i, s i)]

private noncomputable def signVec (d : ℕ) (b : Fin d → Bool) : Fin d → ℝ :=
  fun i => if b i then 1 else -1

private lemma mixVertexPoly_uniform (d : ℕ) (p q r A B : ℝ)
    (hpq : p+q+r=1) (hcancel : p*A+q*B=0) :
    ∃ C : ℝ, 0 < C ∧ ∀ b : Fin d → Bool, ∀ x : ℝ, |x| ≤ 1 →
      |(mixVertexPoly d p q r A B (signVec d b)).eval x - 1| ≤ C*x^2 := by
  have hpoly : ∀ b : Fin d → Bool, ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, |x| ≤ 1 →
      |(mixVertexPoly d p q r A B (signVec d b)).eval x - 1| ≤ C*x^2 := by
    intro b
    exact polynomial_quadratic_bound _ (mixVertexPoly_eval_zero d p q r A B _ hpq)
      (mixVertexPoly_derivative_zero d p q r A B _ hcancel)
  choose C hCpos hCbound using hpoly
  refine ⟨(∑ b : Fin d → Bool, C b)+1, ?_, ?_⟩
  · have : 0 ≤ ∑ b : Fin d → Bool, C b := Finset.sum_nonneg (by intro b hb; exact (hCpos b).le)
    linarith
  · intro b x hx
    have hsingle : C b ≤ ∑ b : Fin d → Bool, C b :=
      Finset.single_le_sum (fun b hb => (hCpos b).le) (Finset.mem_univ b)
    exact (hCbound b x hx).trans (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg x))
namespace ZeroFreeRRG.Hardcore
private lemma hardcore_vertex_poly_identity (α ε : ℝ) (d : ℕ) (b : Fin d → Bool)
    (hα : α ≠ 0) (hα1 : 1-α ≠ 0) :
    vertexFactor .hardcore α d
      (fun i => hcPoint α (signVec d b i * ε * Real.sqrt (α*(1-α)))) =
    (mixVertexPoly d (1-α) α 0
      (α*Real.sqrt (α*(1-α))/(1-α)^2) (-(Real.sqrt (α*(1-α))/(1-α))) (signVec d b)).eval ε := by
  rw [hardcore_vertex_factor α d _ hα hα1]
  simp only [mixVertexPoly, eval_add, eval_mul, eval_C, eval_prod, eval_one, eval_X, add_zero]
  congr 2 <;> apply Finset.prod_congr rfl <;> intro i hi <;> ring
end ZeroFreeRRG.Hardcore
namespace ZeroFreeRRG.Hardcore
private lemma hardcore_vertex_uniform_quadratic (α : ℝ) (d : ℕ)
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, |ε| ≤ 1 →
      ∀ᵐ xs : Fin d → (Model.hardcore.Spin → ℝ)
        ∂(Measure.pi (fun _ : Fin d =>
          (twoPoint .hardcore (hcPoint α (ε*Real.sqrt (α*(1-α))))
            (hcPoint α (-(ε*Real.sqrt (α*(1-α))))) : Measure (Model.hardcore.Spin → ℝ)))),
        |vertexFactor .hardcore α d xs - 1| ≤ C*ε^2 := by
  have hα0 : α ≠ 0 := ne_of_gt hα
  have hα1' : 1-α ≠ 0 := ne_of_gt (by linarith)
  let s := Real.sqrt (α*(1-α))
  let A := α*s/(1-α)^2
  let B := -s/(1-α)
  have hpq : (1-α)+α+0 = 1 := by ring
  have hcancel : (1-α)*A + α*B = 0 := by
    dsimp [A,B]
    field_simp
    ring
  obtain ⟨C, hC, hbound⟩ := mixVertexPoly_uniform d (1-α) α 0 A B hpq hcancel
  refine ⟨C, hC, ?_⟩
  intro ε hε
  filter_upwards [twoPoint_pi_support .hardcore (hcPoint α (ε*s)) (hcPoint α (-(ε*s))) d] with xs hxs
  let b : Fin d → Bool := fun i => decide (xs i = hcPoint α (ε*s))
  have heq : xs = fun i => hcPoint α (signVec d b i * ε * s) := by
    funext i
    by_cases hi : xs i = hcPoint α (ε*s)
    · simpa [signVec, b, hi] using hi
    · have hj := (hxs i).resolve_left hi
      simpa [signVec, b, hi] using hj
  rw [heq, hardcore_vertex_poly_identity α ε d b hα0 hα1']
  have hbnd := hbound b ε hε
  dsimp [A, B, s] at hbnd
  simpa only [neg_div] using hbnd
end ZeroFreeRRG.Hardcore
namespace ZeroFreeRRG.Hardcore
private lemma twoPoint_pi_continuous_integrable (m : Model) (a b : m.Spin → ℝ) (d : ℕ)
    (F : (Fin d → (m.Spin → ℝ)) → ℝ) (hF : Continuous F) :
    Integrable F (Measure.pi (fun _ : Fin d => (twoPoint m a b : Measure (m.Spin → ℝ)))) := by
  let choiceFn : (Fin d → Bool) → (Fin d → (m.Spin → ℝ)) := fun signs i => if signs i then a else b
  let C : ℝ := ∑ signs : Fin d → Bool, |F (choiceFn signs)|
  apply (integrable_const C).mono' hF.aestronglyMeasurable
  filter_upwards [twoPoint_pi_support m a b d] with xs hxs
  let signs : Fin d → Bool := fun i => decide (xs i = a)
  have hx : xs = choiceFn signs := by
    funext i
    by_cases h : xs i = a
    · simp [choiceFn, signs, h]
    · have hb := (hxs i).resolve_left h
      simp [choiceFn, signs, h, hb]
  rw [hx]
  change |F (choiceFn signs)| ≤ C
  exact Finset.single_le_sum (fun s hs => abs_nonneg (F (choiceFn s))) (Finset.mem_univ signs)
end ZeroFreeRRG.Hardcore
namespace ZeroFreeRRG.Hardcore
private lemma vertexFactor_continuous (m : Model) (t : ℝ) (d : ℕ) :
    Continuous (fun xs : Fin d → (m.Spin → ℝ) => vertexFactor m t d xs) := by
  unfold vertexFactor Mmul
  fun_prop
end ZeroFreeRRG.Hardcore
namespace ZeroFreeRRG.Hardcore
private lemma vertex_expectation_lower (m : Model) (t : ℝ) (d : ℕ) (a b : m.Spin → ℝ)
    (C ε : ℝ) (hC : 0 < C) (hsmall : C*ε^2 ≤ 1/2)
    (hbound : ∀ᵐ xs : Fin d → (m.Spin → ℝ)
      ∂(Measure.pi (fun _ : Fin d => (twoPoint m a b : Measure (m.Spin → ℝ)))),
        |vertexFactor m t d xs - 1| ≤ C*ε^2) :
    (1/2:ℝ) * (∫ xs : Fin d → (m.Spin → ℝ), (vertexFactor m t d xs)^2
      ∂(Measure.pi (fun _ : Fin d => (twoPoint m a b : Measure (m.Spin → ℝ))))) -
      1/2 - 4*(C*ε^2)^3 ≤
    ∫ xs : Fin d → (m.Spin → ℝ), xlogx (vertexFactor m t d xs)
      ∂(Measure.pi (fun _ : Fin d => (twoPoint m a b : Measure (m.Spin → ℝ)))) := by
  let μ := Measure.pi (fun _ : Fin d => (twoPoint m a b : Measure (m.Spin → ℝ)))
  let V : (Fin d → (m.Spin → ℝ)) → ℝ := fun xs => vertexFactor m t d xs
  have hV : Continuous V := vertexFactor_continuous m t d
  have hW : Integrable (fun xs => (V xs)^2) μ :=
    twoPoint_pi_continuous_integrable m a b d _ (hV.pow 2)
  have hX : Integrable (fun xs => xlogx (V xs)) μ :=
    twoPoint_pi_continuous_integrable m a b d _ (Real.continuous_mul_log.comp hV)
  let E : ℝ := 1/2 + 4*(C*ε^2)^3
  have hG : Integrable (fun xs => (1/2:ℝ)*(V xs)^2-E) μ :=
    (hW.const_mul (1/2)).sub (integrable_const E)
  have hae : (fun xs => (1/2:ℝ)*(V xs)^2-E) ≤ᵐ[μ] (fun xs => xlogx (V xs)) := by
    filter_upwards [hbound] with xs hx
    have hsmall' : |V xs-1| ≤ 1/2 := le_trans hx hsmall
    have htaylor := xlogx_lower_third (V xs-1) hsmall'
    have hpow : |V xs-1|^3 ≤ (C*ε^2)^3 := pow_le_pow_left₀ (abs_nonneg _) hx _
    dsimp [E]
    have heq : 1 + (V xs-1) = V xs := by ring
    rw [heq] at htaylor
    nlinarith [htaylor, hpow]
  have hi := integral_mono_ae hG hX hae
  have heval : (∫ xs, (1/2:ℝ)*(V xs)^2-E ∂μ) =
      (1/2:ℝ)*(∫ xs, (V xs)^2 ∂μ)-E := by
    rw [integral_sub (hW.const_mul (1/2)) (integrable_const E), integral_const_mul, integral_const]
    simp
  rw [heval] at hi
  dsimp [E, V, μ] at hi
  linarith
end ZeroFreeRRG.Hardcore
namespace ZeroFreeRRG.Hardcore
private lemma hardcore_fourth_order_witness (d : ℕ) (hd : 3 ≤ d) (α : ℝ)
    (hα : 0 < α) (hα2 : α < 1/2) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ ν ∈ cavityLaws .hardcore α,
        ((d : ℝ) / 4) * (α / (1 - α))^2 *
          (((d : ℝ) - 1) * (α / (1 - α))^2 - 1) * ε^4 - C * ε^6 ≤
            betheK .hardcore α d ν := by
  let θ := α/(1-α)
  have hθ : 0 < θ := div_pos hα (by linarith)
  have hd' : (3:ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0:ℝ) ≤ d := by linarith
  obtain ⟨C,hC,hbound⟩ := hardcore_vertex_uniform_quadratic α d hα (by linarith)
  obtain ⟨δ,hδ,hadmissible⟩ := hardcore_normalized_two_point_cavity α hα hα2
  let Ctotal := 4*C^3 + (d:ℝ)*θ^3 + 1
  have hCtotal : 0 < Ctotal := by dsimp [Ctotal]; positivity
  let ε₀ := min δ (min 1 (min (1/(2*(C+1))) (1/(2*(θ+1)))))
  have hε₀ : 0 < ε₀ := by dsimp [ε₀]; positivity
  refine ⟨Ctotal, ε₀, hCtotal, hε₀, ?_⟩
  intro ε hε hε₀'
  have hεδ : ε < δ := lt_of_lt_of_le hε₀' (min_le_left _ _)
  have hε1 : ε < 1 := lt_of_lt_of_le hε₀' (le_trans (min_le_right _ _) (min_le_left _ _))
  have hεC : ε < 1/(2*(C+1)) := lt_of_lt_of_le hε₀'
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hεθ : ε < 1/(2*(θ+1)) := lt_of_lt_of_le hε₀'
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hεsq : ε^2 ≤ ε := by nlinarith
  have hmultC : ε*(2*(C+1)) < 1 := (lt_div_iff₀ (by positivity)).mp hεC
  have hmultθ : ε*(2*(θ+1)) < 1 := (lt_div_iff₀ (by positivity)).mp hεθ
  have hsmallC : C*ε^2 ≤ 1/2 := by
    nlinarith [mul_nonneg hC.le (sub_nonneg.mpr hεsq)]
  have hsmallθ : ε^2*θ ≤ 1/2 := by
    nlinarith [mul_nonneg hθ.le (sub_nonneg.mpr hεsq)]
  let a := hcPoint α (ε*Real.sqrt (α*(1-α)))
  let b := hcPoint α (-(ε*Real.sqrt (α*(1-α))))
  let ν := twoPoint .hardcore a b
  have hν : ν ∈ cavityLaws .hardcore α := hadmissible ε hε hεδ
  refine ⟨ν, hν, ?_⟩
  have hεabs : |ε| ≤ 1 := by simpa [abs_of_pos hε] using hε1.le
  have hxs := hbound ε hεabs
  have hv := vertex_expectation_lower .hardcore α d a b C ε hC hsmallC hxs
  have hm := hardcore_normalized_vertex_second_lower α ε d (by omega) hα (by linarith)
  have he := hardcore_edge_expansion_upper α ε hα (by linarith) hε.le hsmallθ
  have he' := mul_le_mul_of_nonneg_left he (show (0:ℝ) ≤ (d:ℝ)/2 by positivity)
  unfold betheK
  change _ ≤ (∫ xs : Fin d → (Model.hardcore.Spin → ℝ), xlogx (vertexFactor .hardcore α d xs)
      ∂(Measure.pi (fun _ : Fin d => (ν : Measure (Model.hardcore.Spin → ℝ))))) -
    (d:ℝ)/2 * (∫ p, xlogx (edgeFactor .hardcore α p.1 p.2)
      ∂((ν : Measure (Model.hardcore.Spin → ℝ)).prod (ν : Measure (Model.hardcore.Spin → ℝ))))
  dsimp [ν,a,b,θ,Ctotal] at *
  nlinarith [sq_nonneg ε, pow_nonneg (le_of_lt hε) 6]
end ZeroFreeRRG.Hardcore
open ZeroFreeRRG.Hardcore

theorem solution (d : ℕ) (hd : 3 ≤ d) (α : ℝ)
    (hα : 0 < α) (hα2 : α < 1/2) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ ν ∈ cavityLaws .hardcore α,
        ((d : ℝ) / 4) * (α / (1 - α))^2 *
          (((d : ℝ) - 1) * (α / (1 - α))^2 - 1) * ε^4 - C * ε^6 ≤
            betheK .hardcore α d ν := by
  exact hardcore_fourth_order_witness d hd α hα hα2
