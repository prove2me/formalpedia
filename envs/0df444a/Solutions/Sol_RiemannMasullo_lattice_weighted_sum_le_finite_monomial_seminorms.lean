-- Prove2me | solution 1 for RiemannMasullo.lattice_weighted_sum_le_finite_monomial_seminorms
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T03:19:59.098488+00:00
-- url     : https://prove2.me/submissions/95090826-fe70-47bb-9eba-4d89d321976f

-- New supporting theorem for the lattice Schwartz-space equivalence of Appendix D.
import Theorems.Thm_RiemannMasullo_summable_lattice_product_majorant
import Theorems.Thm_RiemannMasullo_lattice_radial_weight_monomial_domination
import Theorems.Thm_RiemannMasullo_lattice_monomial_evaluation_le_seminorm
import Definitions.Def_RiemannMasullo_RapidDecaySequenceTopology
import Mathlib
open RiemannMasullo
open scoped ENNReal

theorem solution (r j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ElementarySchwartz 0 0 r PUnit,
      rapidDecaySequenceBound j (fun a => f (0,0,a,PUnit.unit)) ≤
        ENNReal.ofReal (C * ∑ U : Finset (Fin r), elementarySchwartzSeminorm
          (0,0,0, fun i => if i ∈ U then j+2 else 0) f) := by
  classical
  let b := fun a : Fin r → ℤ => ∏ i, (1/(1+(a i:ℝ)^2))
  have hb : Summable b := (summable_lattice_product_majorant r).1
  have hb0 (a) : 0 ≤ b a := by dsimp [b]; positivity
  let K : ℝ := ((r:ℝ)+2)^j*2^r
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K*(∑' a,b a),mul_nonneg hK (tsum_nonneg hb0),?_⟩
  intro f
  let p (U : Finset (Fin r)) := elementarySchwartzSeminorm
    (0,0,0,fun i => if i ∈ U then j+2 else 0) f
  let P := ∑ U,p U
  have hp (U) : 0 ≤ p U := apply_nonneg _ _
  have hP : 0 ≤ P := Finset.sum_nonneg fun i _ => hp i
  let v (a : Fin r → ℤ) : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (fun i => (a i:ℝ))
  let s := fun a : Fin r → ℤ => f (0,0,a,PUnit.unit)
  have hpoint (a) : (1+‖v a‖)^j * ‖s a‖ ≤ (K*P)*b a := by
    let U := Finset.univ.filter (fun i => a i ≠ 0)
    let d := fun i => if a i=0 then 0 else j+2
    have he : d = fun i => if i ∈ U then j+2 else 0 := by
      funext i; by_cases hi : a i = 0 <;> simp [d,U,hi]
    have hev : (∏ i, |(a i:ℝ)|^d i)*‖s a‖ ≤ P := by
      apply (lattice_monomial_evaluation_le_seminorm r f d a).trans
      change elementarySchwartzSeminorm (0,0,0,d) f ≤ P
      rw [he]
      exact Finset.single_le_sum (fun U _ => hp U) (Finset.mem_univ U)
    let D := ∏ i, (1+(a i:ℝ)^2)
    have hD : 0 < D := by dsimp [D]; positivity
    have hbi : b a = 1/D := by simp [b,D,one_div,Finset.prod_inv_distrib]
    rw [hbi,←div_eq_mul_one_div,le_div_iff₀ hD]
    have hdom : (1+‖v a‖)^j * D ≤ K * ∏ i, |(a i:ℝ)|^d i := lattice_radial_weight_monomial_domination r j a
    calc
      _ = ((1+‖v a‖)^j * D) * ‖s a‖ := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_right hdom (norm_nonneg _)).trans (by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hev hK)
  have hnn (a) : 0 ≤ (K*P)*b a := mul_nonneg (mul_nonneg hK hP) (hb0 a)
  have hh (a) : ((1+(‖v a‖₊:ℝ≥0∞))^j * (‖s a‖₊:ℝ≥0∞)) ≤ ENNReal.ofReal ((K*P)*b a) := by
    have h := ENNReal.ofReal_le_ofReal (hpoint a)
    simpa only [ENNReal.ofReal_mul (by positivity : 0 ≤ (1+‖v a‖)^j),
      ENNReal.ofReal_pow (by positivity : 0 ≤ 1+‖v a‖), ENNReal.ofReal_add (by norm_num : (0:ℝ) ≤ 1) (norm_nonneg (v a)),
      ENNReal.ofReal_one, ofReal_norm_eq_enorm, enorm_eq_nnnorm] using h
  change (∑' a, (1+(‖v a‖₊:ℝ≥0∞))^j * (‖s a‖₊:ℝ≥0∞)) ≤ ENNReal.ofReal ((K*(∑' a,b a))*P)
  apply (ENNReal.tsum_le_tsum hh).trans
  rw [←ENNReal.ofReal_tsum_of_nonneg hnn (hb.mul_left (K*P)),tsum_mul_left]
  apply le_of_eq
  congr 1
  ring
