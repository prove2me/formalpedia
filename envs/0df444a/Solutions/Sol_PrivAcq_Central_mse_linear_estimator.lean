-- Prove2me | solution 1 for PrivAcq.Central.mse_linear_estimator
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-29T08:16:10.723981+00:00
-- url     : https://prove2.me/submissions/539cb69c-0cce-4f8b-bd78-be95ffad4bf9

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
open MeasureTheory ProbabilityTheory
namespace Queelius.PrivateAcquisition
lemma laplace_second (η : ℝ) (hη : 0 < η) :
    (∫ x : ℝ,x^2 ∂PrivLearn.Generic.laplace (1/η))=2/η^2 := by
  have hd : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (-|x|/(1/η))/(2*(1/η)))) := by fun_prop
  have hnon (x : ℝ) : 0 ≤ Real.exp (-|x|/(1/η))/(2*(1/η)) := by positivity
  unfold PrivLearn.Generic.laplace
  rw [integral_withDensity_eq_integral_toReal_smul hd (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hnon _),smul_eq_mul]
  have he : (fun x : ℝ => Real.exp (-|x|/(1/η))/(2*(1/η))*x^2)=
      (fun x : ℝ => (η/2)*(|x|^2*Real.exp (-(η*|x|)))) := by
    funext x
    have ha : -|x|/(1/η)= -(η*|x|) := by field_simp <;> ring
    rw [ha,sq_abs]
    field_simp
    <;> ring
  rw [he,integral_const_mul]
  change η/2*(∫ x : ℝ,(fun t : ℝ => t^2*Real.exp (-(η*t))) |x|)=2/η^2
  rw [integral_comp_abs (f:= fun x : ℝ => x^2*Real.exp (-(η*x)))]
  have hg := Real.integral_rpow_mul_exp_neg_mul_Ioi (a:=3) (r:=η) (by norm_num) hη
  norm_num [Real.Gamma_ofNat_eq_factorial,Real.rpow_natCast] at hg
  rw [hg]
  field_simp
  <;> ring
lemma laplace_memLp (η : ℝ) (hη : 0 < η) :
    MemLp (fun x : ℝ => x) 2 (PrivLearn.Generic.laplace (1/η)) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  apply Integrable.of_integral_ne_zero
  rw [laplace_second η hη]
  positivity
lemma weighted_second {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (w : Fin n → ℝ) (Z : Fin n → Ω → ℝ) (L : Ω → ℝ)
    (hZ : ∀ i,MemLp (Z i) 2 P) (hL : MemLp L 2 P)
    (hindep : iIndepFun (fun o : Option (Fin n) => Option.elim o L Z) P)
    (hmean : ∀ i,∫ ω,Z i ω ∂P=0) (var : ℝ) (hvar : ∀ i,variance (Z i) P=var) :
    (∫ ω,(L ω+∑ i,w i*Z i ω)^2 ∂P)=(∫ ω,L ω^2 ∂P)+∑ i,w i^2*var := by
  let a : Option (Fin n) → ℝ := fun o => Option.elim o 1 w
  let X : Option (Fin n) → Ω → ℝ := fun o ω => a o*Option.elim o L Z ω
  have hX (o : Option (Fin n)) : MemLp (X o) 2 P := by
    cases o with
    | none => simpa only [X,a,Option.elim_none,one_mul] using hL
    | some i => exact (hZ i).const_mul (w i)
  have hi : iIndepFun X P := hindep.comp (fun o x => a o*x) (fun o => by fun_prop)
  have hv := IndepFun.variance_sum (s:=Finset.univ) (fun o _ => hX o)
    (fun i _ j _ hij => hi.indepFun hij)
  let U : Ω → ℝ := fun ω => L ω+∑ i,w i*Z i ω
  have hU : MemLp U 2 P := hL.add (memLp_finsetSum _ (fun i _ => (hZ i).const_mul (w i)))
  have he : (∑ o,X o)=U := by funext ω;simp [X,a,U,Fintype.sum_option]
  rw [he] at hv
  have hs : (∑ o,variance (X o) P)=variance L P+∑ i,w i^2*var := by
    simp [X,a,Fintype.sum_option,variance_const_mul,hvar]
  rw [hs] at hv
  have hm : (∫ ω,U ω ∂P)=∫ ω,L ω ∂P := by
    unfold U
    rw [integral_add (hL.integrable (by norm_num)) (integrable_finsetSum _ (fun i _ => ((hZ i).const_mul (w i)).integrable (by norm_num))),integral_finsetSum]
    · simp only [integral_const_mul,hmean,mul_zero,Finset.sum_const_zero,add_zero]
    · intro i _;exact ((hZ i).const_mul (w i)).integrable (by norm_num)
  have hVU := variance_eq_sub hU
  have hVL := variance_eq_sub hL
  rw [hm] at hVU
  change (∫ ω,U ω^2 ∂P)=(∫ ω,L ω^2 ∂P)+∑ i,w i^2*var
  simp only [Pi.pow_apply] at hVU hVL
  linarith
lemma correlated_data_control :
    (∑ b : Bool,(1/2:ℚ)*((1/2)*(if b then (1/2:ℚ) else -1/2)+
      (1/2)*(if b then (1/2:ℚ) else -1/2))^2)=1/4 ∧
    2*(1/2:ℚ)^2*(1/4)=1/8 ∧ (1/4:ℚ) ≠ 1/8 := by norm_num
end Queelius.PrivateAcquisition

namespace PrivAcq.Central

open MeasureTheory ProbabilityTheory

theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n : ℕ} (θ var η : ℝ) (hη : 0 < η) (w : Fin n → ℝ)
    (hsum : ∑ i, w i = 1) (Z : Fin n → Ω → ℝ) (L : Ω → ℝ)
    (hZmeas : ∀ i, Measurable (Z i)) (hLmeas : Measurable L)
    (hindep : iIndepFun (fun o : Option (Fin n) => Option.elim o L Z) P)
    (hident : ∀ i j, IdentDistrib (Z i) (Z j) P P)
    (hbdd : ∀ i ω, |Z i ω| ≤ 1 / 2)
    (hmean : ∀ i, ∫ ω, Z i ω ∂P = 0)
    (hvar : ∀ i, variance (Z i) P = var)
    (hL : P.map L = PrivLearn.Generic.laplace (1 / η)) :
    ∫ ω, (∑ i, w i * (θ + Z i ω) + L ω - θ) ^ 2 ∂P = 2 / η ^ 2 + ∑ i, (w i) ^ 2 * var := by
  have hZ2 (i : Fin n) : MemLp (Z i) 2 P :=
    MemLp.of_bound (hZmeas i).aestronglyMeasurable (1/2) (ae_of_all _ (fun ω => by simpa only [Real.norm_eq_abs] using hbdd i ω))
  have hL2 : MemLp L 2 P := by
    have hm : MemLp (fun x : ℝ => x) 2 (P.map L) := by
      rw [hL]
      exact Queelius.PrivateAcquisition.laplace_memLp η hη
    exact hm.comp_of_map hLmeas.aemeasurable
  have hmoment : (∫ ω,L ω^2 ∂P)=2/η^2 := by
    rw [← integral_map (f:=fun x : ℝ => x^2) hLmeas.aemeasurable (by fun_prop),hL,
      Queelius.PrivateAcquisition.laplace_second η hη]
  have he (ω : Ω) : (∑ i,w i*(θ+Z i ω))+L ω-θ=L ω+∑ i,w i*Z i ω := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib,← Finset.sum_mul,hsum,one_mul]
    ring
  simp_rw [he]
  rw [Queelius.PrivateAcquisition.weighted_second P w Z L hZ2 hL2 hindep hmean var hvar,hmoment]

end PrivAcq.Central
