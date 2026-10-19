-- Prove2me | solution 1 for RiskEU.RobustShrink.proposition_IA_1_limit
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-17T09:30:04.058995+00:00
-- url     : https://prove2.me/submissions/22921d55-f77f-4432-ad8c-9f3015e8bfc2

import Definitions.Def_RiskEU_RobustShrink_Setting
set_option autoImplicit false
open Filter Topology
noncomputable section
namespace RiskEU.RobustShrink

lemma sample_bounds (p : Params) (hp : p.Standing) (T : ℕ) (hT : p.N+7<T) :
    (2:ℝ) ≤ p.N ∧ (p.N:ℝ)+7 < T := by
  constructor
  · exact_mod_cast hp.1
  · exact_mod_cast hT

lemma mean_vertex_core (p : Params) (hp : p.Standing) (T : ℕ) (hT : p.N+7<T) :
    p.kappaE T ∈ Set.Icc (0 : ℝ) 1 ∧
      ∀ kappa : ℝ, p.oosuMean T kappa ≤ p.oosuMean T (p.kappaE T) := by
  obtain ⟨hn,ht⟩ := sample_bounds p hp T hT
  have ht0 : (0:ℝ)<T := by linarith
  have ht2 : (0:ℝ)<(T:ℝ)-2 := by linarith
  have htn : (0:ℝ)<(T:ℝ)-p.N := by linarith
  have htn1 : (0:ℝ)<(T:ℝ)-p.N-1 := by linarith
  have htn3 : (0:ℝ)<(T:ℝ)-p.N-3 := by linarith
  have hn1 : (0:ℝ)<(p.N:ℝ)-1 := by linarith
  have hpsi : 0 ≤ p.psi2 := hp.2.2.2.1
  have hden : 0 < p.psi2+((p.N:ℝ)-1)/T := add_pos_of_nonneg_of_pos hpsi (div_pos hn1 ht0)
  have hratio : 0 ≤ ((T:ℝ)-p.N)*((T:ℝ)-p.N-3)/((T:ℝ)*((T:ℝ)-2)) := by positivity
  have hratio1 : ((T:ℝ)-p.N)*((T:ℝ)-p.N-3)/((T:ℝ)*((T:ℝ)-2)) ≤ 1 := by
    apply (div_le_one (mul_pos ht0 ht2)).mpr
    apply mul_le_mul
    · linarith
    · linarith
    · exact htn3.le
    · exact ht0.le
  have heid : p.kappaE T = (((T:ℝ)-p.N)*((T:ℝ)-p.N-3)/((T:ℝ)*((T:ℝ)-2))) *
      (p.psi2/(p.psi2+((p.N:ℝ)-1)/T)) := by unfold Params.kappaE; ring
  have he0 : 0 ≤ p.kappaE T := by rw [heid]; positivity
  have he1 : p.kappaE T ≤ 1 := by
    rw [heid]
    apply mul_le_one₀ hratio1 (div_nonneg hpsi hden.le)
    apply (div_le_one hden).mpr
    linarith [div_pos hn1 ht0]
  refine ⟨⟨he0,he1⟩,?_⟩
  let B : ℝ := (p.psi2+((p.N:ℝ)-1)/T)*((T:ℝ)*((T:ℝ)-2))/(2*((T:ℝ)-p.N)*((T:ℝ)-p.N-3))
  have hB : 0 < B := by dsimp [B]; positivity
  have heB : 2*B*p.kappaE T=p.psi2 := by
    unfold Params.kappaE
    dsimp [B]
    field_simp
    <;> ring
  have hg : 0 < p.gamma := hp.2.1
  intro k
  have hs : k*p.psi2-k^2*B ≤ p.kappaE T*p.psi2-(p.kappaE T)^2*B := by
    have hid : (p.kappaE T*p.psi2-(p.kappaE T)^2*B)-(k*p.psi2-k^2*B) = B*(k-p.kappaE T)^2 := by
      rw [← heB]
      ring
    linarith [mul_nonneg hB.le (sq_nonneg (k-p.kappaE T))]
  have hcoef : 0 ≤ 1/p.gamma*(T:ℝ)/((T:ℝ)-p.N-1) := by positivity
  have hh := mul_le_mul_of_nonneg_left hs hcoef
  have hm (x : ℝ) : p.oosuMean T x = p.meanGMV T + (1/p.gamma*(T:ℝ)/((T:ℝ)-p.N-1))*(x*p.psi2-x^2*B) := by
    dsimp [Params.oosuMean,B]
    ring
  rw [hm k,hm (p.kappaE T)]
  linarith only [hh]

lemma extrema_core (p : Params) (T : ℕ) :
    (∃ kappa ∈ Set.Icc (0 : ℝ) 1, IsMaxOn (p.meanRisk T) (Set.Icc (0 : ℝ) 1) kappa) ∧
    (∃ kappa ∈ Set.Icc (0 : ℝ) 1, IsMinOn (p.oosuVar T) (Set.Icc (0 : ℝ) 1) kappa) := by
  have hc : Continuous (p.oosuVar T) := by unfold Params.oosuVar Params.Delta; fun_prop
  have hm : Continuous (p.meanRisk T) := by
    unfold Params.meanRisk Params.oosuMean
    fun_prop
  exact ⟨isCompact_Icc.exists_isMaxOn (by exact ⟨0,by norm_num⟩) hm.continuousOn,
    isCompact_Icc.exists_isMinOn (by exact ⟨0,by norm_num⟩) hc.continuousOn⟩


lemma mean_limit_core (p : Params) (hp : p.Standing) (hpsi : 0 < p.psi2) :
    Tendsto (fun T : ℕ => p.kappaE T) atTop (nhds 1) := by
  have hi : Tendsto (fun T : ℕ => (T:ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  let F : ℝ → ℝ := fun x =>
    ((1-(p.N:ℝ)*x)*(1-((p.N:ℝ)+3)*x)/(1-2*x)) * (p.psi2/(p.psi2+((p.N:ℝ)-1)*x))
  have hc : ContinuousAt F 0 := by
    dsimp [F]
    fun_prop (disch := simp [ne_of_gt hpsi])
  have hf : F 0=1 := by simp [F,ne_of_gt hpsi]
  have hh := hc.tendsto.comp hi
  rw [hf] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with T hT
  have ht : (T:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hT
  dsimp [F,Params.kappaE]
  field_simp
  <;> ring

end RiskEU.RobustShrink

open RiskEU.RobustShrink

/-- Proposition IA.1, final sentence, p. IA2: the mean-optimal intensity tends to one. -/
theorem solution (p : Params) (hp : p.Standing)
    (hpsi : 0 < p.psi2) :
    Filter.Tendsto (fun T : ℕ => p.kappaE T) Filter.atTop (nhds 1) := by exact mean_limit_core p hp hpsi


#print axioms solution
