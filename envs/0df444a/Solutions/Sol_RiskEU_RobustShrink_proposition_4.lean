-- Prove2me | solution 1 for RiskEU.RobustShrink.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-17T10:33:47.482764+00:00
-- url     : https://prove2.me/submissions/b2e85997-9405-4765-a4e0-99147b4ca2aa

import Definitions.Def_RiskEU_RobustShrink_Setting
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
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
namespace RiskEU.RobustShrink

def Params.curvature (p : Params) (T : ℕ) : ℝ :=
  1/p.gamma*(T:ℝ)/((T:ℝ)-p.N-1)*(p.psi2+((p.N:ℝ)-1)/T)*((T:ℝ)*((T:ℝ)-2))/(2*((T:ℝ)-p.N)*((T:ℝ)-p.N-3))

lemma limit_a1 (p : Params) (hp : p.Standing) :
    Tendsto (fun T : ℕ => p.a1 T) atTop (nhds (0)) := by
  have hg : 0 < p.gamma := hp.2.1
  have hi : Tendsto (fun T : ℕ => (T:ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  let n : ℝ := p.N
  let g := p.gamma
  let v := p.sigmaG2
  let z := p.psi2
  let F : ℝ → ℝ := fun x => ((-1 * x * (-1 + (2 * x)) * ((-1 * x) + (-70 * (x ^ 5)) + (-53 * (x ^ 3)) + (2 * z) + (4 * (z ^ 2)) + (12 * (x ^ 2)) + (100 * (x ^ 4)) + (n * x) + ((n ^ 2) * (x ^ 2)) + ((n ^ 4) * (x ^ 4)) + ((n ^ 5) * (x ^ 5)) + (-200 * z * (x ^ 3)) + (-113 * n * (x ^ 4)) + (-70 * (z ^ 2) * (x ^ 3)) + (-34 * x * (z ^ 2)) + (-28 * (n ^ 3) * (x ^ 5)) + (-24 * z * x) + (-13 * n * (x ^ 2)) + (-9 * (n ^ 2) * (x ^ 4)) + (-4 * (n ^ 3) * (x ^ 3)) + (-4 * (n ^ 4) * (x ^ 5)) + (-3 * (n ^ 2) * (x ^ 3)) + (21 * (n ^ 3) * (x ^ 4)) + (26 * (n ^ 2) * (x ^ 5)) + (60 * n * (x ^ 3)) + (75 * n * (x ^ 5)) + (88 * (z ^ 2) * (x ^ 2)) + (106 * z * (x ^ 2)) + (140 * z * (x ^ 4)) + ((n ^ 3) * (z ^ 2) * (x ^ 3)) + (-62 * z * (n ^ 2) * (x ^ 4)) + (-53 * n * (z ^ 2) * (x ^ 3)) + (-14 * n * z * (x ^ 2)) + (-10 * n * z * (x ^ 4)) + (-8 * z * (n ^ 2) * (x ^ 2)) + (-7 * n * x * (z ^ 2)) + (-6 * z * (n ^ 3) * (x ^ 4)) + (-6 * (n ^ 2) * (z ^ 2) * (x ^ 3)) + (2 * n * z * x) + (2 * z * (n ^ 3) * (x ^ 3)) + (2 * z * (n ^ 4) * (x ^ 4)) + (2 * (n ^ 2) * (z ^ 2) * (x ^ 2)) + (26 * n * z * (x ^ 3)) + (40 * n * (z ^ 2) * (x ^ 2)) + (44 * z * (n ^ 2) * (x ^ 3)))) / ((2 * (g ^ 2)) * ((1-(n+(2))*x)^1) * ((1-(n+(5))*x)^1) * ((1-(n+(7))*x)^1) * ((1-(n+(0))*x)^2) * ((1-(n+(1))*x)^2) * ((1-(n+(3))*x)^2)))
  have hc : ContinuousAt F 0 := by
    dsimp [F]
    fun_prop (disch := simp [g,ne_of_gt hg])
  have hf : F 0 = 0 := by
    dsimp [F,g,z]
    field_simp
    <;> ring
  have hh := hc.tendsto.comp hi
  rw [hf] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (p.N+7)] with T hT
  have hn : (2:ℝ) ≤ p.N := by exact_mod_cast hp.1
  have ht : (p.N:ℝ)+7 < T := by exact_mod_cast hT
  have ht0 : (0:ℝ)<T := by linarith
  have htn : (0:ℝ)<(T:ℝ)-p.N := by linarith
  have ht1 : (0:ℝ)<(T:ℝ)-p.N-1 := by linarith
  have ht2 : (0:ℝ)<(T:ℝ)-p.N-2 := by linarith
  have ht3 : (0:ℝ)<(T:ℝ)-p.N-3 := by linarith
  have ht5 : (0:ℝ)<(T:ℝ)-p.N-5 := by linarith
  have ht7 : (0:ℝ)<(T:ℝ)-p.N-7 := by linarith
  have hnorm (c : ℝ) : 1-((p.N:ℝ)+c)*(T:ℝ)⁻¹ = ((T:ℝ)-p.N-c)/T := by
    field_simp
    <;> ring
  have hnorm0 : 1-(p.N:ℝ)*(T:ℝ)⁻¹ = ((T:ℝ)-p.N)/T := by
    field_simp
    <;> ring
  dsimp [F,n,g,v,z,Params.a1,C]
  simp only [hnorm,hnorm0,sub_zero]
  field_simp
  <;> ring
end RiskEU.RobustShrink

namespace RiskEU.RobustShrink
lemma limit_a2 (p : Params) (hp : p.Standing) :
    Tendsto (fun T : ℕ => p.a2 T) atTop (nhds (0)) := by
  have hg : 0 < p.gamma := hp.2.1
  have hi : Tendsto (fun T : ℕ => (T:ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  let n : ℝ := p.N
  let g := p.gamma
  let v := p.sigmaG2
  let z := p.psi2
  let F : ℝ → ℝ := fun x => ((2 * z * x * (-1 + (2 * x)) * (1 + (-3 * x) + (2 * z) + (n * x))) / ((g ^ 2) * ((1-(n+(0))*x)^1) * ((1-(n+(3))*x)^1) * ((1-(n+(5))*x)^1) * ((1-(n+(1))*x)^2)))
  have hc : ContinuousAt F 0 := by
    dsimp [F]
    fun_prop (disch := simp [g,ne_of_gt hg])
  have hf : F 0 = 0 := by
    dsimp [F,g,z]
    field_simp
    <;> ring
  have hh := hc.tendsto.comp hi
  rw [hf] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (p.N+7)] with T hT
  have hn : (2:ℝ) ≤ p.N := by exact_mod_cast hp.1
  have ht : (p.N:ℝ)+7 < T := by exact_mod_cast hT
  have ht0 : (0:ℝ)<T := by linarith
  have htn : (0:ℝ)<(T:ℝ)-p.N := by linarith
  have ht1 : (0:ℝ)<(T:ℝ)-p.N-1 := by linarith
  have ht2 : (0:ℝ)<(T:ℝ)-p.N-2 := by linarith
  have ht3 : (0:ℝ)<(T:ℝ)-p.N-3 := by linarith
  have ht5 : (0:ℝ)<(T:ℝ)-p.N-5 := by linarith
  have ht7 : (0:ℝ)<(T:ℝ)-p.N-7 := by linarith
  have hnorm (c : ℝ) : 1-((p.N:ℝ)+c)*(T:ℝ)⁻¹ = ((T:ℝ)-p.N-c)/T := by
    field_simp
    <;> ring
  have hnorm0 : 1-(p.N:ℝ)*(T:ℝ)⁻¹ = ((T:ℝ)-p.N)/T := by
    field_simp
    <;> ring
  dsimp [F,n,g,v,z,Params.a2,C]
  simp only [hnorm,hnorm0,sub_zero]
  field_simp
  <;> ring
end RiskEU.RobustShrink

namespace RiskEU.RobustShrink
lemma limit_a3 (p : Params) (hp : p.Standing) :
    Tendsto (fun T : ℕ => p.a3 T) atTop (nhds (0)) := by
  have hg : 0 < p.gamma := hp.2.1
  have hi : Tendsto (fun T : ℕ => (T:ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  let n : ℝ := p.N
  let g := p.gamma
  let v := p.sigmaG2
  let z := p.psi2
  let F : ℝ → ℝ := fun x => ((-1 * x * ((-1 * z) + (-2 * (z ^ 2)) + (-17 * z * (x ^ 2)) + (8 * z * x) + (10 * z * (x ^ 3)) + (10 * x * (z ^ 2)) + (v * x * (g ^ 2)) + (-1 * v * z * (g ^ 2)) + (-1 * z * (n ^ 2) * (x ^ 2)) + (-10 * n * z * (x ^ 2)) + (-10 * n * (z ^ 2) * (x ^ 2)) + (-5 * v * (g ^ 2) * (x ^ 2)) + (-2 * (n ^ 2) * (z ^ 2) * (x ^ 2)) + (2 * n * z * x) + (2 * z * (n ^ 2) * (x ^ 3)) + (4 * n * x * (z ^ 2)) + (6 * v * (g ^ 2) * (x ^ 3)) + (12 * n * z * (x ^ 3)) + (-1 * n * v * x * (g ^ 2)) + (-1 * v * (g ^ 2) * (n ^ 2) * (x ^ 2)) + (-8 * n * v * (g ^ 2) * (x ^ 3)) + (-6 * v * z * (g ^ 2) * (x ^ 2)) + (2 * v * (g ^ 2) * (n ^ 2) * (x ^ 3)) + (5 * v * z * x * (g ^ 2)) + (6 * n * v * (g ^ 2) * (x ^ 2)) + (-1 * n * v * z * x * (g ^ 2)) + (2 * n * v * z * (g ^ 2) * (x ^ 2)))) / ((g ^ 2) * ((1-(n+(0))*x)^1) * ((1-(n+(3))*x)^1) * ((1-(n+(5))*x)^1) * ((1-(n+(1))*x)^2)))
  have hc : ContinuousAt F 0 := by
    dsimp [F]
    fun_prop (disch := simp [g,ne_of_gt hg])
  have hf : F 0 = 0 := by
    dsimp [F,g,z]
    field_simp
    <;> ring
  have hh := hc.tendsto.comp hi
  rw [hf] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (p.N+7)] with T hT
  have hn : (2:ℝ) ≤ p.N := by exact_mod_cast hp.1
  have ht : (p.N:ℝ)+7 < T := by exact_mod_cast hT
  have ht0 : (0:ℝ)<T := by linarith
  have htn : (0:ℝ)<(T:ℝ)-p.N := by linarith
  have ht1 : (0:ℝ)<(T:ℝ)-p.N-1 := by linarith
  have ht2 : (0:ℝ)<(T:ℝ)-p.N-2 := by linarith
  have ht3 : (0:ℝ)<(T:ℝ)-p.N-3 := by linarith
  have ht5 : (0:ℝ)<(T:ℝ)-p.N-5 := by linarith
  have ht7 : (0:ℝ)<(T:ℝ)-p.N-7 := by linarith
  have hnorm (c : ℝ) : 1-((p.N:ℝ)+c)*(T:ℝ)⁻¹ = ((T:ℝ)-p.N-c)/T := by
    field_simp
    <;> ring
  have hnorm0 : 1-(p.N:ℝ)*(T:ℝ)⁻¹ = ((T:ℝ)-p.N)/T := by
    field_simp
    <;> ring
  dsimp [F,n,g,v,z,Params.a3,C]
  simp only [hnorm,hnorm0,sub_zero]
  field_simp
  <;> ring
end RiskEU.RobustShrink

namespace RiskEU.RobustShrink
lemma limit_a4 (p : Params) (hp : p.Standing) :
    Tendsto (fun T : ℕ => p.a4 T) atTop (nhds (0)) := by
  have hg : 0 < p.gamma := hp.2.1
  have hi : Tendsto (fun T : ℕ => (T:ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  let n : ℝ := p.N
  let g := p.gamma
  let v := p.sigmaG2
  let z := p.psi2
  let F : ℝ → ℝ := fun x => ((2 * v * z * x * (-1 + (2 * x))) / (1 * ((1-(n+(3))*x)^1) * ((1-(n+(1))*x)^2)))
  have hc : ContinuousAt F 0 := by
    dsimp [F]
    fun_prop (disch := simp [g,ne_of_gt hg])
  have hf : F 0 = 0 := by
    dsimp [F,g,z]
    field_simp
    <;> ring
  have hh := hc.tendsto.comp hi
  rw [hf] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (p.N+7)] with T hT
  have hn : (2:ℝ) ≤ p.N := by exact_mod_cast hp.1
  have ht : (p.N:ℝ)+7 < T := by exact_mod_cast hT
  have ht0 : (0:ℝ)<T := by linarith
  have htn : (0:ℝ)<(T:ℝ)-p.N := by linarith
  have ht1 : (0:ℝ)<(T:ℝ)-p.N-1 := by linarith
  have ht2 : (0:ℝ)<(T:ℝ)-p.N-2 := by linarith
  have ht3 : (0:ℝ)<(T:ℝ)-p.N-3 := by linarith
  have ht5 : (0:ℝ)<(T:ℝ)-p.N-5 := by linarith
  have ht7 : (0:ℝ)<(T:ℝ)-p.N-7 := by linarith
  have hnorm (c : ℝ) : 1-((p.N:ℝ)+c)*(T:ℝ)⁻¹ = ((T:ℝ)-p.N-c)/T := by
    field_simp
    <;> ring
  have hnorm0 : 1-(p.N:ℝ)*(T:ℝ)⁻¹ = ((T:ℝ)-p.N)/T := by
    field_simp
    <;> ring
  dsimp [F,n,g,v,z,Params.a4,C]
  simp only [hnorm,hnorm0,sub_zero]
  field_simp
  <;> ring
end RiskEU.RobustShrink

namespace RiskEU.RobustShrink
lemma limit_varGMV (p : Params) (hp : p.Standing) :
    Tendsto (fun T : ℕ => p.varGMV T) atTop (nhds (0)) := by
  have hg : 0 < p.gamma := hp.2.1
  have hi : Tendsto (fun T : ℕ => (T:ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  let n : ℝ := p.N
  let g := p.gamma
  let v := p.sigmaG2
  let z := p.psi2
  let F : ℝ → ℝ := fun x => ((v * x * ((2 * z) + (-8 * z * x) + (6 * z * (x ^ 2)) + (-1 * v * x * (g ^ 2)) + (-4 * n * z * x) + (2 * v * (g ^ 2) * (x ^ 2)) + (2 * z * (n ^ 2) * (x ^ 2)) + (8 * n * z * (x ^ 2)) + (n * v * x * (g ^ 2)) + (-2 * n * v * (g ^ 2) * (x ^ 2)))) / (2 * ((1-(n+(3))*x)^1) * ((1-(n+(1))*x)^2)))
  have hc : ContinuousAt F 0 := by
    dsimp [F]
    fun_prop (disch := simp [g,ne_of_gt hg])
  have hf : F 0 = 0 := by
    dsimp [F,g,z]
    field_simp
    <;> ring
  have hh := hc.tendsto.comp hi
  rw [hf] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (p.N+7)] with T hT
  have hn : (2:ℝ) ≤ p.N := by exact_mod_cast hp.1
  have ht : (p.N:ℝ)+7 < T := by exact_mod_cast hT
  have ht0 : (0:ℝ)<T := by linarith
  have htn : (0:ℝ)<(T:ℝ)-p.N := by linarith
  have ht1 : (0:ℝ)<(T:ℝ)-p.N-1 := by linarith
  have ht2 : (0:ℝ)<(T:ℝ)-p.N-2 := by linarith
  have ht3 : (0:ℝ)<(T:ℝ)-p.N-3 := by linarith
  have ht5 : (0:ℝ)<(T:ℝ)-p.N-5 := by linarith
  have ht7 : (0:ℝ)<(T:ℝ)-p.N-7 := by linarith
  have hnorm (c : ℝ) : 1-((p.N:ℝ)+c)*(T:ℝ)⁻¹ = ((T:ℝ)-p.N-c)/T := by
    field_simp
    <;> ring
  have hnorm0 : 1-(p.N:ℝ)*(T:ℝ)⁻¹ = ((T:ℝ)-p.N)/T := by
    field_simp
    <;> ring
  dsimp [F,n,g,v,z,Params.varGMV,C]
  simp only [hnorm,hnorm0,sub_zero]
  field_simp
  <;> ring
end RiskEU.RobustShrink

namespace RiskEU.RobustShrink
lemma limit_curvature (p : Params) (hp : p.Standing) :
    Tendsto (fun T : ℕ => p.curvature T) atTop (nhds (p.psi2/(2*p.gamma))) := by
  have hg : 0 < p.gamma := hp.2.1
  have hi : Tendsto (fun T : ℕ => (T:ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  let n : ℝ := p.N
  let g := p.gamma
  let v := p.sigmaG2
  let z := p.psi2
  let F : ℝ → ℝ := fun x => ((-1 * (-1 + (2 * x)) * (z + (-1 * x) + (n * x))) / ((2 * g) * ((1-(n+(0))*x)^1) * ((1-(n+(1))*x)^1) * ((1-(n+(3))*x)^1)))
  have hc : ContinuousAt F 0 := by
    dsimp [F]
    fun_prop (disch := simp [g,ne_of_gt hg])
  have hf : F 0 = p.psi2/(2*p.gamma) := by
    dsimp [F,g,z]
    field_simp
    <;> ring
  have hh := hc.tendsto.comp hi
  rw [hf] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (p.N+7)] with T hT
  have hn : (2:ℝ) ≤ p.N := by exact_mod_cast hp.1
  have ht : (p.N:ℝ)+7 < T := by exact_mod_cast hT
  have ht0 : (0:ℝ)<T := by linarith
  have htn : (0:ℝ)<(T:ℝ)-p.N := by linarith
  have ht1 : (0:ℝ)<(T:ℝ)-p.N-1 := by linarith
  have ht2 : (0:ℝ)<(T:ℝ)-p.N-2 := by linarith
  have ht3 : (0:ℝ)<(T:ℝ)-p.N-3 := by linarith
  have ht5 : (0:ℝ)<(T:ℝ)-p.N-5 := by linarith
  have ht7 : (0:ℝ)<(T:ℝ)-p.N-7 := by linarith
  have hnorm (c : ℝ) : 1-((p.N:ℝ)+c)*(T:ℝ)⁻¹ = ((T:ℝ)-p.N-c)/T := by
    field_simp
    <;> ring
  have hnorm0 : 1-(p.N:ℝ)*(T:ℝ)⁻¹ = ((T:ℝ)-p.N)/T := by
    field_simp
    <;> ring
  dsimp [F,n,g,v,z,Params.curvature,C]
  simp only [hnorm,hnorm0,sub_zero]
  field_simp
  <;> ring
end RiskEU.RobustShrink

namespace RiskEU.RobustShrink
lemma curvature_pos (p : Params) (hp : p.Standing) (T : ℕ) (hT : p.N+7<T) :
    0 < p.curvature T := by
  obtain ⟨hn,ht⟩ := sample_bounds p hp T hT
  have hg : 0 < p.gamma := hp.2.1
  have hz : 0 ≤ p.psi2 := hp.2.2.2.1
  have ht0 : (0:ℝ)<T := by linarith
  have ht2 : (0:ℝ)<(T:ℝ)-2 := by linarith
  have hn0 : (0:ℝ)<(T:ℝ)-p.N := by linarith
  have hn1 : (0:ℝ)<(T:ℝ)-p.N-1 := by linarith
  have hn3 : (0:ℝ)<(T:ℝ)-p.N-3 := by linarith
  have hnpos : (0:ℝ)<(p.N:ℝ)-1 := by linarith
  dsimp [Params.curvature]
  positivity

lemma mean_gap (p : Params) (hp : p.Standing) (T : ℕ) (hT : p.N+7<T) (k : ℝ) :
    p.oosuMean T (p.kappaE T)-p.oosuMean T k = p.curvature T*(k-p.kappaE T)^2 := by
  obtain ⟨hn,ht⟩ := sample_bounds p hp T hT
  have hg : 0 < p.gamma := hp.2.1
  have hz : 0 ≤ p.psi2 := hp.2.2.2.1
  have ht0 : (0:ℝ)<T := by linarith
  have ht2 : (0:ℝ)<(T:ℝ)-2 := by linarith
  have hn0 : (0:ℝ)<(T:ℝ)-p.N := by linarith
  have hn1 : (0:ℝ)<(T:ℝ)-p.N-1 := by linarith
  have hn3 : (0:ℝ)<(T:ℝ)-p.N-3 := by linarith
  have hsum : 0 < (p.N:ℝ)+(T:ℝ)*p.psi2-1 := by nlinarith [mul_nonneg ht0.le hz]
  have hpsi_id : p.psi2+((p.N:ℝ)-1)/T = ((p.N:ℝ)+(T:ℝ)*p.psi2-1)/T := by field_simp; ring
  have hek : p.kappaE T = ((T:ℝ)-p.N)*((T:ℝ)-p.N-3)*p.psi2 / (((T:ℝ)-2)*((p.N:ℝ)+(T:ℝ)*p.psi2-1)) := by
    dsimp [Params.kappaE]
    rw [hpsi_id]
    field_simp
    <;> ring
  unfold Params.oosuMean Params.curvature
  simp only [hek,hpsi_id]
  field_simp
  <;> ring

lemma variance_at_mean_limit (p : Params) (hp : p.Standing) (hpsi : 0 < p.psi2) :
    Tendsto (fun T : ℕ => p.oosuVar T (p.kappaE T)) atTop (nhds 0) := by
  have he := mean_limit_core p hp hpsi
  have h := (limit_varGMV p hp).add (((((limit_a1 p hp).mul (he.pow 4)).add
    ((limit_a2 p hp).mul (he.pow 3))).add ((limit_a3 p hp).mul (he.pow 2))).add
    ((limit_a4 p hp).mul he))
  simpa [Params.oosuVar,Params.Delta] using h
end RiskEU.RobustShrink
namespace RiskEU.RobustShrink
lemma robust_limit_core (p : Params) (hp : p.Standing) (hpsi : 0 < p.psi2)
    (kappaR : ℕ → ℝ)
    (hk : ∀ T : ℕ, p.N+7<T → kappaR T ∈ Set.Icc (0:ℝ) 1 ∧
      IsMaxOn (p.meanRisk T) (Set.Icc (0:ℝ) 1) (kappaR T)) :
    Tendsto kappaR atTop (nhds 1) := by
  have hq : 0 < p.psi2/(2*p.gamma) := div_pos hpsi (mul_pos (by norm_num) hp.2.1)
  have hnum := (Real.continuous_sqrt.tendsto 0).comp (variance_at_mean_limit p hp hpsi)
  simp only [Real.sqrt_zero] at hnum
  have hupper : Tendsto (fun T : ℕ => p.lam * Real.sqrt (p.oosuVar T (p.kappaE T)) / p.curvature T) atTop (nhds 0) := by
    have h := (hnum.const_mul p.lam).div (limit_curvature p hp) (ne_of_gt hq)
    change Tendsto (fun T => p.lam * Real.sqrt (p.oosuVar T (p.kappaE T)) / p.curvature T) atTop (nhds (p.lam*0/(p.psi2/(2*p.gamma)))) at h
    simpa only [mul_zero,zero_div] using h
  have hb : ∀ᶠ T : ℕ in atTop, (kappaR T-p.kappaE T)^2 ≤
      p.lam * Real.sqrt (p.oosuVar T (p.kappaE T)) / p.curvature T := by
    filter_upwards [eventually_gt_atTop (p.N+7)] with T hT
    have hm := (hk T hT).2 (mean_vertex_core p hp T hT).1
    have hn : 0 ≤ p.lam*Real.sqrt (p.oosuVar T (kappaR T)) :=
      mul_nonneg hp.2.2.2.2 (Real.sqrt_nonneg _)
    have hg := mean_gap p hp T hT (kappaR T)
    apply (le_div_iff₀ (curvature_pos p hp T hT)).mpr
    change p.meanRisk T (p.kappaE T) ≤ p.meanRisk T (kappaR T) at hm
    unfold Params.meanRisk at hm
    nlinarith only [hm,hn,hg]
  have hs : Tendsto (fun T : ℕ => (kappaR T-p.kappaE T)^2) atTop (nhds 0) :=
    squeeze_zero' (Eventually.of_forall (fun T => sq_nonneg _)) hb hupper
  have ha := (Real.continuous_sqrt.tendsto 0).comp hs
  simp only [Real.sqrt_zero,Function.comp_def,Real.sqrt_sq_eq_abs] at ha
  have hd : Tendsto (fun T : ℕ => kappaR T-p.kappaE T) atTop (nhds 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).mpr ha
  have h := hd.add (mean_limit_core p hp hpsi)
  simpa using h
end RiskEU.RobustShrink
namespace RiskEU.RobustShrink
lemma ordering_of_strict_variance (p : Params) (hp : p.Standing) (T : ℕ) (hT : p.N+7<T)
    (hmono : StrictMonoOn (p.oosuVar T) (Set.Ici (p.kappaE T)))
    (V R : ℝ) (hV : V∈Set.Icc (0:ℝ) 1)
    (hmin : IsMinOn (p.oosuVar T) (Set.Icc (0:ℝ) 1) V)
    (hR : R∈Set.Icc (0:ℝ) 1)
    (hmax : IsMaxOn (p.meanRisk T) (Set.Icc (0:ℝ) 1) R) :
    V≤R ∧ R≤p.kappaE T := by
  have hE := (mean_vertex_core p hp T hT).1
  have hQ := curvature_pos p hp T hT
  have hVle : V≤p.kappaE T := by
    by_contra h
    have hv : p.kappaE T<V := lt_of_not_ge h
    have hh := hmono (show p.kappaE T∈Set.Ici (p.kappaE T) by simp) hv.le hv
    have hm := hmin hE
    change p.oosuVar T V≤p.oosuVar T (p.kappaE T) at hm
    linarith
  have hRle : R≤p.kappaE T := by
    by_contra h
    have hr : p.kappaE T<R := lt_of_not_ge h
    have hvar := (hmono.monotoneOn) (show p.kappaE T∈Set.Ici (p.kappaE T) by simp) hr.le hr.le
    have hpen := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hvar) hp.2.2.2.2
    have hgap := mean_gap p hp T hT R
    have hs : 0<(R-p.kappaE T)^2 := sq_pos_of_pos (sub_pos.mpr hr)
    have hh := mul_pos hQ hs
    have hm := hmax hE
    change p.meanRisk T (p.kappaE T)≤p.meanRisk T R at hm
    dsimp [Params.meanRisk] at hm
    linarith
  refine ⟨?_,hRle⟩
  by_contra h
  have hr : R<V := lt_of_not_ge h
  have hvar := hmin hR
  change p.oosuVar T V≤p.oosuVar T R at hvar
  have hpen := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hvar) hp.2.2.2.2
  have hgapR := mean_gap p hp T hT R
  have hgapV := mean_gap p hp T hT V
  have hs : (V-p.kappaE T)^2<(R-p.kappaE T)^2 := by
    have hp' := mul_pos (sub_pos.mpr hr) (show 0<2*p.kappaE T-R-V by linarith)
    nlinarith
  have hh := mul_lt_mul_of_pos_left hs hQ
  have hm := hmax hV
  change p.meanRisk T V≤p.meanRisk T R at hm
  dsimp [Params.meanRisk] at hm
  linarith
end RiskEU.RobustShrink

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace RiskEU.RobustShrink.Certificates
private def P_a1 (b u z g v : ℝ) : ℝ :=
  (714420 + (z * (12859560 + (19289340 * z))) + (b * (1356264 + (z * (12982032 + (15186528 * z))) + (b * (860076 + (z * (5211864 + (4919292 * z))) + (b * (253680 + (z * (1074528 + (840672 * z))) + (b * (38220 + (z * (120792 + (80052 * z))) + (b * (2856 + (z * (7056 + (4032 * z))) + (b * (84 + (z * (168 + (84 * z))) + (u * (42 + (z * (84 + (42 * z))) + (u * (5 + (z * (10 + (5 * z))))))))) + (u * (1764 + (z * (4368 + (2510 * z))) + (u * (338 + (z * (840 + (485 * z))) + (u * (20 + (z * (50 + (29 * z))))))))))) + (u * (28054 + (z * (89204 + (59756 * z))) + (u * (7269 + (z * (23310 + (15754 * z))) + (u * (793 + (z * (2572 + (1752 * z))) + (u * (31 + (z * (102 + (70 * z))))))))))))) + (u * (214904 + (z * (922016 + (733164 * z))) + (u * (69296 + (z * (302232 + (243578 * z))) + (u * (10704 + (z * (47648 + (38858 * z))) + (u * (797 + (z * (3636 + (2998 * z))) + (u * (23 + (z * (108 + (90 * z))))))))))))))) + (u * (819670 + (z * (5092956 + (4918482 * z))) + (u * (311947 + (z * (1998798 + (1967769 * z))) + (u * (61010 + (z * (405636 + (406200 * z))) + (u * (6495 + (z * (45108 + (45890 * z))) + (u * (358 + (z * (2616 + (2702 * z))) + (u * (8 + (z * (62 + (65 * z))))))))))))))))) + (u * (1414692 + (z * (14210640 + (17162118 * z))) + (u * (607454 + (z * (6470496 + (8030097 * z))) + (u * (139604 + (z * (1595646 + (2029281 * z))) + (u * (18575 + (z * (230972 + (300530 * z))) + (u * (1431 + (z * (19680 + (26176 * z))) + (u * (59 + (z * (916 + (1245 * z))) + (u * (1 + (z * (18 + (25 * z))))))))))))))))))) + (u * (783594 + (z * (15533532 + (24371928 * z))) + (u * (357867 + (z * (8008794 + (13069512 * z))) + (u * (88525 + (z * (2309184 + (3906360 * z))) + (u * (12846 + (z * (408278 + (714624 * z))) + (u * (1096 + (z * (45420 + (82184 * z))) + (u * (51 + (z * (3110 + (5816 * z))) + (u * (1 + (z * (120 + (232 * z))) + (z * u * (2 + (4 * z))))))))))))))))))

lemma a1_sign (p : Params) (hp : p.Standing) (T : ℕ) (hT : p.N+7<T) :
    0 < p.a1 T := by
  have hn : (2:ℝ) ≤ p.N := by exact_mod_cast hp.1
  have ht : (p.N:ℝ)+7 < T := by exact_mod_cast hT
  have hg : 0 < p.gamma := hp.2.1
  have hv : 0 < p.sigmaG2 := hp.2.2.1
  have hz : 0 ≤ p.psi2 := hp.2.2.2.1
  let b : ℝ := (p.N:ℝ)-2
  let u : ℝ := (T:ℝ)-p.N-7
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hu : 0 < u := by dsimp [u]; linarith
  have ht0 : (0:ℝ)<T := by linarith
  have ht2 : (0:ℝ)<(T:ℝ)-2 := by linarith
  have hn0 : (0:ℝ)<(T:ℝ)-p.N := by linarith
  have hn1 : (0:ℝ)<(T:ℝ)-p.N-1 := by linarith
  have hn2 : (0:ℝ)<(T:ℝ)-p.N-2 := by linarith
  have hn3 : (0:ℝ)<(T:ℝ)-p.N-3 := by linarith
  have hn5 : (0:ℝ)<(T:ℝ)-p.N-5 := by linarith
  have hn7 : (0:ℝ)<(T:ℝ)-p.N-7 := by linarith
  have hpsi : 0 < p.psi2+((p.N:ℝ)-1)/T := by
    apply add_pos_of_nonneg_of_pos hz
    apply div_pos _ ht0
    linarith
  let z := p.psi2
  let g := p.gamma
  let v := p.sigmaG2
  have hz' : 0 ≤ z := hz
  have hg' : 0 < g := hg
  have hv' : 0 < v := hv
  have hsum : 0 < (p.N:ℝ)+(T:ℝ)*p.psi2-1 := by
    nlinarith [mul_nonneg ht0.le hz]
  have hpsi_id : p.psi2+((p.N:ℝ)-1)/T = ((p.N:ℝ)+(T:ℝ)*p.psi2-1)/T := by
    field_simp
    <;> ring
  have hek : p.kappaE T = ((T:ℝ)-p.N)*((T:ℝ)-p.N-3)*p.psi2 / (((T:ℝ)-2)*((p.N:ℝ)+(T:ℝ)*p.psi2-1)) := by
    dsimp [Params.kappaE]
    rw [hpsi_id]
    field_simp
    <;> ring
  have hd : (2 * u * (g ^ 2) * ((4 + u) ^ 2) * ((6 + u) ^ 2) * ((7 + u) ^ 2) * (2 + u) * (5 + u)) = 2*p.gamma^2*((T:ℝ)-p.N)^2*((T:ℝ)-p.N-1)^2*((T:ℝ)-p.N-2)*((T:ℝ)-p.N-3)^2*((T:ℝ)-p.N-5)*((T:ℝ)-p.N-7) := by
    dsimp [b,u,z,g,v]
    ring
  have hid : p.a1 T = P_a1 b u z g v / (2 * u * (g ^ 2) * ((4 + u) ^ 2) * ((6 + u) ^ 2) * ((7 + u) ^ 2) * (2 + u) * (5 + u)) := by
    rw [hd]
    try simp only [hek]
    dsimp [P_a1,Params.a1,Params.a2,Params.a3,Params.a4,C,b,u,z,g,v]
    field_simp
    <;> ring
  rw [hid]
  apply div_pos
  · dsimp [P_a1]
    positivity
  · positivity
end RiskEU.RobustShrink.Certificates

namespace RiskEU.RobustShrink.Certificates
private def P_c3 (b u z g v : ℝ) : ℝ :=
  ((z * (34020 + (z * (612360 + (918540 * z))))) + (b * ((z * (59724 + (z * (530712 + (591948 * z))))) + (b * ((z * (32424 + (z * (172368 + (149688 * z))))) + (b * ((z * (7448 + (z * (26544 + (18648 * z))))) + (b * ((z * (756 + (z * (1960 + (1148 * z))))) + (b * ((z * (28 + (z * (56 + (28 * z))))) + (z * u * (6 + (z * (12 + (6 * z))))))) + (u * ((z * (236 + (z * (634 + (376 * z))))) + (z * u * (16 + (z * (46 + (28 * z))))))))) + (u * ((z * (3000 + (z * (11476 + (8228 * z))))) + (u * ((z * (368 + (z * (1560 + (1152 * z))))) + (z * u * (14 + (z * (68 + (52 * z))))))))))) + (u * ((z * (15580 + (z * (93240 + (83160 * z))))) + (u * ((z * (2592 + (z * (18240 + (16824 * z))))) + (u * ((z * (176 + (z * (1544 + (1480 * z))))) + (z * u * (4 + (z * (48 + (48 * z))))))))))))) + (u * ((z * (32034 + (z * (344736 + (397062 * z))))) + (u * ((z * (6224 + (z * (87408 + (104544 * z))))) + (u * ((z * (522 + (z * (10864 + (13556 * z))))) + (u * ((z * (16 + (z * (664 + (868 * z))))) + (u * (z ^ 2) * (16 + (22 * z))))))))))))) + (u * ((z * (19224 + (z * (465102 + (723168 * z))))) + (u * ((z * (3984 + (z * (144666 + (234252 * z))))) + (u * ((z * (360 + (z * (23628 + (40032 * z))))) + (u * ((z * (12 + (z * (2140 + (3812 * z))))) + (u * (((z ^ 2) * (102 + (192 * z))) + (u * (z ^ 2) * (2 + (4 * z))))))))))))))

lemma c3_sign (p : Params) (hp : p.Standing) (T : ℕ) (hT : p.N+7<T) :
    0 ≤ 4*p.a1 T*p.kappaE T+p.a2 T := by
  have hn : (2:ℝ) ≤ p.N := by exact_mod_cast hp.1
  have ht : (p.N:ℝ)+7 < T := by exact_mod_cast hT
  have hg : 0 < p.gamma := hp.2.1
  have hv : 0 < p.sigmaG2 := hp.2.2.1
  have hz : 0 ≤ p.psi2 := hp.2.2.2.1
  let b : ℝ := (p.N:ℝ)-2
  let u : ℝ := (T:ℝ)-p.N-7
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hu : 0 < u := by dsimp [u]; linarith
  have ht0 : (0:ℝ)<T := by linarith
  have ht2 : (0:ℝ)<(T:ℝ)-2 := by linarith
  have hn0 : (0:ℝ)<(T:ℝ)-p.N := by linarith
  have hn1 : (0:ℝ)<(T:ℝ)-p.N-1 := by linarith
  have hn2 : (0:ℝ)<(T:ℝ)-p.N-2 := by linarith
  have hn3 : (0:ℝ)<(T:ℝ)-p.N-3 := by linarith
  have hn5 : (0:ℝ)<(T:ℝ)-p.N-5 := by linarith
  have hn7 : (0:ℝ)<(T:ℝ)-p.N-7 := by linarith
  have hpsi : 0 < p.psi2+((p.N:ℝ)-1)/T := by
    apply add_pos_of_nonneg_of_pos hz
    apply div_pos _ ht0
    linarith
  let z := p.psi2
  let g := p.gamma
  let v := p.sigmaG2
  have hz' : 0 ≤ z := hz
  have hg' : 0 < g := hg
  have hv' : 0 < v := hv
  have hsum : 0 < (p.N:ℝ)+(T:ℝ)*p.psi2-1 := by
    nlinarith [mul_nonneg ht0.le hz]
  have hpsi_id : p.psi2+((p.N:ℝ)-1)/T = ((p.N:ℝ)+(T:ℝ)*p.psi2-1)/T := by
    field_simp
    <;> ring
  have hek : p.kappaE T = ((T:ℝ)-p.N)*((T:ℝ)-p.N-3)*p.psi2 / (((T:ℝ)-2)*((p.N:ℝ)+(T:ℝ)*p.psi2-1)) := by
    dsimp [Params.kappaE]
    rw [hpsi_id]
    field_simp
    <;> ring
  have hd : (u * (g ^ 2) * (2 + u) * (4 + u) * (5 + u) * (6 + u) * (7 + u) * (1 + b + (9 * z) + (z * b) + (z * u))) = p.gamma^2*((T:ℝ)-p.N)*((T:ℝ)-p.N-7)*((T:ℝ)-p.N-5)*((T:ℝ)-p.N-3)*((T:ℝ)-p.N-2)*((T:ℝ)-p.N-1)*((p.N:ℝ)+(T:ℝ)*p.psi2-1) := by
    dsimp [b,u,z,g,v]
    ring
  have hid : 4*p.a1 T*p.kappaE T+p.a2 T = P_c3 b u z g v / (u * (g ^ 2) * (2 + u) * (4 + u) * (5 + u) * (6 + u) * (7 + u) * (1 + b + (9 * z) + (z * b) + (z * u))) := by
    rw [hd]
    try simp only [hek]
    dsimp [P_c3,Params.a1,Params.a2,Params.a3,Params.a4,C,b,u,z,g,v]
    field_simp
    <;> ring
  rw [hid]
  apply div_nonneg
  · dsimp [P_c3]
    positivity
  · positivity
end RiskEU.RobustShrink.Certificates

namespace RiskEU.RobustShrink.GammaCertificates
private def a31 (p : Params) (T : ℕ) : ℝ :=
  p.psi2 / p.gamma^2 * (2*(T:ℝ)*((p.N:ℝ)+1)+(T:ℝ)^2*((T:ℝ)-p.N-3+2*((T:ℝ)-p.N)*p.psi2)) /
    (((T:ℝ)-p.N)*((T:ℝ)-p.N-1)^2*((T:ℝ)-p.N-3))
private def P_g1 (b u z g : ℝ) : ℝ :=
  ((b * ((b * ((b * ((b * ((b * ((u * ((z * (20 + (z * (376 + (z * (692 + (336 * z))))))) + (u * ((z * (14 + (z * (74 + (z * (106 + (46 * z))))))) + (z * u * (2 + (z * (6 + (z * (6 + (2 * z))))))))))) + ((z ^ 2) * (784 + (z * (1568 + (784 * z))))))) + (u * ((z * (500 + (z * (11904 + (z * (29772 + (17136 * z))))))) + (u * ((z * (410 + (z * (2836 + (z * (6084 + (3304 * z))))))) + (u * ((z * (92 + (z * (340 + (z * (564 + (272 * z))))))) + (z * u * (6 + (z * (16 + (z * (20 + (8 * z))))))))))))) + ((z ^ 2) * (21168 + (z * (54880 + (32144 * z))))))) + (u * ((z * (4440 + (z * (131808 + (z * (477192 + (332192 * z))))))) + (u * ((z * (4148 + (z * (35808 + (z * (121176 + (81908 * z))))))) + (u * ((z * (1232 + (z * (5336 + (z * (15288 + (9748 * z))))))) + (u * ((z * (146 + (z * (426 + (z * (960 + (556 * z))))))) + (z * u * (6 + (z * (14 + (z * (24 + (12 * z))))))))))))))) + ((z ^ 2) * (208544 + (z * (743232 + (522144 * z))))))) + (u * ((z * (16280 + (z * (618064 + (z * (3572568 + (3090528 * z))))))) + (u * ((z * (16796 + (z * (179532 + (z * (1079508 + (922296 * z))))))) + (u * ((z * (5988 + (z * (29404 + (z * (170336 + (142000 * z))))))) + (u * ((z * (966 + (z * (2912 + (z * (14768 + (11808 * z))))))) + (u * ((z * (72 + (z * (164 + (z * (664 + (496 * z))))))) + (z * u * (2 + (z * (4 + (z * (12 + (8 * z))))))))))))))))) + ((z ^ 2) * (907872 + (z * (4826304 + (4191264 * z))))))) + (u * ((z * (21140 + (z * (1172136 + (z * (12462660 + (13852944 * z))))))) + (u * ((z * (22718 + (z * (334934 + (z * (4361886 + (4823118 * z))))))) + (u * ((z * (8638 + (z * (50418 + (z * (822058 + (902234 * z))))))) + (u * ((z * (1518 + (z * (4278 + (z * (89364 + (97068 * z))))))) + (u * ((z * (126 + (z * (198 + (z * (5520 + (5908 * z))))))) + (u * ((z * (4 + (z * (4 + (z * (174 + (182 * z))))))) + (u * (z ^ 3) * (2 + (2 * z))))))))))))))) + ((z ^ 2) * (1672272 + (z * (14859936 + (16574544 * z))))))) + (u * ((z * (8820 + (z * (674352 + (z * (16186716 + (23922864 * z))))))) + (u * ((z * (9674 + (z * (188448 + (z * (6496200 + (9451728 * z))))))) + (u * ((z * (3792 + (z * (26016 + (z * (1437780 + (2057904 * z))))))) + (u * ((z * (692 + (z * (1776 + (z * (189648 + (266864 * z))))))) + (u * ((z * (60 + (z * (48 + (z * (14916 + (20624 * z))))))) + (u * ((z * (2 + ((z ^ 2) * (648 + (880 * z))))) + (u * (z ^ 3) * (12 + (16 * z))))))))))))))) + ((z ^ 2) * (952560 + (z * (17146080 + (25719120 * z))))))

lemma g1_sign (p : Params) (hp : p.Standing) (T : ℕ) (hT : p.N+7<T) :
    0 ≤ 4*p.a1 T*(p.kappaE T)^2+3*p.a2 T*p.kappaE T+2*a31 p T := by
  have hn : (2:ℝ) ≤ p.N := by exact_mod_cast hp.1
  have ht : (p.N:ℝ)+7 < T := by exact_mod_cast hT
  have hg : 0 < p.gamma := hp.2.1
  have hv : 0 < p.sigmaG2 := hp.2.2.1
  have hz : 0 ≤ p.psi2 := hp.2.2.2.1
  obtain ⟨b,hbdef⟩ : ∃b:ℝ,b=(p.N:ℝ)-2 := ⟨_,rfl⟩
  obtain ⟨u,hudef⟩ : ∃u:ℝ,u=(T:ℝ)-p.N-7 := ⟨_,rfl⟩
  have hb : 0 ≤ b := by rw [hbdef];linarith
  have hu : 0 < u := by rw [hudef];linarith
  have ht0 : (0:ℝ)<T := by linarith
  have ht2 : (0:ℝ)<(T:ℝ)-2 := by linarith
  have hn0 : (0:ℝ)<(T:ℝ)-p.N := by linarith
  have hn1 : (0:ℝ)<(T:ℝ)-p.N-1 := by linarith
  have hn2 : (0:ℝ)<(T:ℝ)-p.N-2 := by linarith
  have hn3 : (0:ℝ)<(T:ℝ)-p.N-3 := by linarith
  have hn5 : (0:ℝ)<(T:ℝ)-p.N-5 := by linarith
  have hn7 : (0:ℝ)<(T:ℝ)-p.N-7 := by linarith
  have hpsi : 0 < p.psi2+((p.N:ℝ)-1)/T := by
    apply add_pos_of_nonneg_of_pos hz
    apply div_pos _ ht0
    linarith
  let z := p.psi2
  let g := p.gamma
  let v := p.sigmaG2
  have hz' : 0 ≤ z := hz
  have hg' : 0 < g := hg
  have hv' : 0 < v := hv
  have hsum : 0 < (p.N:ℝ)+(T:ℝ)*p.psi2-1 := by
    nlinarith [mul_nonneg ht0.le hz]
  have hpsi_id : p.psi2+((p.N:ℝ)-1)/T = ((p.N:ℝ)+(T:ℝ)*p.psi2-1)/T := by
    field_simp
    <;> ring
  have hek : p.kappaE T = ((T:ℝ)-p.N)*((T:ℝ)-p.N-3)*p.psi2 / (((T:ℝ)-2)*((p.N:ℝ)+(T:ℝ)*p.psi2-1)) := by
    dsimp [Params.kappaE]
    rw [hpsi_id]
    field_simp
    <;> ring
  have hid : 4*p.a1 T*(p.kappaE T)^2+3*p.a2 T*p.kappaE T+2*a31 p T = P_g1 b u z g / (u * (g ^ 2) * ((1 + b + (9 * z) + (z * b) + (z * u)) ^ 2) * (2 + u) * (4 + u) * (5 + u) * (6 + u) * (7 + u) * (7 + b + u)) := by
    have hnr : (p.N:ℝ)=b+2 := by rw [hbdef];ring
    have htr : (T:ℝ)=b+u+9 := by rw [hbdef,hudef];ring
    rw [hek]
    dsimp [Params.a1,Params.a2,a31,C]
    rw [hnr,htr]
    dsimp [P_g1,z,g]
    have hshift : b+u+9-(b+2) = 7+u := by ring
    have hshift2 : b+u+9-2 = 7+b+u := by ring
    have hshiftpsi : b+2+(b+u+9)*p.psi2-1 = 1+b+9*p.psi2+p.psi2*b+p.psi2*u := by ring
    simp only [hshift, hshift2, hshiftpsi]
    have h1 : 7+u-1=6+u := by ring
    have h2 : 7+u-2=5+u := by ring
    have h3 : 7+u-3=4+u := by ring
    have h5 : 7+u-5=2+u := by ring
    have h7 : 7+u-7=u := by ring
    simp only [h1,h2,h3,h5,h7]
    field_simp (disch := positivity)
    <;> ring
  rw [hid]
  apply div_nonneg
  · dsimp [P_g1];positivity
  · positivity
end RiskEU.RobustShrink.GammaCertificates

namespace RiskEU.RobustShrink.GammaCertificates
private def P_g2 (b u z g : ℝ) : ℝ :=
  ((b * ((b * ((b * ((b * ((b * ((b * ((u * ((z * (60 + (z * (4940 + (z * (14460 + (z * (14340 + (4760 * z))))))))) + (u * ((z * (52 + (z * (1336 + (z * (3696 + (z * (3592 + (1180 * z))))))))) + (u * ((z * (13 + (z * (166 + (z * (420 + (z * (394 + (127 * z))))))))) + (z * u * (1 + (z * (8 + (z * (18 + (z * (16 + (5 * z))))))))))))))) + ((z ^ 2) * (7056 + (z * (21168 + (z * (21168 + (7056 * z))))))))) + (u * ((z * (1560 + (z * (155528 + (z * (596232 + (z * (718680 + (276416 * z))))))))) + (u * ((z * (1532 + (z * (49516 + (z * (184356 + (z * (221258 + (84886 * z))))))))) + (u * ((z * (494 + (z * (7972 + (z * (28146 + (z * (33425 + (12757 * z))))))))) + (u * ((z * (65 + (z * (647 + (z * (2121 + (z * (2477 + (938 * z))))))))) + (z * u * (3 + (z * (21 + (z * (63 + (z * (72 + (27 * z))))))))))))))))) + ((z ^ 2) * (197568 + (z * (762048 + (z * (917280 + (352800 * z))))))))) + (u * ((z * (14820 + (z * (1785156 + (z * (9461556 + (z * (14327052 + (6514200 * z))))))))) + (u * ((z * (16144 + (z * (641860 + (z * (3405132 + (z * (5210338 + (2377210 * z))))))))) + (u * ((z * (6251 + (z * (123092 + (z * (642276 + (z * (992075 + (454190 * z))))))))) + (u * ((z * (1118 + (z * (13268 + (z * (66906 + (z * (104285 + (47930 * z))))))))) + (u * ((z * (94 + (z * (760 + (z * (3645 + (z * (5737 + (2650 * z))))))))) + (z * u * (3 + (z * (18 + (z * (81 + (z * (129 + (60 * z))))))))))))))))))) + ((z ^ 2) * (2067408 + (z * (10774512 + (z * (16122960 + (7302960 * z))))))))) + (u * ((z * (62160 + (z * (9275312 + (z * (72830256 + (z * (144978192 + (80015040 * z))))))))) + (u * ((z * (73192 + (z * (3622456 + (z * (29644152 + (z * (60620676 + (33744060 * z))))))))) + (u * ((z * (32132 + (z * (775584 + (z * (6563028 + (z * (13837162 + (7780850 * z))))))))) + (u * ((z * (6946 + (z * (98186 + (z * (852048 + (z * (1861710 + (1059860 * z))))))))) + (u * ((z * (790 + (z * (7328 + (z * (64707 + (z * (147602 + (85320 * z))))))))) + (u * ((z * (45 + (z * (297 + (z * (2652 + (z * (6382 + (3760 * z))))))))) + (z * u * (1 + (z * (5 + (z * (45 + (z * (116 + (70 * z))))))))))))))))))))) + ((z ^ 2) * (10047744 + (z * (75188736 + (z * (146059200 + (80015040 * z))))))))) + (u * ((z * (112260 + (z * (22322516 + (z * (279358308 + (z * (779370012 + (541122120 * z))))))))) + (u * ((z * (137252 + (z * (9107584 + (z * (125508600 + (z * (367385004 + (258454800 * z))))))))) + (u * ((z * (63635 + (z * (2046310 + (z * (31395564 + (z * (97320816 + (69564195 * z))))))))) + (u * ((z * (14765 + (z * (273716 + (z * (4764744 + (z * (15840558 + (11544425 * z))))))))) + (u * ((z * (1836 + (z * (21816 + (z * (446679 + (z * (1621412 + (1210030 * z))))))))) + (u * ((z * (117 + (z * (960 + (z * (25023 + (z * (101840 + (78250 * z))))))))) + (u * ((z * (3 + (z * (18 + (z * (753 + (z * (3584 + (2855 * z))))))))) + (u * (z ^ 3) * (9 + (z * (54 + (45 * z))))))))))))))))))) + ((z ^ 2) * (23221296 + (z * (265764240 + (z * (711562320 + (488663280 * z))))))))) + (u * ((z * (89880 + (z * (23211720 + (z * (484295112 + (z * (2080921752 + (1910563200 * z))))))))) + (u * ((z * (112156 + (z * (9675676 + (z * (234470052 + (z * (1089706770 + (1017705870 * z))))))))) + (u * ((z * (53486 + (z * (2219372 + (z * (64049418 + (z * (327577653 + (312328953 * z))))))))) + (u * ((z * (12845 + (z * (302759 + (z * (10798263 + (z * (62265381 + (60876810 * z))))))))) + (u * ((z * (1663 + (z * (24583 + (z * (1150614 + (z * (7754542 + (7816981 * z))))))))) + (u * ((z * (111 + (z * (1101 + (z * (75672 + (z * (631988 + (661370 * z))))))))) + (u * ((z * (3 + (z * (21 + (z * (2808 + (z * (32441 + (35555 * z))))))))) + (u * (((z ^ 3) * (45 + (z * (949 + (1102 * z))))) + (u * (z ^ 4) * (12 + (15 * z))))))))))))))))))) + ((z ^ 2) * (23623488 + (z * (432081216 + (z * (1738612512 + (1574010144 * z))))))))) + (u * ((z * (26460 + (z * (8529948 + (z * (268887276 + (z * (2105109972 + (2747904264 * z))))))))) + (u * ((z * (33432 + (z * (3596868 + (z * (135381132 + (z * (1212748362 + (1612391994 * z))))))))) + (u * ((z * (16213 + (z * (833360 + (z * (38602332 + (z * (407824875 + (554354928 * z))))))))) + (u * ((z * (3972 + (z * (114600 + (z * (6820764 + (z * (88601733 + (123692832 * z))))))))) + (u * ((z * (526 + (z * (9356 + (z * (765060 + (z * (12982155 + (18718128 * z))))))))) + (u * ((z * (36 + (z * (420 + (z * (53220 + (z * (1297369 + (1945556 * z))))))))) + (u * ((z * (1 + (z * (8 + (z * (2100 + (z * (87129 + (137136 * z))))))))) + (u * ((u * (((z ^ 4) * (93 + (168 * z))) + (u * (z ^ 4) * (1 + (2 * z))))) + ((z ^ 3) * (36 + (z * (3751 + (6272 * z))))))))))))))))))))) + ((z ^ 2) * (8573040 + (z * (231472080 + (z * (1620304560 + (2083248720 * z))))))))

lemma g2_sign (p : Params) (hp : p.Standing) (T : ℕ) (hT : p.N+7<T) :
    0 ≤ 6*p.a1 T*(p.kappaE T)^2+3*p.a2 T*p.kappaE T+a31 p T := by
  have hn : (2:ℝ) ≤ p.N := by exact_mod_cast hp.1
  have ht : (p.N:ℝ)+7 < T := by exact_mod_cast hT
  have hg : 0 < p.gamma := hp.2.1
  have hv : 0 < p.sigmaG2 := hp.2.2.1
  have hz : 0 ≤ p.psi2 := hp.2.2.2.1
  obtain ⟨b,hbdef⟩ : ∃b:ℝ,b=(p.N:ℝ)-2 := ⟨_,rfl⟩
  obtain ⟨u,hudef⟩ : ∃u:ℝ,u=(T:ℝ)-p.N-7 := ⟨_,rfl⟩
  have hb : 0 ≤ b := by rw [hbdef];linarith
  have hu : 0 < u := by rw [hudef];linarith
  have ht0 : (0:ℝ)<T := by linarith
  have ht2 : (0:ℝ)<(T:ℝ)-2 := by linarith
  have hn0 : (0:ℝ)<(T:ℝ)-p.N := by linarith
  have hn1 : (0:ℝ)<(T:ℝ)-p.N-1 := by linarith
  have hn2 : (0:ℝ)<(T:ℝ)-p.N-2 := by linarith
  have hn3 : (0:ℝ)<(T:ℝ)-p.N-3 := by linarith
  have hn5 : (0:ℝ)<(T:ℝ)-p.N-5 := by linarith
  have hn7 : (0:ℝ)<(T:ℝ)-p.N-7 := by linarith
  have hpsi : 0 < p.psi2+((p.N:ℝ)-1)/T := by
    apply add_pos_of_nonneg_of_pos hz
    apply div_pos _ ht0
    linarith
  let z := p.psi2
  let g := p.gamma
  let v := p.sigmaG2
  have hz' : 0 ≤ z := hz
  have hg' : 0 < g := hg
  have hv' : 0 < v := hv
  have hsum : 0 < (p.N:ℝ)+(T:ℝ)*p.psi2-1 := by
    nlinarith [mul_nonneg ht0.le hz]
  have hpsi_id : p.psi2+((p.N:ℝ)-1)/T = ((p.N:ℝ)+(T:ℝ)*p.psi2-1)/T := by
    field_simp
    <;> ring
  have hek : p.kappaE T = ((T:ℝ)-p.N)*((T:ℝ)-p.N-3)*p.psi2 / (((T:ℝ)-2)*((p.N:ℝ)+(T:ℝ)*p.psi2-1)) := by
    dsimp [Params.kappaE]
    rw [hpsi_id]
    field_simp
    <;> ring
  have hid : 6*p.a1 T*(p.kappaE T)^2+3*p.a2 T*p.kappaE T+a31 p T = P_g2 b u z g / (u * (g ^ 2) * ((6 + u) ^ 2) * ((1 + b + (9 * z) + (z * b) + (z * u)) ^ 3) * (2 + u) * (4 + u) * (5 + u) * (7 + u) * (7 + b + u)) := by
    have hnr : (p.N:ℝ)=b+2 := by rw [hbdef];ring
    have htr : (T:ℝ)=b+u+9 := by rw [hbdef,hudef];ring
    rw [hek]
    dsimp [Params.a1,Params.a2,a31,C]
    rw [hnr,htr]
    dsimp [P_g2,z,g]
    have hshift : b+u+9-(b+2) = 7+u := by ring
    have hshift2 : b+u+9-2 = 7+b+u := by ring
    have hshiftpsi : b+2+(b+u+9)*p.psi2-1 = 1+b+9*p.psi2+p.psi2*b+p.psi2*u := by ring
    simp only [hshift, hshift2, hshiftpsi]
    have h1 : 7+u-1=6+u := by ring
    have h2 : 7+u-2=5+u := by ring
    have h3 : 7+u-3=4+u := by ring
    have h5 : 7+u-5=2+u := by ring
    have h7 : 7+u-7=u := by ring
    simp only [h1,h2,h3,h5,h7]
    field_simp (disch := positivity)
    <;> ring
  rw [hid]
  apply div_nonneg
  · dsimp [P_g2];positivity
  · positivity
end RiskEU.RobustShrink.GammaCertificates

namespace RiskEU.RobustShrink.GammaCertificates
lemma sigma_signs (p : Params) (hp : p.Standing) (T : ℕ) (hT : p.N+7<T) :
    0 ≤ p.a3 T-a31 p T ∧ 0 ≤ 2*(p.a3 T-a31 p T)*p.kappaE T+p.a4 T := by
  have hn : (2:ℝ) ≤ p.N := by exact_mod_cast hp.1
  have ht : (p.N:ℝ)+7 < T := by exact_mod_cast hT
  have hg : 0 < p.gamma := hp.2.1
  have hv : 0 < p.sigmaG2 := hp.2.2.1
  have hz : 0 ≤ p.psi2 := hp.2.2.2.1
  have ht0 : (0:ℝ)<T := by linarith
  have ht2 : (0:ℝ)<(T:ℝ)-2 := by linarith
  have hn0 : (0:ℝ)<(T:ℝ)-p.N := by linarith
  have hn1 : (0:ℝ)<(T:ℝ)-p.N-1 := by linarith
  have hn3 : (0:ℝ)<(T:ℝ)-p.N-3 := by linarith
  have hn5 : (0:ℝ)<(T:ℝ)-p.N-5 := by linarith
  have hsum : 0 < (p.N:ℝ)+(T:ℝ)*p.psi2-1 := by nlinarith [mul_nonneg ht0.le hz]
  have hpsi : 0 < p.psi2+((p.N:ℝ)-1)/T := by
    apply add_pos_of_nonneg_of_pos hz
    apply div_pos _ ht0
    linarith
  have hpsi_id : p.psi2+((p.N:ℝ)-1)/T = ((p.N:ℝ)+(T:ℝ)*p.psi2-1)/T := by
    field_simp
    <;> ring
  have hek : p.kappaE T = ((T:ℝ)-p.N)*((T:ℝ)-p.N-3)*p.psi2 / (((T:ℝ)-2)*((p.N:ℝ)+(T:ℝ)*p.psi2-1)) := by
    dsimp [Params.kappaE]
    rw [hpsi_id]
    field_simp
    <;> ring
  have hd : p.a3 T-a31 p T = p.sigmaG2 *
      ((T:ℝ)*((T:ℝ)-2)*((T:ℝ)+p.N-3)*((T:ℝ)*p.psi2+p.N-1)) /
      (((T:ℝ)-p.N)*((T:ℝ)-p.N-1)^2*((T:ℝ)-p.N-3)*((T:ℝ)-p.N-5)) := by
    dsimp [Params.a3,a31]
    ring
  constructor
  · rw [hd]
    have htn : (0:ℝ)<(T:ℝ)+p.N-3 := by linarith
    have hzs : (0:ℝ)<(T:ℝ)*p.psi2+p.N-1 := by linarith
    positivity
  · have hid : 2*(p.a3 T-a31 p T)*p.kappaE T+p.a4 T =
        2*(T:ℝ)*p.sigmaG2*p.psi2*((p.N:ℝ)+1) /
        (((T:ℝ)-p.N-5)*((T:ℝ)-p.N-3)*((T:ℝ)-p.N-1)) := by
      rw [hd,hek]
      dsimp [Params.a4]
      field_simp (disch := first | positivity | nlinarith)
      <;> ring
    rw [hid]
    positivity
end RiskEU.RobustShrink.GammaCertificates

namespace RiskEU.RobustShrink.GammaCertificates
lemma c1_sign (p : Params) (hp : p.Standing) (T : ℕ) (hT : p.N+7<T) :
    0 ≤ 4*p.a1 T*(p.kappaE T)^3+3*p.a2 T*(p.kappaE T)^2+2*p.a3 T*p.kappaE T+p.a4 T := by
  have h1 := mul_nonneg (mean_vertex_core p hp T hT).1.1 (g1_sign p hp T hT)
  have hs := (sigma_signs p hp T hT).2
  nlinarith only [h1,hs]
lemma c2_sign (p : Params) (hp : p.Standing) (T : ℕ) (hT : p.N+7<T) :
    0 ≤ 6*p.a1 T*(p.kappaE T)^2+3*p.a2 T*p.kappaE T+p.a3 T := by
  have h1 := g2_sign p hp T hT
  have hs := (sigma_signs p hp T hT).1
  linarith only [h1,hs]
end RiskEU.RobustShrink.GammaCertificates
namespace RiskEU.RobustShrink
lemma variance_strict_core (p : Params) (hp : p.Standing) (T : ℕ) (hT : p.N+7<T) :
    StrictMonoOn (p.oosuVar T) (Set.Ici (p.kappaE T)) := by
  have ha := Certificates.a1_sign p hp T hT
  have h1 := GammaCertificates.c1_sign p hp T hT
  have h2 := GammaCertificates.c2_sign p hp T hT
  have h3 := Certificates.c3_sign p hp T hT
  let E := p.kappaE T
  let c1 := 4*p.a1 T*E^3+3*p.a2 T*E^2+2*p.a3 T*E+p.a4 T
  let c2 := 6*p.a1 T*E^2+3*p.a2 T*E+p.a3 T
  let c3 := 4*p.a1 T*E+p.a2 T
  have hid (k : ℝ) : p.oosuVar T k = p.oosuVar T E + c1*(k-E)+c2*(k-E)^2+c3*(k-E)^3+p.a1 T*(k-E)^4 := by
    dsimp [Params.oosuVar,Params.Delta,c1,c2,c3]
    ring
  intro x hx y hy hxy
  have hx0 : 0 ≤ x-E := sub_nonneg.mpr hx
  have hy0 : 0 ≤ y-E := sub_nonneg.mpr hy
  have hlt : x-E < y-E := by linarith
  have hpow2 : (x-E)^2 ≤ (y-E)^2 := by gcongr
  have hpow3 : (x-E)^3 ≤ (y-E)^3 := by gcongr
  have hpow4 : (x-E)^4 < (y-E)^4 := by gcongr
  have hc1 : c1*(x-E) ≤ c1*(y-E) := mul_le_mul_of_nonneg_left hlt.le h1
  have hc2 : c2*(x-E)^2 ≤ c2*(y-E)^2 := mul_le_mul_of_nonneg_left hpow2 h2
  have hc3 : c3*(x-E)^3 ≤ c3*(y-E)^3 := mul_le_mul_of_nonneg_left hpow3 h3
  have hc4 : p.a1 T*(x-E)^4 < p.a1 T*(y-E)^4 := mul_lt_mul_of_pos_left hpow4 ha
  rw [hid x,hid y]
  linarith only [hc1,hc2,hc3,hc4]

lemma variance_mono_core (p : Params) (hp : p.Standing) (T : ℕ) (hT : p.N+7<T) :
    MonotoneOn (p.oosuVar T) (Set.Icc (p.kappaE T) 1) :=
  (variance_strict_core p hp T hT).monotoneOn.mono Set.Icc_subset_Ici_self
end RiskEU.RobustShrink

open RiskEU.RobustShrink


/-- Proposition 4, p. 20, for the closed-form moments (13)–(19) and (IA1)–(IA3). -/
theorem solution (p : Params) (hp : p.Standing) :
    (∀ T : ℕ, p.N + 7 < T →
      (∃ kappa ∈ Set.Icc (0 : ℝ) 1,
        IsMaxOn (p.meanRisk T) (Set.Icc (0 : ℝ) 1) kappa) ∧
      (∃ kappa ∈ Set.Icc (0 : ℝ) 1,
        IsMinOn (p.oosuVar T) (Set.Icc (0 : ℝ) 1) kappa)) ∧
    (0 < p.psi2 → ∀ kappaR : ℕ → ℝ,
      (∀ T : ℕ, p.N + 7 < T →
        kappaR T ∈ Set.Icc (0 : ℝ) 1 ∧
        IsMaxOn (p.meanRisk T) (Set.Icc (0 : ℝ) 1) (kappaR T)) →
      Filter.Tendsto kappaR Filter.atTop (nhds 1)) ∧
    (∀ T : ℕ, p.N + 7 < T → ∀ kappaV kappaR : ℝ,
      kappaV ∈ Set.Icc (0 : ℝ) 1 →
      IsMinOn (p.oosuVar T) (Set.Icc (0 : ℝ) 1) kappaV →
      kappaR ∈ Set.Icc (0 : ℝ) 1 →
      IsMaxOn (p.meanRisk T) (Set.Icc (0 : ℝ) 1) kappaR →
      kappaV ≤ kappaR ∧ kappaR ≤ p.kappaE T) := by
  refine ⟨?_, ?_, ?_⟩
  · intro T hT
    exact extrema_core p T
  · exact fun hpsi kappaR hk => robust_limit_core p hp hpsi kappaR hk
  · intro T hT V R hV hmin hR hmax
    exact ordering_of_strict_variance p hp T hT (variance_strict_core p hp T hT) V R hV hmin hR hmax



#print axioms solution
