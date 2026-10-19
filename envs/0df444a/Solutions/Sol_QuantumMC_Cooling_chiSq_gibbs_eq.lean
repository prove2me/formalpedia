-- Prove2me | solution 1 for QuantumMC.Cooling.chiSq_gibbs_eq
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-17T08:25:04.439044+00:00
-- url     : https://prove2.me/submissions/1297c9f0-b1f1-42c6-82a8-eb2b294db6de

import Definitions.Def_QuantumMC_Cooling_Setting
set_option autoImplicit false
open scoped ENNReal InnerProductSpace
open QuantumMC.Cooling

namespace QueeliusCooling

theorem chi_identity {Ω : Type*} [Fintype Ω] (ν π : Ω → ℝ)
    (hν : ∑ x, ν x = 1) (hπ : ∑ x, π x = 1) (hπpos : ∀ x, 0 < π x) :
    chiSq ν π = ∑ x, ν x ^ 2 / π x - 1 := by
  have he (x : Ω) : π x*(ν x/π x-1)^2=ν x^2/π x-2*ν x+π x := by
    field_simp [(hπpos x).ne']
    <;> ring
  simp only [chiSq,he,Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,hν,hπ]
  ring

theorem overlap_inner {Ω : Type*} [Fintype Ω] (ν π : Ω → ℝ) :
    ⟪qsample ν,qsample π⟫_ℂ = ((∑ x, Real.sqrt (ν x)*Real.sqrt (π x) : ℝ) : ℂ) := by
  simp [qsample,PiLp.inner_apply,RCLike.inner_apply,←Complex.ofReal_mul,←Complex.ofReal_sum,mul_comm]

theorem overlap_moment {Ω : Type*} [Fintype Ω] (ν π : Ω → ℝ)
    (hν0 : ∀ x, 0 ≤ ν x) (hν : ∑ x, ν x=1) (hπpos : ∀ x, 0 < π x) :
    1 ≤ (∑ x, Real.sqrt (ν x)*Real.sqrt (π x))^2*(∑ x, ν x^2/π x) := by
  let a := fun x => Real.sqrt (ν x)*Real.sqrt (π x)
  let b := fun x => ν x*Real.sqrt (ν x)/Real.sqrt (π x)
  have ha (x : Ω) : 0 ≤ a x := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hb (x : Ω) : 0 ≤ b x := div_nonneg (mul_nonneg (hν0 x) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hab (x : Ω) : Real.sqrt (a x)*Real.sqrt (b x)=ν x := by
    have hap := ha x
    have hbp := hb x
    have hsπ := Real.sqrt_pos.mpr (hπpos x)
    have hmul : a x*b x=(ν x)^2 := by
      dsimp [a,b]
      field_simp [hsπ.ne']
      nlinarith only [Real.sq_sqrt (hν0 x)]
    have hs : (Real.sqrt (a x)*Real.sqrt (b x))^2=(ν x)^2 := by
      rw [mul_pow,Real.sq_sqrt hap,Real.sq_sqrt hbp,hmul]
    have hn := mul_nonneg (Real.sqrt_nonneg (a x)) (Real.sqrt_nonneg (b x))
    nlinarith only [hs,hn,hν0 x]
  have h1 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun x => Real.sqrt (a x)) (fun x => Real.sqrt (b x))
  simp only [hab,hν,Real.sq_sqrt (ha _),Real.sq_sqrt (hb _),one_pow] at h1
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun x => ν x/Real.sqrt (π x)) (fun x => Real.sqrt (ν x))
  have hid (x : Ω) : (ν x/Real.sqrt (π x))*Real.sqrt (ν x)=b x := by dsimp [b]; ring
  simp only [hid,div_pow,Real.sq_sqrt (hπpos _).le,Real.sq_sqrt (hν0 _),hν,mul_one] at h2
  have hq := mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 1) h1
  have hm := mul_le_mul_of_nonneg_left h2 (sq_nonneg (∑ x,a x))
  change 1 ≤ (∑ x,a x)^2*(∑ x,ν x^2/π x)
  nlinarith only [hq,hm]

theorem weighted_sqrt {Ω : Type*} (ν π : Ω → ℝ) (hν0 : ∀ x,0 ≤ ν x) (hπpos : ∀ x,0 < π x) (x : Ω) :
    ν x*Real.sqrt (π x/ν x)=Real.sqrt (ν x)*Real.sqrt (π x) := by
  by_cases hz : ν x=0
  · simp [hz]
  have hp : 0 < ν x := lt_of_le_of_ne (hν0 x) (Ne.symm hz)
  rw [Real.sqrt_div (hπpos x).le,div_eq_mul_inv]
  have hs := Real.sq_sqrt (hν0 x)
  have hsne := (Real.sqrt_pos.mpr hp).ne'
  field_simp [hsne]
  rw [hs]
  ring


theorem chi_overlap {Ω : Type*} [Fintype Ω] (ν π : Ω → ℝ)
    (hν0 : ∀ x, 0 ≤ ν x) (hν : ∑ x, ν x = 1) (hπpos : ∀ x, 0 < π x) (hπ : ∑ x, π x = 1) :
    1 / Real.sqrt (chiSq ν π + 1) ≤ ∑ x, ν x * Real.sqrt (π x / ν x) ∧
      ((∑ x, ν x * Real.sqrt (π x / ν x) : ℝ) : ℂ) = ⟪qsample ν, qsample π⟫_ℂ := by
  simp_rw [weighted_sqrt ν π hν0 hπpos]
  refine ⟨?_,(overlap_inner ν π).symm⟩
  let A := ∑ x,Real.sqrt (ν x)*Real.sqrt (π x)
  let Q := ∑ x,ν x^2/π x
  have hA : 0 ≤ A := Finset.sum_nonneg (fun x _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have h1 : 1 ≤ A^2*Q := overlap_moment ν π hν0 hν hπpos
  have hQ : 0 < Q := by
    by_contra hn
    have hh := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg A) (le_of_not_gt hn)
    linarith only [h1,hh]
  rw [chi_identity ν π hν hπ hπpos,sub_add_cancel]
  change 1/Real.sqrt Q ≤ A
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hQ)).2
  have he : (A*Real.sqrt Q)^2=A^2*Q := by rw [mul_pow,Real.sq_sqrt hQ.le]
  have hp := mul_nonneg hA (Real.sqrt_nonneg Q)
  nlinarith only [h1,he,hp]

theorem weight_nonneg (b : ℝ≥0∞) (h : ℕ) : 0 ≤ weight b h := by
  unfold weight
  split_ifs <;> positivity

theorem z_pos {Ω : Type*} [Fintype Ω] (H : Ω → ℕ) (hZ : ∃ x,H x=0) (b : ℝ≥0∞) : 0 < Z H b := by
  obtain ⟨x,hx⟩ := hZ
  apply Finset.sum_pos'
  · intro y _; exact weight_nonneg b (H y)
  · exact ⟨x,Finset.mem_univ _,by simp [weight,hx]⟩

theorem gibbs_sum {Ω : Type*} [Fintype Ω] (H : Ω → ℕ) (hZ : ∃ x,H x=0) (b : ℝ≥0∞) : ∑ x,gibbs H b x=1 := by
  simp only [gibbs,←Finset.sum_div]
  exact div_self (z_pos H hZ b).ne'

theorem weight_sq_div (b c : ℝ≥0∞) (hbc : b < c) (h : ℕ) :
    weight c h^2/weight b h=weight (2*c-b) h := by
  have hb : b ≠ ⊤ := ne_top_of_lt hbc
  by_cases hc : c=⊤
  · subst c
    by_cases hh : h=0
    · simp [weight,hh]
    · simp [weight,hh,hb]
  · have h2 : (2:ℝ≥0∞)*c ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hc
    have hdiff : 2*c-b ≠ ⊤ := ENNReal.sub_ne_top h2
    have hle : b ≤ 2*c := hbc.le.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (by norm_num : (1:ℝ≥0∞) ≤ 2) (by positivity : (0:ℝ≥0∞) ≤ c))
    simp only [weight,if_neg hb,if_neg hc,if_neg hdiff]
    rw [pow_two,←Real.exp_add,←Real.exp_sub,ENNReal.toReal_sub_of_le hle h2,ENNReal.toReal_mul]
    norm_num
    congr 1
    ring


theorem gibbs_pos {Ω : Type*} [Fintype Ω] (H : Ω → ℕ) (hZ : ∃ x,H x=0) (b : ℝ≥0∞) (hb : b ≠ ⊤) (x : Ω) :
    0 < gibbs H b x := by
  apply div_pos _ (z_pos H hZ b)
  simp only [weight,if_neg hb]
  exact Real.exp_pos _

theorem chi_gibbs {Ω : Type*} [Fintype Ω] (H : Ω → ℕ) (hZ : ∃ x,H x=0)
    (b c : ℝ≥0∞) (hbc : b < c) :
    chiSq (gibbs H c) (gibbs H b)=Z H b*Z H (2*c-b)/(Z H c)^2-1 := by
  have hb : b ≠ ⊤ := ne_top_of_lt hbc
  rw [chi_identity _ _ (gibbs_sum H hZ c) (gibbs_sum H hZ b) (gibbs_pos H hZ b hb)]
  congr 1
  have he (x : Ω) : (gibbs H c x)^2/gibbs H b x = Z H b/(Z H c)^2*weight (2*c-b) (H x) := by
    rw [←weight_sq_div b c hbc]
    dsimp [gibbs]
    field_simp [(z_pos H hZ b).ne',(z_pos H hZ c).ne']
    <;> ring
  simp only [he,←Finset.mul_sum]
  change Z H b/(Z H c)^2*Z H (2*c-b)=Z H b*Z H (2*c-b)/(Z H c)^2
  ring

end QueeliusCooling
#print axioms QueeliusCooling.chi_overlap
#print axioms QueeliusCooling.chi_gibbs

theorem solution {Ω : Type*} [Fintype Ω] (H : Ω → ℕ) (hZ : ∃ x, H x = 0)
    (β : ℕ → ℝ≥0∞) (ℓ : ℕ) (hβ : IsCoolingSchedule β ℓ) (i : ℕ) (hi : i < ℓ) :
    chiSq (gibbs H (β (i + 1))) (gibbs H (β i)) =
      Z H (β i) * Z H (2 * β (i + 1) - β i) / Z H (β (i + 1)) ^ 2 - 1 :=
  QueeliusCooling.chi_gibbs H hZ _ _ (hβ.2.1 i hi)
#print axioms solution
