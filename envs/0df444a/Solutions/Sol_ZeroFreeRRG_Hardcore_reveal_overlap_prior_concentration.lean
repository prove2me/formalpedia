-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.reveal_overlap_prior_concentration
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:45:05.42773+00:00
-- url     : https://prove2.me/submissions/97567b26-e143-45e9-8127-34a781ead5cb

import Definitions.Def_ZeroFreeRRG_Hardcore_RevealOverlap
import Theorems.Thm_ZeroFreeRRG_Hardcore_model_pi_positive_simplex
import Theorems.Thm_ZeroFreeRRG_Hardcore_reveal_prior_two_sided_bernstein
import Mathlib
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (hm : m.Valid)
    (t s η : ℝ) (ht : m.PosParam t) (hs : 0 < s) (hs1 : s ≤ 1)
    (hη : 0 < η) (hη1 : η ≤ 1) (n : ℕ) :
    (∑ U : Finset (Fin n), revealProb s U *
      ∑ y : ({v : Fin n // v ∈ U} → m.Spin), ∑ y' : ({v : Fin n // v ∈ U} → m.Spin),
        if revealedOverlapH m t s η U y y' then
          (∏ v : {v : Fin n // v ∈ U}, m.pi t (y v)) *
          (∏ v : {v : Fin n // v ∈ U}, m.pi t (y' v)) else 0)
      ≤ 2*(Fintype.card m.Spin : ℝ)^2*Real.exp (-(s*η^2/12)*n) := by
  classical
  letI : DecidableEq (m.Spin × m.Spin) := Classical.decEq _
  let ν : m.Spin × m.Spin → ℝ := fun ab => m.pi t ab.1 * m.pi t ab.2
  let z : (m.Spin × m.Spin) → (m.Spin × m.Spin) → ℝ :=
    fun ab x => (if x = ab then 1 else 0) - ν ab
  let a := s*η*n/2
  have hπ := model_pi_positive_simplex m hm t ht
  have hπsum : (∑ i, m.pi t i) = 1 := hπ.2.2
  have hν : ∀ x, 0 ≤ ν x := fun x => mul_nonneg (hπ.1 x.1).le (hπ.1 x.2).le
  have hνsum : (∑ x, ν x) = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [ν,← Finset.mul_sum,hπsum,mul_one]
  have hνle (ab : m.Spin × m.Spin) : ν ab ≤ 1 := by
    have ha := mem_Icc_of_mem_stdSimplex hπ.2 ab.1
    have hb := mem_Icc_of_mem_stdSimplex hπ.2 ab.2
    have hh := mul_le_mul_of_nonneg_right ha.2 hb.1
    dsimp [ν]
    nlinarith [hb.2]
  have hz (ab x : m.Spin × m.Spin) : |z ab x| ≤ 1 := by
    dsimp [z]
    have h0 := hν ab
    have h1 := hνle ab
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  have hcenter (ab : m.Spin × m.Spin) : (∑ x, ν x * z ab x) = 0 := by
    have hone : (∑ x, ν x * (if x=ab then (1:ℝ) else 0)) = ν ab := by simp
    simp only [z,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hone,hνsum,one_mul,sub_self]
  have hrepr (U : Finset (Fin n)) :
      (∑ y : ({v : Fin n // v ∈ U} → m.Spin), ∑ y' : ({v : Fin n // v ∈ U} → m.Spin),
        if revealedOverlapH m t s η U y y' then
          (∏ v : {v : Fin n // v ∈ U}, m.pi t (y v)) *
          (∏ v : {v : Fin n // v ∈ U}, m.pi t (y' v)) else 0) =
      ∑ w : ({v : Fin n // v ∈ U} → m.Spin × m.Spin),
        (∏ v, ν (w v)) * (if ∃ ab, a ≤ |∑ v, z ab (w v)| then 1 else 0) := by
    let e : (({v : Fin n // v ∈ U} → m.Spin) × ({v : Fin n // v ∈ U} → m.Spin)) ≃
        ({v : Fin n // v ∈ U} → m.Spin × m.Spin) :=
      ⟨fun yy v => (yy.1 v,yy.2 v), fun w => (fun v => (w v).1,fun v => (w v).2),
        by intro yy; cases yy; rfl, by intro w; funext v; exact Prod.eta _⟩
    rw [← Fintype.sum_prod_type' (fun (y y' : {v : Fin n // v ∈ U} → m.Spin) =>
      if revealedOverlapH m t s η U y y' then
        (∏ v, m.pi t (y v)) * (∏ v, m.pi t (y' v)) else 0)]
    apply Fintype.sum_equiv e
    intro yy
    have hevent : revealedOverlapH m t s η U yy.1 yy.2 ↔
        ∃ ab, a ≤ |∑ v, z ab (e yy v)| := by
      simp only [revealedOverlapH,a,z,ν,Prod.ext_iff]
      rfl
    simp only [hevent]
    rw [Finset.prod_mul_distrib]
    split_ifs <;> simp [ν,e]
  have hbound (ab : m.Spin × m.Spin) :=
    reveal_prior_two_sided_bernstein n s η ν (z ab) hs.le hs1 hη hη1 hν hνsum (hz ab) (hcenter ab)
  have hU (U : Finset (Fin n)) :
      (∑ w : ({v : Fin n // v ∈ U} → m.Spin × m.Spin),
        (∏ v, ν (w v)) * (if ∃ ab, a ≤ |∑ v, z ab (w v)| then 1 else 0)) ≤
      ∑ ab : m.Spin × m.Spin, ∑ w : ({v : Fin n // v ∈ U} → m.Spin × m.Spin),
        (∏ v, ν (w v)) * (if a ≤ |∑ v, z ab (w v)| then 1 else 0) := by
    calc
      _ ≤ ∑ w : ({v : Fin n // v ∈ U} → m.Spin × m.Spin),
          (∏ v, ν (w v)) * ∑ ab : m.Spin × m.Spin,
            (if a ≤ |∑ v, z ab (w v)| then 1 else 0) := by
        apply Finset.sum_le_sum
        intro w hw
        apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun v hv => hν (w v))
        by_cases hex : ∃ ab, a ≤ |∑ v, z ab (w v)|
        · obtain ⟨ab,hab⟩ := hex
          have hex' : ∃ ab : m.Spin × m.Spin, a ≤ |∑ v, z ab (w v)| := ⟨ab,hab⟩
          rw [if_pos hex']
          have hh := Finset.single_le_sum (s := (Finset.univ : Finset (m.Spin × m.Spin)))
            (fun x hx => show (0:ℝ) ≤ if a ≤ |∑ v, z x (w v)| then 1 else 0 by split_ifs <;> norm_num)
            (Finset.mem_univ ab)
          rw [if_pos hab] at hh
          exact hh
        · rw [if_neg hex]
          exact Finset.sum_nonneg (fun x hx => by split_ifs <;> norm_num)
      _ = _ := by simp only [Finset.mul_sum]; rw [Finset.sum_comm]
  have hprob (U : Finset (Fin n)) : 0 ≤ revealProb s U := by
    unfold revealProb
    exact mul_nonneg (pow_nonneg hs.le _) (pow_nonneg (sub_nonneg.mpr hs1) _)
  calc
    _ = ∑ U : Finset (Fin n), revealProb s U *
        (∑ w : ({v : Fin n // v ∈ U} → m.Spin × m.Spin),
          (∏ v, ν (w v)) * (if ∃ ab, a ≤ |∑ v, z ab (w v)| then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro U hU
      rw [hrepr]
    _ ≤ ∑ U : Finset (Fin n), revealProb s U *
        (∑ ab : m.Spin × m.Spin, ∑ w : ({v : Fin n // v ∈ U} → m.Spin × m.Spin),
          (∏ v, ν (w v)) * (if a ≤ |∑ v, z ab (w v)| then 1 else 0)) := by
      exact Finset.sum_le_sum (fun U hUmem => mul_le_mul_of_nonneg_left (hU U) (hprob U))
    _ = ∑ ab : m.Spin × m.Spin, ∑ U : Finset (Fin n), revealProb s U *
        (∑ w : ({v : Fin n // v ∈ U} → m.Spin × m.Spin),
          (∏ v, ν (w v)) * (if a ≤ |∑ v, z ab (w v)| then 1 else 0)) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ ∑ _ab : m.Spin × m.Spin, 2*Real.exp (-(s*η^2/12)*n) := by
      exact Finset.sum_le_sum (fun ab hab => hbound ab)
    _ = _ := by simp [Fintype.card_prod,pow_two]; ring
