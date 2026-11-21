-- Prove2me | solution 1 for WeightedCongestionBR.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T04:28:44.801322+00:00
-- url     : https://prove2.me/submissions/38959d59-4c2d-4e82-9475-a6ec2561b29f

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_privateCost
import Definitions.Def_CongestionApproxPNE_IsPolyGame
import Definitions.Def_WeightedCongestionBR_alphaC
import Definitions.Def_WeightedCongestionBR_pConst
import Definitions.Def_WeightedCongestionBR_cmax
import Definitions.Def_WeightedCongestionBR_cmin
import Definitions.Def_WeightedCongestionBR_gConst
import Definitions.Def_WeightedCongestionBR_bnd
import Definitions.Def_WeightedCongestionBR_Config
import Definitions.Def_WeightedCongestionBR_AlgStep
import Definitions.Def_WeightedCongestionBR_Reach
import Definitions.Def_WeightedCongestionBR_partialPot
import Definitions.Def_WeightedCongestionBR_cfgMovers
import Definitions.Def_WeightedCongestionBR_PhasePrefix
import Definitions.Def_WeightedCongestionBR_PhaseRun
set_option autoImplicit false
open scoped NNReal
open HarksKlimm.Consistency

namespace Aux9gc

noncomputable def gcost {n r : ℕ} (G : HarksKlimm.Consistency.Game n r) (R : Finset (Fin n))
    (s : G.Profile) : ℝ :=
  ∑ u ∈ R, privateCost G s u

end Aux9gc

namespace Aux9a

open WeightedCongestionBR Aux9gc

theorem pair_term (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (k j : ℕ) :
    y ^ k * x ^ j + y ^ j * x ^ k ≤ x ^ (k + j) + y ^ (k + j) := by
  have h1 : x ^ k ≤ y ^ k := pow_le_pow_left₀ hx hxy k
  have h2 : x ^ j ≤ y ^ j := pow_le_pow_left₀ hx hxy j
  rw [pow_add, pow_add]
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]

theorem trap (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (ν : ℕ) :
    2 * ∑ k ∈ Finset.range (ν + 1), y ^ k * x ^ (ν - k) ≤ ((ν : ℝ) + 1) * (x ^ ν + y ^ ν) := by
  have hrefl : ∑ k ∈ Finset.range (ν + 1), y ^ k * x ^ (ν - k)
      = ∑ k ∈ Finset.range (ν + 1), y ^ (ν - k) * x ^ k := by
    rw [← Finset.sum_range_reflect (fun k => y ^ k * x ^ (ν - k)) (ν + 1)]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk' : k < ν + 1 := Finset.mem_range.mp hk
    have e1 : ν + 1 - 1 - k = ν - k := by omega
    have e3 : ν - (ν - k) = k := by omega
    simp only [e1, e3]
  calc 2 * ∑ k ∈ Finset.range (ν + 1), y ^ k * x ^ (ν - k)
      = ∑ k ∈ Finset.range (ν + 1), y ^ k * x ^ (ν - k)
        + ∑ k ∈ Finset.range (ν + 1), y ^ (ν - k) * x ^ k := by rw [← hrefl]; ring
    _ = ∑ k ∈ Finset.range (ν + 1), (y ^ k * x ^ (ν - k) + y ^ (ν - k) * x ^ k) :=
        (Finset.sum_add_distrib).symm
    _ ≤ ∑ _k ∈ Finset.range (ν + 1), (x ^ ν + y ^ ν) := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        have hk' : k < ν + 1 := Finset.mem_range.mp hk
        have h := pair_term x y hx hxy k (ν - k)
        have e : k + (ν - k) = ν := by omega
        rw [e] at h
        exact h
    _ = ((ν : ℝ) + 1) * (x ^ ν + y ^ ν) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

theorem term_bounds (d ν : ℕ) (hν : ν ≤ d) (x w : ℝ) (hx : 0 ≤ x) (hw : 1 ≤ w) :
    w * (x + w) ^ ν ≤ ((x + w) ^ (ν + 1) + ((ν : ℝ) + 1) / 2 * (x + w) ^ ν)
        - (x ^ (ν + 1) + ((ν : ℝ) + 1) / 2 * x ^ ν) ∧
      ((x + w) ^ (ν + 1) + ((ν : ℝ) + 1) / 2 * (x + w) ^ ν)
        - (x ^ (ν + 1) + ((ν : ℝ) + 1) / 2 * x ^ ν) ≤ ((d : ℝ) + 1) * w * (x + w) ^ ν := by
  obtain ⟨y, hy⟩ : ∃ y, y = x + w := ⟨_, rfl⟩
  rw [← hy]
  have hxy : x ≤ y := by rw [hy]; linarith
  have hy0 : 0 ≤ y := le_trans hx hxy
  have hgeom := geom_sum₂_mul y x (ν + 1)
  simp only [Nat.add_sub_cancel] at hgeom
  obtain ⟨E, hE⟩ : ∃ E, E = ∑ i ∈ Finset.range (ν + 1), y ^ i * x ^ (ν - i) := ⟨_, rfl⟩
  rw [← hE] at hgeom
  have hyx : y - x = w := by rw [hy]; ring
  rw [hyx] at hgeom
  have hEge : y ^ ν ≤ E := by
    have h := Finset.single_le_sum (f := fun i => y ^ i * x ^ (ν - i)) (s := Finset.range (ν + 1))
      (fun i _ => mul_nonneg (pow_nonneg hy0 _) (pow_nonneg hx _)) (Finset.self_mem_range_succ ν)
    simp only [Nat.sub_self, pow_zero, mul_one] at h
    rw [hE]
    exact h
  have hEle : 2 * E ≤ ((ν : ℝ) + 1) * (x ^ ν + y ^ ν) := by rw [hE]; exact trap x y hx hxy ν
  have hxν : x ^ ν ≤ y ^ ν := pow_le_pow_left₀ hx hxy ν
  have hw0 : 0 ≤ w := by linarith
  have hc : (0 : ℝ) ≤ (ν : ℝ) + 1 := by positivity
  have hdν : (ν : ℝ) ≤ d := by exact_mod_cast hν
  have hyν : 0 ≤ y ^ ν := pow_nonneg hy0 ν
  constructor
  · have h1 : 0 ≤ w * (E - y ^ ν) := mul_nonneg hw0 (sub_nonneg.mpr hEge)
    have h2 : 0 ≤ ((ν : ℝ) + 1) * (y ^ ν - x ^ ν) := mul_nonneg hc (sub_nonneg.mpr hxν)
    nlinarith
  · have h1 : w * (2 * E) ≤ w * (((ν : ℝ) + 1) * (x ^ ν + y ^ ν)) :=
      mul_le_mul_of_nonneg_left hEle hw0
    have h2 : 0 ≤ (w - 1) * (((ν : ℝ) + 1) * (y ^ ν - x ^ ν)) :=
      mul_nonneg (by linarith) (mul_nonneg hc (sub_nonneg.mpr hxν))
    have h3 : 0 ≤ ((d : ℝ) - ν) * (w * y ^ ν) :=
      mul_nonneg (by linarith) (mul_nonneg hw0 hyν)
    nlinarith

theorem eval_split (P : Polynomial ℝ) (z : ℝ) :
    P.eval z = P.coeff 0 + ∑ ν ∈ Finset.Icc 1 P.natDegree, P.coeff ν * z ^ ν := by
  rw [Polynomial.eval_eq_sum_range, Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < P.natDegree + 1), Finset.Ico_add_one_right_eq_Icc]
  simp only [pow_zero, mul_one, zero_add]


theorem lemma4 (d : ℕ) (hd : 1 ≤ d) (P : Polynomial ℝ) (hP : P.natDegree ≤ d ∧ ∀ j, 0 ≤ P.coeff j) (x w : ℝ) (hx : 0 ≤ x)
    (hw : 1 ≤ w) :
    w * P.eval (x + w) ≤ phiPoly P (x + w) - phiPoly P x ∧
      phiPoly P (x + w) - phiPoly P x ≤ alphaC d * w * P.eval (x + w) := by
  obtain ⟨hdeg, hcoef⟩ := hP
  unfold phiPoly alphaC
  rw [eval_split]
  have hdiff : (∑ ν ∈ Finset.Icc 1 P.natDegree,
        P.coeff ν * ((x + w) ^ (ν + 1) + ((ν : ℝ) + 1) / 2 * (x + w) ^ ν))
      - (∑ ν ∈ Finset.Icc 1 P.natDegree,
        P.coeff ν * (x ^ (ν + 1) + ((ν : ℝ) + 1) / 2 * x ^ ν))
      = ∑ ν ∈ Finset.Icc 1 P.natDegree, P.coeff ν *
        (((x + w) ^ (ν + 1) + ((ν : ℝ) + 1) / 2 * (x + w) ^ ν)
          - (x ^ (ν + 1) + ((ν : ℝ) + 1) / 2 * x ^ ν)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun _ _ => ?_)
    ring
  have eL : w * (P.coeff 0 + ∑ ν ∈ Finset.Icc 1 P.natDegree, P.coeff ν * (x + w) ^ ν)
      = w * P.coeff 0 + ∑ ν ∈ Finset.Icc 1 P.natDegree, P.coeff ν * (w * (x + w) ^ ν) := by
    rw [mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun _ _ => ?_)
    ring
  have eU : ((d : ℝ) + 1) * w * (P.coeff 0 + ∑ ν ∈ Finset.Icc 1 P.natDegree, P.coeff ν * (x + w) ^ ν)
      = ((d : ℝ) + 1) * w * P.coeff 0 + ∑ ν ∈ Finset.Icc 1 P.natDegree,
          P.coeff ν * (((d : ℝ) + 1) * w * (x + w) ^ ν) := by
    rw [mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun _ _ => ?_)
    ring
  have hsumL : ∑ ν ∈ Finset.Icc 1 P.natDegree, P.coeff ν * (w * (x + w) ^ ν)
      ≤ ∑ ν ∈ Finset.Icc 1 P.natDegree, P.coeff ν *
        (((x + w) ^ (ν + 1) + ((ν : ℝ) + 1) / 2 * (x + w) ^ ν)
          - (x ^ (ν + 1) + ((ν : ℝ) + 1) / 2 * x ^ ν)) := by
    refine Finset.sum_le_sum (fun ν hν => ?_)
    have hνd : ν ≤ d := le_trans (Finset.mem_Icc.mp hν).2 hdeg
    exact mul_le_mul_of_nonneg_left (term_bounds d ν hνd x w hx hw).1 (hcoef ν)
  have hsumU : ∑ ν ∈ Finset.Icc 1 P.natDegree, P.coeff ν *
        (((x + w) ^ (ν + 1) + ((ν : ℝ) + 1) / 2 * (x + w) ^ ν)
          - (x ^ (ν + 1) + ((ν : ℝ) + 1) / 2 * x ^ ν))
      ≤ ∑ ν ∈ Finset.Icc 1 P.natDegree, P.coeff ν * (((d : ℝ) + 1) * w * (x + w) ^ ν) := by
    refine Finset.sum_le_sum (fun ν hν => ?_)
    have hνd : ν ≤ d := le_trans (Finset.mem_Icc.mp hν).2 hdeg
    exact mul_le_mul_of_nonneg_left (term_bounds d ν hνd x w hx hw).2 (hcoef ν)
  have ha0 : 0 ≤ P.coeff 0 := hcoef 0
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hw0 : 0 ≤ w := by linarith
  have hprod : 0 ≤ (d : ℝ) * w * P.coeff 0 := mul_nonneg (mul_nonneg hd0 hw0) ha0
  have hlin0 : P.coeff 0 * (x + w) - P.coeff 0 * x = w * P.coeff 0 := by ring
  have hlin1 : ((d : ℝ) + 1) * w * P.coeff 0 = (d : ℝ) * w * P.coeff 0 + w * P.coeff 0 := by ring
  constructor
  · rw [eL]
    linarith
  · rw [eU]
    linarith

/-- Facility-level bounds, allowing `w = 0`. -/
theorem fac (d : ℕ) (hd : 1 ≤ d) (P : Polynomial ℝ) (hP : P.natDegree ≤ d ∧ ∀ j, 0 ≤ P.coeff j) (x w : ℝ) (hx : 0 ≤ x)
    (hw : w = 0 ∨ 1 ≤ w) :
    w * P.eval (x + w) ≤ phiPoly P (x + w) - phiPoly P x ∧
      phiPoly P (x + w) - phiPoly P x ≤ alphaC d * w * P.eval (x + w) := by
  rcases hw with h0 | h1
  · subst h0
    simp
  · exact lemma4 d hd P hP x w hx h1

theorem costPoly_eq {n r : ℕ} (G : Game n r) (e : Fin r) (P : Polynomial ℝ)
    (hP : ∀ x : ℝ≥0, G.cost e x = P.eval (x : ℝ)) : costPoly G e = P := by
  have hex : ∃ P : Polynomial ℝ, ∀ x : ℝ≥0, G.cost e x = P.eval (x : ℝ) := ⟨P, hP⟩
  unfold costPoly
  rw [dif_pos hex]
  have hQ := Classical.choose_spec hex
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ici_infinite (0 : ℝ)).mono
  intro x hx
  have hx0 : (0 : ℝ) ≤ x := hx
  show Polynomial.eval x (Classical.choose hex) = Polynomial.eval x P
  have h1 := hQ ⟨x, hx0⟩
  have h2 := hP ⟨x, hx0⟩
  exact h1.symm.trans h2

theorem load_eq {n r : ℕ} (G : Game n r) (s : G.Profile) (e : Fin r) :
    ((load G s e : ℝ≥0) : ℝ) = groupLoad G s Finset.univ e := by
  unfold load groupLoad
  rw [NNReal.coe_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs <;> simp

theorem groupLoad_split {n r : ℕ} (G : Game n r) (s : G.Profile) (R : Finset (Fin n)) (e : Fin r) :
    groupLoad G s Finset.univ e = groupLoad G s Rᶜ e + groupLoad G s R e := by
  unfold groupLoad
  rw [← Finset.sum_add_sum_compl R]
  ring

theorem groupLoad_nonneg {n r : ℕ} (G : Game n r) (s : G.Profile) (R : Finset (Fin n)) (e : Fin r) :
    0 ≤ groupLoad G s R e := by
  unfold groupLoad
  refine Finset.sum_nonneg (fun u _ => ?_)
  split_ifs
  · exact NNReal.coe_nonneg _
  · exact le_rfl

theorem groupLoad_cases {n r : ℕ} (G : Game n r) (hw : ∀ u, 1 ≤ G.demand u) (s : G.Profile)
    (R : Finset (Fin n)) (e : Fin r) :
    groupLoad G s R e = 0 ∨ 1 ≤ groupLoad G s R e := by
  by_cases h : ∃ u ∈ R, e ∈ (s u).val
  · right
    obtain ⟨u, hu, he⟩ := h
    unfold groupLoad
    have hle := Finset.single_le_sum (f := fun u => if e ∈ (s u).val then (G.demand u : ℝ) else 0)
      (fun u _ => by
        show 0 ≤ (if e ∈ (s u).val then (G.demand u : ℝ) else 0)
        split_ifs
        · exact NNReal.coe_nonneg _
        · exact le_rfl) hu
    simp only [he, ↓reduceIte] at hle
    have h1 : (1 : ℝ) ≤ (G.demand u : ℝ) := by exact_mod_cast hw u
    linarith
  · left
    push_neg at h
    unfold groupLoad
    refine Finset.sum_eq_zero (fun u hu => ?_)
    rw [if_neg (h u hu)]

theorem groupCost_eq {n r : ℕ} (G : Game n r) (R : Finset (Fin n)) (s : G.Profile) :
    gcost G R s = ∑ e : Fin r, groupLoad G s R e * G.cost e (load G s e) := by
  unfold gcost privateCost groupLoad
  simp_rw [Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_mem_eq]

theorem mainL {n r : ℕ} (G : Game n r) (d : ℕ) (hd : 1 ≤ d)
    (hG : CongestionApproxPNE.IsPolyGame d G) (hw : ∀ u, 1 ≤ G.demand u)
    (R : Finset (Fin n)) (s : G.Profile) :
    gcost G R s ≤ partialPot G R s ∧ partialPot G R s ≤ alphaC d * gcost G R s := by
  have hPf : ∀ e : Fin r, ∃ P : Polynomial ℝ, (P.natDegree ≤ d ∧ ∀ j, 0 ≤ P.coeff j) ∧ costPoly G e = P ∧
      ∀ x : ℝ≥0, G.cost e x = P.eval (x : ℝ) := by
    intro e
    obtain ⟨P, hdeg, hcoef, hcost⟩ := hG e
    exact ⟨P, ⟨hdeg, hcoef⟩, costPoly_eq G e P hcost, hcost⟩
  choose P hPd hcP hcost using hPf
  have hC : gcost G R s = ∑ e : Fin r,
      groupLoad G s R e * (P e).eval (groupLoad G s Rᶜ e + groupLoad G s R e) := by
    rw [groupCost_eq]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [hcost e, load_eq, groupLoad_split G s R e]
  have hΦ : partialPot G R s = ∑ e : Fin r,
      (phiPoly (P e) (groupLoad G s Rᶜ e + groupLoad G s R e) - phiPoly (P e) (groupLoad G s Rᶜ e)) := by
    unfold partialPot subgamePot
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [hcP e, groupLoad_split G s R e]
  have hfac := fun e : Fin r => fac d hd (P e) (hPd e) (groupLoad G s Rᶜ e) (groupLoad G s R e)
    (groupLoad_nonneg G s Rᶜ e) (groupLoad_cases G hw s R e)
  rw [hC, hΦ]
  constructor
  · exact Finset.sum_le_sum (fun e _ => (hfac e).1)
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun e _ => ?_)
    have := (hfac e).2
    calc _ ≤ alphaC d * groupLoad G s R e * (P e).eval (groupLoad G s Rᶜ e + groupLoad G s R e) :=
          this
      _ = _ := by ring

end Aux9a


namespace Aux6

open WeightedCongestionBR

theorem pair_term (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (k j : ℕ) :
    y ^ k * x ^ j + y ^ j * x ^ k ≤ x ^ (k + j) + y ^ (k + j) := by
  have h1 : x ^ k ≤ y ^ k := pow_le_pow_left₀ hx hxy k
  have h2 : x ^ j ≤ y ^ j := pow_le_pow_left₀ hx hxy j
  rw [pow_add, pow_add]
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]

theorem trap (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (ν : ℕ) :
    2 * ∑ k ∈ Finset.range (ν + 1), y ^ k * x ^ (ν - k) ≤ ((ν : ℝ) + 1) * (x ^ ν + y ^ ν) := by
  have hrefl : ∑ k ∈ Finset.range (ν + 1), y ^ k * x ^ (ν - k)
      = ∑ k ∈ Finset.range (ν + 1), y ^ (ν - k) * x ^ k := by
    rw [← Finset.sum_range_reflect (fun k => y ^ k * x ^ (ν - k)) (ν + 1)]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk' : k < ν + 1 := Finset.mem_range.mp hk
    have e1 : ν + 1 - 1 - k = ν - k := by omega
    have e3 : ν - (ν - k) = k := by omega
    simp only [e1, e3]
  calc 2 * ∑ k ∈ Finset.range (ν + 1), y ^ k * x ^ (ν - k)
      = ∑ k ∈ Finset.range (ν + 1), y ^ k * x ^ (ν - k)
        + ∑ k ∈ Finset.range (ν + 1), y ^ (ν - k) * x ^ k := by rw [← hrefl]; ring
    _ = ∑ k ∈ Finset.range (ν + 1), (y ^ k * x ^ (ν - k) + y ^ (ν - k) * x ^ k) :=
        (Finset.sum_add_distrib).symm
    _ ≤ ∑ _k ∈ Finset.range (ν + 1), (x ^ ν + y ^ ν) := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        have hk' : k < ν + 1 := Finset.mem_range.mp hk
        have h := pair_term x y hx hxy k (ν - k)
        have e : k + (ν - k) = ν := by omega
        rw [e] at h
        exact h
    _ = ((ν : ℝ) + 1) * (x ^ ν + y ^ ν) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

theorem term_bounds (d ν : ℕ) (hν : ν ≤ d) (x w : ℝ) (hx : 0 ≤ x) (hw : 1 ≤ w) :
    w * (x + w) ^ ν ≤ ((x + w) ^ (ν + 1) + ((ν : ℝ) + 1) / 2 * (x + w) ^ ν)
        - (x ^ (ν + 1) + ((ν : ℝ) + 1) / 2 * x ^ ν) ∧
      ((x + w) ^ (ν + 1) + ((ν : ℝ) + 1) / 2 * (x + w) ^ ν)
        - (x ^ (ν + 1) + ((ν : ℝ) + 1) / 2 * x ^ ν) ≤ ((d : ℝ) + 1) * w * (x + w) ^ ν := by
  obtain ⟨y, hy⟩ : ∃ y, y = x + w := ⟨_, rfl⟩
  rw [← hy]
  have hxy : x ≤ y := by rw [hy]; linarith
  have hy0 : 0 ≤ y := le_trans hx hxy
  have hgeom := geom_sum₂_mul y x (ν + 1)
  simp only [Nat.add_sub_cancel] at hgeom
  obtain ⟨E, hE⟩ : ∃ E, E = ∑ i ∈ Finset.range (ν + 1), y ^ i * x ^ (ν - i) := ⟨_, rfl⟩
  rw [← hE] at hgeom
  have hyx : y - x = w := by rw [hy]; ring
  rw [hyx] at hgeom
  have hEge : y ^ ν ≤ E := by
    have h := Finset.single_le_sum (f := fun i => y ^ i * x ^ (ν - i)) (s := Finset.range (ν + 1))
      (fun i _ => mul_nonneg (pow_nonneg hy0 _) (pow_nonneg hx _)) (Finset.self_mem_range_succ ν)
    simp only [Nat.sub_self, pow_zero, mul_one] at h
    rw [hE]
    exact h
  have hEle : 2 * E ≤ ((ν : ℝ) + 1) * (x ^ ν + y ^ ν) := by rw [hE]; exact trap x y hx hxy ν
  have hxν : x ^ ν ≤ y ^ ν := pow_le_pow_left₀ hx hxy ν
  have hw0 : 0 ≤ w := by linarith
  have hc : (0 : ℝ) ≤ (ν : ℝ) + 1 := by positivity
  have hdν : (ν : ℝ) ≤ d := by exact_mod_cast hν
  have hyν : 0 ≤ y ^ ν := pow_nonneg hy0 ν
  constructor
  · have h1 : 0 ≤ w * (E - y ^ ν) := mul_nonneg hw0 (sub_nonneg.mpr hEge)
    have h2 : 0 ≤ ((ν : ℝ) + 1) * (y ^ ν - x ^ ν) := mul_nonneg hc (sub_nonneg.mpr hxν)
    nlinarith
  · have h1 : w * (2 * E) ≤ w * (((ν : ℝ) + 1) * (x ^ ν + y ^ ν)) :=
      mul_le_mul_of_nonneg_left hEle hw0
    have h2 : 0 ≤ (w - 1) * (((ν : ℝ) + 1) * (y ^ ν - x ^ ν)) :=
      mul_nonneg (by linarith) (mul_nonneg hc (sub_nonneg.mpr hxν))
    have h3 : 0 ≤ ((d : ℝ) - ν) * (w * y ^ ν) :=
      mul_nonneg (by linarith) (mul_nonneg hw0 hyν)
    nlinarith

theorem eval_split (P : Polynomial ℝ) (z : ℝ) :
    P.eval z = P.coeff 0 + ∑ ν ∈ Finset.Icc 1 P.natDegree, P.coeff ν * z ^ ν := by
  rw [Polynomial.eval_eq_sum_range, Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < P.natDegree + 1), Finset.Ico_add_one_right_eq_Icc]
  simp only [pow_zero, mul_one, zero_add]


theorem lemma4 (d : ℕ) (hd : 1 ≤ d) (P : Polynomial ℝ) (hP : P.natDegree ≤ d ∧ ∀ j, 0 ≤ P.coeff j) (x w : ℝ) (hx : 0 ≤ x)
    (hw : 1 ≤ w) :
    w * P.eval (x + w) ≤ phiPoly P (x + w) - phiPoly P x ∧
      phiPoly P (x + w) - phiPoly P x ≤ alphaC d * w * P.eval (x + w) := by
  obtain ⟨hdeg, hcoef⟩ := hP
  unfold phiPoly alphaC
  rw [eval_split]
  have hdiff : (∑ ν ∈ Finset.Icc 1 P.natDegree,
        P.coeff ν * ((x + w) ^ (ν + 1) + ((ν : ℝ) + 1) / 2 * (x + w) ^ ν))
      - (∑ ν ∈ Finset.Icc 1 P.natDegree,
        P.coeff ν * (x ^ (ν + 1) + ((ν : ℝ) + 1) / 2 * x ^ ν))
      = ∑ ν ∈ Finset.Icc 1 P.natDegree, P.coeff ν *
        (((x + w) ^ (ν + 1) + ((ν : ℝ) + 1) / 2 * (x + w) ^ ν)
          - (x ^ (ν + 1) + ((ν : ℝ) + 1) / 2 * x ^ ν)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun _ _ => ?_)
    ring
  have eL : w * (P.coeff 0 + ∑ ν ∈ Finset.Icc 1 P.natDegree, P.coeff ν * (x + w) ^ ν)
      = w * P.coeff 0 + ∑ ν ∈ Finset.Icc 1 P.natDegree, P.coeff ν * (w * (x + w) ^ ν) := by
    rw [mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun _ _ => ?_)
    ring
  have eU : ((d : ℝ) + 1) * w * (P.coeff 0 + ∑ ν ∈ Finset.Icc 1 P.natDegree, P.coeff ν * (x + w) ^ ν)
      = ((d : ℝ) + 1) * w * P.coeff 0 + ∑ ν ∈ Finset.Icc 1 P.natDegree,
          P.coeff ν * (((d : ℝ) + 1) * w * (x + w) ^ ν) := by
    rw [mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun _ _ => ?_)
    ring
  have hsumL : ∑ ν ∈ Finset.Icc 1 P.natDegree, P.coeff ν * (w * (x + w) ^ ν)
      ≤ ∑ ν ∈ Finset.Icc 1 P.natDegree, P.coeff ν *
        (((x + w) ^ (ν + 1) + ((ν : ℝ) + 1) / 2 * (x + w) ^ ν)
          - (x ^ (ν + 1) + ((ν : ℝ) + 1) / 2 * x ^ ν)) := by
    refine Finset.sum_le_sum (fun ν hν => ?_)
    have hνd : ν ≤ d := le_trans (Finset.mem_Icc.mp hν).2 hdeg
    exact mul_le_mul_of_nonneg_left (term_bounds d ν hνd x w hx hw).1 (hcoef ν)
  have hsumU : ∑ ν ∈ Finset.Icc 1 P.natDegree, P.coeff ν *
        (((x + w) ^ (ν + 1) + ((ν : ℝ) + 1) / 2 * (x + w) ^ ν)
          - (x ^ (ν + 1) + ((ν : ℝ) + 1) / 2 * x ^ ν))
      ≤ ∑ ν ∈ Finset.Icc 1 P.natDegree, P.coeff ν * (((d : ℝ) + 1) * w * (x + w) ^ ν) := by
    refine Finset.sum_le_sum (fun ν hν => ?_)
    have hνd : ν ≤ d := le_trans (Finset.mem_Icc.mp hν).2 hdeg
    exact mul_le_mul_of_nonneg_left (term_bounds d ν hνd x w hx hw).2 (hcoef ν)
  have ha0 : 0 ≤ P.coeff 0 := hcoef 0
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hw0 : 0 ≤ w := by linarith
  have hprod : 0 ≤ (d : ℝ) * w * P.coeff 0 := mul_nonneg (mul_nonneg hd0 hw0) ha0
  have hlin0 : P.coeff 0 * (x + w) - P.coeff 0 * x = w * P.coeff 0 := by ring
  have hlin1 : ((d : ℝ) + 1) * w * P.coeff 0 = (d : ℝ) * w * P.coeff 0 + w * P.coeff 0 := by ring
  constructor
  · rw [eL]
    linarith
  · rw [eU]
    linarith

theorem costPoly_eq {n r : ℕ} (G : Game n r) (e : Fin r) (P : Polynomial ℝ)
    (hP : ∀ x : ℝ≥0, G.cost e x = P.eval (x : ℝ)) : costPoly G e = P := by
  have hex : ∃ P : Polynomial ℝ, ∀ x : ℝ≥0, G.cost e x = P.eval (x : ℝ) := ⟨P, hP⟩
  unfold costPoly
  rw [dif_pos hex]
  have hQ := Classical.choose_spec hex
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ici_infinite (0 : ℝ)).mono
  intro x hx
  have hx0 : (0 : ℝ) ≤ x := hx
  show Polynomial.eval x (Classical.choose hex) = Polynomial.eval x P
  have h1 := hQ ⟨x, hx0⟩
  have h2 := hP ⟨x, hx0⟩
  exact h1.symm.trans h2

theorem load_eq {n r : ℕ} (G : Game n r) (s : G.Profile) (e : Fin r) :
    ((load G s e : ℝ≥0) : ℝ) = groupLoad G s Finset.univ e := by
  unfold load groupLoad
  rw [NNReal.coe_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs <;> simp

theorem groupLoad_nonneg {n r : ℕ} (G : Game n r) (s : G.Profile) (R : Finset (Fin n)) (e : Fin r) :
    0 ≤ groupLoad G s R e := by
  unfold groupLoad
  refine Finset.sum_nonneg (fun u _ => ?_)
  split_ifs
  · exact NNReal.coe_nonneg _
  · exact le_rfl

theorem fac6 (d : ℕ) (hd : 1 ≤ d) (P : Polynomial ℝ) (hP : P.natDegree ≤ d ∧ ∀ j, 0 ≤ P.coeff j)
    (ℓ w : ℝ) (hℓ : 0 ≤ ℓ) (hw : 1 ≤ w) (a b : Prop) [Decidable a] [Decidable b] :
    (if a then w * P.eval (ℓ + w) else 0) - alphaC d * (if b then w * P.eval (ℓ + w) else 0) ≤
      phiPoly P (ℓ + if a then w else 0) - phiPoly P (ℓ + if b then w else 0) := by
  have h := lemma4 d hd P hP ℓ w hℓ hw
  obtain ⟨h1, h2⟩ := h
  by_cases ha : a <;> by_cases hb : b <;>
    simp only [ha, hb, ↓reduceIte, add_zero, mul_zero, sub_zero, zero_sub, sub_self] <;>
    linarith

theorem mainL {n r : ℕ} (G : Game n r) (d : ℕ) (hd : 1 ≤ d)
    (hG : CongestionApproxPNE.IsPolyGame d G) (hw : ∀ u, 1 ≤ G.demand u)
    (u : Fin n) (R : Finset (Fin n)) (hu : u ∈ R) (s s' : G.Profile) (hss' : ∀ v, v ≠ u → s v = s' v) :
    privateCost G s u - alphaC d * privateCost G s' u ≤ partialPot G R s - partialPot G R s' := by
  have hPf : ∀ e : Fin r, ∃ P : Polynomial ℝ, (P.natDegree ≤ d ∧ ∀ j, 0 ≤ P.coeff j) ∧
      costPoly G e = P ∧ ∀ x : ℝ≥0, G.cost e x = P.eval (x : ℝ) := by
    intro e
    obtain ⟨P, hdeg, hcoef, hcost⟩ := hG e
    exact ⟨P, ⟨hdeg, hcoef⟩, costPoly_eq G e P hcost, hcost⟩
  choose P hPd hcP hcost using hPf
  have hw1 : (1 : ℝ) ≤ (G.demand u : ℝ) := by exact_mod_cast hw u
  have hsplit : ∀ (t : G.Profile) (e : Fin r), groupLoad G t Finset.univ e =
      groupLoad G t (Finset.univ.erase u) e + (if e ∈ (t u).val then (G.demand u : ℝ) else 0) := by
    intro t e
    unfold groupLoad
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u)]
    ring
  have hℓ : ∀ e : Fin r, groupLoad G s' (Finset.univ.erase u) e =
      groupLoad G s (Finset.univ.erase u) e := by
    intro e
    unfold groupLoad
    refine Finset.sum_congr rfl (fun v hv => ?_)
    rw [hss' v (Finset.ne_of_mem_erase hv)]
  have hRc : ∀ e : Fin r, groupLoad G s' Rᶜ e = groupLoad G s Rᶜ e := by
    intro e
    unfold groupLoad
    refine Finset.sum_congr rfl (fun v hv => ?_)
    have hvu : v ≠ u := by
      intro h
      rw [h] at hv
      exact (Finset.mem_compl.mp hv) hu
    rw [hss' v hvu]
  have hpc : ∀ t : G.Profile, privateCost G t u = ∑ e : Fin r,
      (if e ∈ (t u).val then
        (G.demand u : ℝ) * (P e).eval (groupLoad G t (Finset.univ.erase u) e + G.demand u) else 0) := by
    intro t
    unfold privateCost
    symm
    rw [Finset.sum_ite_mem_eq]
    refine Finset.sum_congr rfl (fun e he => ?_)
    rw [hcost e, load_eq, hsplit t e, if_pos he]
  have hpp : partialPot G R s - partialPot G R s' = ∑ e : Fin r,
      (phiPoly (P e) (groupLoad G s Finset.univ e) - phiPoly (P e) (groupLoad G s' Finset.univ e)) := by
    unfold partialPot subgamePot
    have hc : ∑ e : Fin r, phiPoly (costPoly G e) (groupLoad G s' Rᶜ e) =
        ∑ e : Fin r, phiPoly (costPoly G e) (groupLoad G s Rᶜ e) :=
      Finset.sum_congr rfl (fun e _ => by rw [hRc e])
    rw [hc, sub_sub_sub_cancel_right, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [hcP e]
  rw [hpc s, hpc s', hpp, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro e _
  rw [hsplit s e, hsplit s' e, hℓ e]
  exact fac6 d hd (P e) (hPd e) _ _ (groupLoad_nonneg G s _ e) hw1 _ _

end Aux6


namespace Aux14

/-- Key one-variable inequality: `a (a+x)^k ≤ (1+ε) a^(k+1) + (k(1+1/ε))^k x^(k+1)`. -/
theorem key (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) (a x : ℝ) (ha : 0 ≤ a) (hx : 0 ≤ x) :
    a * (a + x) ^ k ≤ (1 + ε) * a ^ (k + 1) + ((k : ℝ) * (1 + 1 / ε)) ^ k * x ^ (k + 1) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h1ε : (0 : ℝ) < 1 + ε := by linarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = ε / (k * (1 + ε)) := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs]; positivity
  have hs1 : s < 1 := by
    rw [hs, div_lt_one (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hk1 h1ε.le]
  have hkne : (k : ℝ) ≠ 0 := hk0.ne'
  have hu : (k : ℝ) * s = ε / (1 + ε) := by
    rw [hs, mul_div_assoc', mul_div_mul_left _ _ hkne]
  have hinv : 1 / s = (k : ℝ) * (1 + 1 / ε) := by
    rw [hs, one_div_div, mul_div_assoc, add_div, div_self hε.ne', add_comm (1 / ε)]
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = 1 - s := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by rw [hθ]; linarith
  have hsum : θ + s = 1 := by rw [hθ]; ring
  have hbern : 1 + (k : ℝ) * (-s) ≤ (1 + (-s)) ^ k :=
    one_add_mul_le_pow (by linarith) k
  have hbern' : 1 - ε / (1 + ε) ≤ θ ^ k := by
    have e1 : (1 : ℝ) + (k : ℝ) * (-s) = 1 - ε / (1 + ε) := by rw [← hu]; ring
    have e2 : (1 : ℝ) + (-s) = θ := by rw [hθ]; ring
    rw [e1, e2] at hbern
    exact hbern
  have hid : (1 + ε) * (1 - ε / (1 + ε)) = 1 := by
    rw [mul_sub, mul_one, mul_div_cancel₀ ε h1ε.ne']
    ring
  have hθk : 1 ≤ (1 + ε) * θ ^ k := by
    have := mul_le_mul_of_nonneg_left hbern' h1ε.le
    linarith
  have hconv := (convexOn_pow (𝕜 := ℝ) (k + 1)).2
    (Set.mem_Ici.mpr (div_nonneg ha hθ0.le)) (Set.mem_Ici.mpr (div_nonneg hx hs0.le))
    hθ0.le hs0.le hsum
  simp only [smul_eq_mul] at hconv
  have e3 : θ * (a / θ) + s * (x / s) = a + x := by
    rw [mul_div_cancel₀ a hθ0.ne', mul_div_cancel₀ x hs0.ne']
  rw [e3] at hconv
  have t1 : θ * (a / θ) ^ (k + 1) ≤ (1 + ε) * a ^ (k + 1) := by
    have e4 : θ * (a / θ) ^ (k + 1) = a ^ (k + 1) * (1 / θ ^ k) := by
      rw [div_pow, pow_succ θ k]
      field_simp
    have h5 : 1 / θ ^ k ≤ 1 + ε := by
      rw [div_le_iff₀ (pow_pos hθ0 k)]
      linarith
    rw [e4]
    have := mul_le_mul_of_nonneg_left h5 (pow_nonneg ha (k + 1))
    linarith
  have t2 : s * (x / s) ^ (k + 1) = (1 / s) ^ k * x ^ (k + 1) := by
    rw [div_pow, pow_succ s k, one_div_pow]
    field_simp
  rw [t2, hinv] at hconv
  have h6 : a * (a + x) ^ k ≤ (a + x) ^ (k + 1) := by
    rw [pow_succ]
    have := mul_le_mul_of_nonneg_left (show a ≤ a + x by linarith) (pow_nonneg (by linarith : (0:ℝ) ≤ a + x) k)
    linarith
  linarith

theorem constC (d k : ℕ) (hd : 1 ≤ d) (hkd : k ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ((k : ℝ) * (1 + 1 / ε)) ^ k ≤ (1 + 1 / ε) ^ d * (d : ℝ) ^ d := by
  have h1 : (1 : ℝ) ≤ 1 + 1 / ε := by
    have : 0 ≤ 1 / ε := by positivity
    linarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  rw [mul_pow, mul_comm]
  apply mul_le_mul
  · exact pow_le_pow_right₀ h1 hkd
  · calc (k : ℝ) ^ k ≤ (d : ℝ) ^ k :=
          pow_le_pow_left₀ (Nat.cast_nonneg k) (by exact_mod_cast hkd) k
      _ ≤ (d : ℝ) ^ d := pow_le_pow_right₀ hd1 hkd
  · positivity
  · positivity

/-- Monomial version of the inequality. -/
theorem mono (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hkd : k ≤ d) (ε : ℝ) (hε : 0 < ε)
    (x x' y y' z : ℝ) (hx : 0 ≤ x) (hx' : 0 ≤ x') (hy : 0 ≤ y) (hy' : 0 ≤ y') (hz : 0 ≤ z) :
    y * (z + x + y) ^ k ≤
      (1 + ε) * y * (z + x' + y) ^ k + (1 + 1 / ε) ^ d * (d : ℝ) ^ d * x * (z + x + y') ^ k := by
  have hC0 : 0 ≤ (1 + 1 / ε) ^ d * (d : ℝ) ^ d := by positivity
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · simp only [pow_zero, mul_one]
    have := mul_nonneg hε.le hy
    have := mul_nonneg hC0 hx
    linarith
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = (1 + 1 / ε) ^ d * (d : ℝ) ^ d := ⟨_, rfl⟩
  rw [← hC] at hC0 ⊢
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = ((k : ℝ) * (1 + 1 / ε)) ^ k := ⟨_, rfl⟩
  have hKC : K ≤ C := by rw [hK, hC]; exact constC d k hd hkd ε hε
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = z + y := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have hya : y ≤ a := by rw [ha]; linarith
  have hA : a ^ k ≤ (z + x' + y) ^ k := pow_le_pow_left₀ ha0 (by rw [ha]; linarith) k
  have hB : x ^ k ≤ (z + x + y') ^ k := pow_le_pow_left₀ hx (by linarith) k
  have e0 : z + x + y = a + x := by rw [ha]; ring
  rw [e0]
  have core : y * (a + x) ^ k ≤ (1 + ε) * y * a ^ k + C * x * x ^ k := by
    by_cases h : (a + x) ^ k ≤ (1 + ε) * a ^ k
    · have := mul_le_mul_of_nonneg_left h hy
      have := mul_nonneg (mul_nonneg hC0 hx) (pow_nonneg hx k)
      have e : (1 + ε) * y * a ^ k = y * ((1 + ε) * a ^ k) := by ring
      linarith
    · push_neg at h
      have e1 := mul_le_mul_of_nonneg_right hya (sub_nonneg.mpr h.le)
      have hkey := key k hk1 ε hε a x ha0 hx
      rw [← hK] at hkey
      have e2 : K * x ^ (k + 1) ≤ C * x * x ^ k := by
        calc K * x ^ (k + 1) ≤ C * x ^ (k + 1) :=
              mul_le_mul_of_nonneg_right hKC (pow_nonneg hx _)
          _ = C * x * x ^ k := by ring
      calc y * (a + x) ^ k
          = y * ((a + x) ^ k - (1 + ε) * a ^ k) + (1 + ε) * y * a ^ k := by ring
        _ ≤ a * ((a + x) ^ k - (1 + ε) * a ^ k) + (1 + ε) * y * a ^ k := by linarith
        _ = a * (a + x) ^ k - (1 + ε) * a ^ (k + 1) + (1 + ε) * y * a ^ k := by ring
        _ ≤ K * x ^ (k + 1) + (1 + ε) * y * a ^ k := by linarith
        _ ≤ (1 + ε) * y * a ^ k + C * x * x ^ k := by linarith
  have f1 : (1 + ε) * y * a ^ k ≤ (1 + ε) * y * (z + x' + y) ^ k :=
    mul_le_mul_of_nonneg_left hA (mul_nonneg (by linarith) hy)
  have f2 : C * x * x ^ k ≤ C * x * (z + x + y') ^ k :=
    mul_le_mul_of_nonneg_left hB (mul_nonneg hC0 hx)
  linarith

theorem mainL (d : ℕ) (hd : 1 ≤ d) (f : Polynomial ℝ) (hf : f.natDegree ≤ d ∧ ∀ j, 0 ≤ f.coeff j) (ε : ℝ) (hε : 0 < ε)
    (x x' y y' z : ℝ) (hx : 0 ≤ x) (hx' : 0 ≤ x') (hy : 0 ≤ y) (hy' : 0 ≤ y') (hz : 0 ≤ z) :
    y * f.eval (z + x + y) ≤
      (1 + ε) * y * f.eval (z + x' + y) + (1 + 1 / ε) ^ d * (d : ℝ) ^ d * x * f.eval (z + x + y') := by
  have hlt : f.natDegree < d + 1 := Nat.lt_succ_of_le hf.1
  simp only [Polynomial.eval_eq_sum_range' hlt]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k hk
  have hkd : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hm := mono d hd k hkd ε hε x x' y y' z hx hx' hy hy' hz
  have hc := hf.2 k
  have := mul_le_mul_of_nonneg_left hm hc
  calc y * (f.coeff k * (z + x + y) ^ k) = f.coeff k * (y * (z + x + y) ^ k) := by ring
    _ ≤ f.coeff k * ((1 + ε) * y * (z + x' + y) ^ k +
          (1 + 1 / ε) ^ d * (d : ℝ) ^ d * x * (z + x + y') ^ k) := this
    _ = (1 + ε) * y * (f.coeff k * (z + x' + y) ^ k) +
          (1 + 1 / ε) ^ d * (d : ℝ) ^ d * x * (f.coeff k * (z + x + y') ^ k) := by ring

end Aux14

namespace Aux10

open WeightedCongestionBR Aux9gc

theorem memf {α : Type} [Fintype α] (p : α → Prop) (inst : DecidablePred p) (a : α) :
    a ∈ @Finset.filter α p inst Finset.univ ↔ p a := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem eval_nonneg (P : Polynomial ℝ) (hP : ∀ j, 0 ≤ P.coeff j) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ P.eval x := by
  rw [Polynomial.eval_eq_sum_range]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hP i) (pow_nonneg hx i))

theorem eval_mono (P : Polynomial ℝ) (hP : ∀ j, 0 ≤ P.coeff j) (a b : ℝ) (ha : 0 ≤ a)
    (hab : a ≤ b) : P.eval a ≤ P.eval b := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  refine Finset.sum_le_sum (fun i _ => ?_)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hab i) (hP i)

theorem pc_nonneg {n r : ℕ} (G : Game n r) (d : ℕ) (hG : CongestionApproxPNE.IsPolyGame d G)
    (s : G.Profile) (u : Fin n) : 0 ≤ privateCost G s u := by
  unfold privateCost
  refine Finset.sum_nonneg (fun e _ => ?_)
  obtain ⟨P, _, hc, hcost⟩ := hG e
  rw [hcost]
  exact mul_nonneg (NNReal.coe_nonneg _) (eval_nonneg P hc _ (NNReal.coe_nonneg _))

theorem alpha_le_p (d : ℕ) (hd : 1 ≤ d) : alphaC d ≤ pConst d ∧ 0 < pConst d := by
  unfold alphaC pConst
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h4 : (1 : ℝ) ≤ (4 * (d : ℝ)) ^ (d + 1) := one_le_pow₀ (by linarith)
  have h5 : (d : ℝ) + 1 ≤ (2 * (d : ℝ) + 3) * ((d : ℝ) + 1) := by nlinarith
  have h7 : (0 : ℝ) ≤ (2 * (d : ℝ) + 3) * ((d : ℝ) + 1) := by positivity
  have h6 : (2 * (d : ℝ) + 3) * ((d : ℝ) + 1) ≤
      (2 * (d : ℝ) + 3) * ((d : ℝ) + 1) * (4 * (d : ℝ)) ^ (d + 1) :=
    le_mul_of_one_le_right h7 h4
  constructor
  · linarith
  · linarith

theorem step_moveI {n r : ℕ} (G : Game n r) (d m : ℕ) (sinit : G.Profile) (a b : Config G)
    (h : AlgStep G d m sinit a b) (hph : b.phase = a.phase) (h1 : 1 ≤ a.phase) :
    ∃ (v : Fin n) (t : G.Strategy v), b = ⟨a.phase, Function.update a.s v t, a.F⟩ ∧ v ∉ a.F ∧
      (HasRhoMove G (alphaC d + 1 / pConst d) a.s v ∨ HasRhoMove G (pConst d) a.s v) ∧
      IsBestResponse G a.s v t := by
  cases h with
  | move0 u t h0 _ _ _ => omega
  | end0 h0 _ => omega
  | moveI u t _ _ hu hcond hbr =>
    refine ⟨u, t, rfl, hu, ?_, hbr⟩
    rcases hcond with ⟨_, _, hh⟩ | ⟨_, hh⟩
    · exact Or.inl hh
    · exact Or.inr hh
  | endI _ _ _ =>
    have hh : a.phase + 1 = a.phase := hph
    omega

theorem pot_step {n r : ℕ} (G : Game n r) (d : ℕ) (hd : 1 ≤ d)
    (hG : CongestionApproxPNE.IsPolyGame d G) (hw : ∀ u, 1 ≤ G.demand u) (R : Finset (Fin n))
    (s : G.Profile) (v : Fin n) (t : G.Strategy v)
    (hR : s v ≠ Function.update s v t v → v ∈ R)
    (hmove : HasRhoMove G (alphaC d + 1 / pConst d) s v ∨ HasRhoMove G (pConst d) s v)
    (hbr : IsBestResponse G s v t) :
    partialPot G R (Function.update s v t) ≤ partialPot G R s := by
  by_cases hsame : s v = t
  · have e : partialPot G R (Function.update s v t) = partialPot G R s := by
      rw [← hsame, Function.update_eq_self]
    exact le_of_eq e
  · have hvR : v ∈ R := hR (fun h => hsame (h.trans (Function.update_self v t s)))
    have h6 := Aux6.mainL G d hd hG hw v R hvR s (Function.update s v t)
      (fun w hw => (Function.update_of_ne hw t s).symm)
    obtain ⟨hap, hp0⟩ := alpha_le_p d hd
    have hc0 : 0 ≤ privateCost G (Function.update s v t) v := pc_nonneg G d hG _ v
    have hge : alphaC d * privateCost G (Function.update s v t) v ≤ privateCost G s v := by
      rcases hmove with ⟨t', ht'⟩ | ⟨t', ht'⟩
      · have hb := hbr t'
        have hinv : 0 ≤ 1 / pConst d := div_nonneg zero_le_one hp0.le
        have hα0 : (0 : ℝ) ≤ alphaC d := by unfold alphaC; positivity
        have hρ0 : (0 : ℝ) ≤ alphaC d + 1 / pConst d := by linarith
        have h1 : alphaC d * privateCost G (Function.update s v t) v ≤
            (alphaC d + 1 / pConst d) * privateCost G (Function.update s v t) v :=
          mul_le_mul_of_nonneg_right (by linarith) hc0
        have h2 : (alphaC d + 1 / pConst d) * privateCost G (Function.update s v t) v ≤
            (alphaC d + 1 / pConst d) * privateCost G (Function.update s v t') v :=
          mul_le_mul_of_nonneg_left hb hρ0
        have h3 : (alphaC d + 1 / pConst d) * privateCost G (Function.update s v t') v <
            privateCost G s v := ht'
        linarith
      · have hb := hbr t'
        have h1 : alphaC d * privateCost G (Function.update s v t) v ≤
            pConst d * privateCost G (Function.update s v t) v :=
          mul_le_mul_of_nonneg_right hap hc0
        have h2 : pConst d * privateCost G (Function.update s v t) v ≤
            pConst d * privateCost G (Function.update s v t') v :=
          mul_le_mul_of_nonneg_left hb hp0.le
        have h3 : pConst d * privateCost G (Function.update s v t') v < privateCost G s v := ht'
        linarith
    linarith

theorem chain {n r : ℕ} (G : Game n r) (d m : ℕ) (sinit : G.Profile) (hd : 1 ≤ d)
    (hG : CongestionApproxPNE.IsPolyGame d G) (hw : ∀ u, 1 ≤ G.demand u) (R : Finset (Fin n)) :
    ∀ (L : List (Config G)) (a : Config G), List.IsChain (AlgStep G d m sinit) (a :: L) →
      (∀ c' ∈ a :: L, c'.phase = a.phase) → 1 ≤ a.phase →
      (∀ q ∈ (a :: L).zip L, ∀ v, q.1.s v ≠ q.2.s v → v ∈ R) →
      ∀ z : Config G, (a :: L).getLast? = some z →
        z.F = a.F ∧ (∀ v ∈ a.F, z.s v = a.s v) ∧ (∀ v, v ∉ R → z.s v = a.s v) ∧
        partialPot G R z.s ≤ partialPot G R a.s ∧
        (∀ q ∈ (a :: L).zip L, ∀ v ∈ a.F, q.1.s v = q.2.s v) := by
  intro L
  induction L with
  | nil =>
    intro a _ _ _ _ z hz
    rw [List.getLast?_singleton] at hz
    have hza : a = z := Option.some.inj hz
    subst hza
    refine ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, le_rfl, ?_⟩
    intro q hq
    exact absurd hq (by simp)
  | cons b L ih =>
    intro a hch hph h1 hR z hz
    rw [List.isChain_cons_cons] at hch
    obtain ⟨hab, hch'⟩ := hch
    have hbph : b.phase = a.phase := hph b (List.mem_cons_of_mem _ List.mem_cons_self)
    obtain ⟨v, t, hb, hvF, hmv, hbr⟩ := step_moveI G d m sinit a b hab hbph h1
    have hph' : ∀ c' ∈ b :: L, c'.phase = b.phase :=
      fun c' hc' => (hph c' (List.mem_cons_of_mem _ hc')).trans hbph.symm
    have h1' : 1 ≤ b.phase := by rw [hbph]; exact h1
    have hzip : (a :: b :: L).zip (b :: L) = (a, b) :: (b :: L).zip L := rfl
    have hR' : ∀ q ∈ (b :: L).zip L, ∀ w, q.1.s w ≠ q.2.s w → w ∈ R := by
      intro q hq
      exact hR q (by rw [hzip]; exact List.mem_cons_of_mem _ hq)
    have hRab : ∀ w, a.s w ≠ b.s w → w ∈ R := by
      intro w
      exact hR (a, b) (by rw [hzip]; exact List.mem_cons_self) w
    have hz' : (b :: L).getLast? = some z := by
      rw [List.getLast?_cons_cons] at hz
      exact hz
    obtain ⟨ihF, ihFs, ihR, ihP, ihZ⟩ := ih b hch' hph' h1' hR' z hz'
    have hbF : b.F = a.F := by
      have h := congrArg Config.F hb
      exact h
    have hbs : b.s = Function.update a.s v t := by
      have h := congrArg Config.s hb
      exact h
    have hfix : ∀ w ∈ a.F, b.s w = a.s w := by
      intro w hw
      have hwv : w ≠ v := fun h => hvF (h ▸ hw)
      rw [hbs]
      exact Function.update_of_ne hwv t a.s
    refine ⟨ihF.trans hbF, ?_, ?_, ?_, ?_⟩
    · intro w hw
      have hwb : w ∈ b.F := by rw [hbF]; exact hw
      rw [ihFs w hwb]
      exact hfix w hw
    · intro w hw
      rw [ihR w hw]
      by_contra hne
      exact hw (hRab w (fun h => hne h.symm))
    · have hstep : partialPot G R b.s ≤ partialPot G R a.s := by
        rw [hbs]
        refine pot_step G d hd hG hw R a.s v t ?_ hmv hbr
        intro hne
        apply hRab v
        rw [hbs]
        exact hne
      exact le_trans ihP hstep
    · intro q hq w hw
      rw [hzip] at hq
      rcases List.mem_cons.mp hq with hq0 | hq'
      · rw [hq0]
        exact (hfix w hw).symm
      · have hwb : w ∈ b.F := by rw [hbF]; exact hw
        exact ihZ q hq' w hwb

theorem gl_congr {n r : ℕ} (G : Game n r) (t1 t2 : G.Profile) (S : Finset (Fin n)) (e : Fin r)
    (h : ∀ w ∈ S, t1 w = t2 w) : groupLoad G t1 S e = groupLoad G t2 S e := by
  unfold groupLoad
  refine Finset.sum_congr rfl (fun w hw => ?_)
  rw [h w hw]

theorem split3 {n r : ℕ} (G : Game n r) (t0 : G.Profile) (R : Finset (Fin n)) (u : Fin n)
    (hu : u ∉ R) (e : Fin r) :
    groupLoad G t0 Finset.univ e = groupLoad G t0 (Rᶜ.erase u) e + groupLoad G t0 R e +
      (if e ∈ (t0 u).val then (G.demand u : ℝ) else 0) := by
  unfold groupLoad
  rw [← Finset.sum_add_sum_compl R, ← Finset.add_sum_erase Rᶜ _ (Finset.mem_compl.mpr hu)]
  ring

end Aux10

open WeightedCongestionBR Aux9gc Aux10 in
theorem solution {n r : ℕ} (G : Game n r) (d m : ℕ) (sinit : G.Profile) (hd : 1 ≤ d)
    (hG : CongestionApproxPNE.IsPolyGame d G) (hw : ∀ u, 1 ≤ G.demand u) (hm : 1 ≤ m)
    (hcmin : 0 < cmin G) (hratio : cmax G sinit / cmin G ≤ gConst n d m ^ m)
    (l : List (Config G)) (c cl : Config G) (hl : PhaseRun G d m sinit l) (hc : l.head? = some c)
    (hcl : l.getLast? = some cl) (u : Fin n) (hu : u ∈ c.F) (ε : ℝ) (hε : 0 < ε) :
    privateCost G cl.s u ≤
        (1 + ε) * privateCost G c.s u +
          (1 + 1 / ε) ^ d * (d : ℝ) ^ d * partialPot G (cfgMovers l) c.s ∧
      ∀ t : G.Strategy u,
        1 / (1 + ε) * privateCost G (Function.update c.s u t) u -
            (1 + 1 / ε) ^ d * (d : ℝ) ^ d / (1 + ε) * partialPot G (cfgMovers l) c.s ≤
          privateCost G (Function.update cl.s u t) u := by
  obtain ⟨hpre, _⟩ := hl
  obtain ⟨c0, rest, hlc, hstart, hch, hphase⟩ := hpre
  have hc0 : c0 = c := by
    rw [hlc] at hc
    exact Option.some.inj hc
  rw [← hc0] at hu ⊢
  have hph1 : 1 ≤ c0.phase := by
    rcases hstart with hinit | ⟨cp, _, _, hcp⟩
    · rw [hinit] at hu
      exact absurd hu (Finset.notMem_empty u)
    · omega
  obtain ⟨R, hRdef⟩ : ∃ R, R = cfgMovers l := ⟨_, rfl⟩
  rw [← hRdef]
  have hRmem : ∀ q ∈ (c0 :: rest).zip rest, ∀ v, q.1.s v ≠ q.2.s v → v ∈ R := by
    intro q hq v hv
    rw [hRdef]
    unfold cfgMovers
    refine (memf _ _ v).mpr ⟨q, ?_, hv⟩
    rw [hlc]
    exact hq
  have hcl' : (c0 :: rest).getLast? = some cl := by rw [← hlc]; exact hcl
  obtain ⟨_, hFs, hRs, hPot, hZ⟩ :=
    chain G d m sinit hd hG hw R rest c0 (by rw [hlc] at hch; exact hch)
      (by rw [hlc] at hphase; exact hphase) hph1 hRmem cl hcl'
  have huR : u ∉ R := by
    intro huR
    rw [hRdef] at huR
    unfold cfgMovers at huR
    obtain ⟨q, hq, hne⟩ := (memf _ _ u).mp huR
    rw [hlc] at hq
    exact hne (hZ q hq u hu)
  have hsu : cl.s u = c0.s u := hFs u hu
  choose P hdeg hcoef hcost using hG
  obtain ⟨w, hwdef⟩ : ∃ w : ℝ, w = (G.demand u : ℝ) := ⟨_, rfl⟩
  have hw0 : 0 ≤ w := by rw [hwdef]; exact NNReal.coe_nonneg _
  obtain ⟨ξ, hξ⟩ : ∃ ξ : ℝ, ξ = (1 + 1 / ε) ^ d * (d : ℝ) ^ d := ⟨_, rfl⟩
  have hξ0 : 0 ≤ ξ := by rw [hξ]; positivity
  rw [← hξ]
  -- the frozen load
  have hZeq : ∀ e, groupLoad G cl.s (Rᶜ.erase u) e = groupLoad G c0.s (Rᶜ.erase u) e := by
    intro e
    refine gl_congr G _ _ _ e (fun v hv => ?_)
    have hvR : v ∉ R := Finset.mem_compl.mp (Finset.mem_of_mem_erase hv)
    exact hRs v hvR
  have hupdZ : ∀ (t0 : G.Profile) (t : G.Strategy u) e,
      groupLoad G (Function.update t0 u t) (Rᶜ.erase u) e = groupLoad G t0 (Rᶜ.erase u) e := by
    intro t0 t e
    refine gl_congr G _ _ _ e (fun v hv => ?_)
    exact Function.update_of_ne (Finset.ne_of_mem_erase hv) t t0
  have hupdR : ∀ (t0 : G.Profile) (t : G.Strategy u) e,
      groupLoad G (Function.update t0 u t) R e = groupLoad G t0 R e := by
    intro t0 t e
    refine gl_congr G _ _ _ e (fun v hv => ?_)
    have hvu : v ≠ u := fun h => huR (h ▸ hv)
    exact Function.update_of_ne hvu t t0
  have hZnn : ∀ (t0 : G.Profile) (S : Finset (Fin n)) e, 0 ≤ groupLoad G t0 S e :=
    fun t0 S e => Aux9a.groupLoad_nonneg G t0 S e
  -- C_R(t0) restricted to a subset of facilities is bounded by the partial potential
  have hCR : ∀ (t0 : G.Profile) (S : Finset (Fin r)),
      ∑ e ∈ S, groupLoad G t0 R e * (P e).eval (groupLoad G t0 Finset.univ e) ≤
        partialPot G R t0 := by
    intro t0 S
    calc ∑ e ∈ S, groupLoad G t0 R e * (P e).eval (groupLoad G t0 Finset.univ e)
        ≤ ∑ e : Fin r, groupLoad G t0 R e * (P e).eval (groupLoad G t0 Finset.univ e) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun e _ _ => ?_)
          exact mul_nonneg (hZnn t0 R e) (eval_nonneg (P e) (hcoef e) _ (hZnn t0 _ e))
      _ = gcost G R t0 := by
          rw [Aux9a.groupCost_eq G R t0]
          refine Finset.sum_congr rfl (fun e _ => ?_)
          rw [hcost e, Aux9a.load_eq]
      _ ≤ partialPot G R t0 :=
          (Aux9a.mainL G d hd (fun e => ⟨P e, hdeg e, hcoef e, hcost e⟩) hw R t0).1
  constructor
  · -- (18)
    have hcl_eq : privateCost G cl.s u = ∑ e ∈ (c0.s u).val,
        w * (P e).eval (groupLoad G c0.s (Rᶜ.erase u) e + groupLoad G cl.s R e + w) := by
      unfold privateCost
      rw [hsu]
      refine Finset.sum_congr rfl (fun e he => ?_)
      have he' : e ∈ (cl.s u).val := by rw [hsu]; exact he
      rw [hcost e, Aux9a.load_eq, split3 G cl.s R u huR e, hZeq e, if_pos he', hwdef]
    have hc_eq : privateCost G c0.s u = ∑ e ∈ (c0.s u).val,
        w * (P e).eval (groupLoad G c0.s (Rᶜ.erase u) e + groupLoad G c0.s R e + w) := by
      unfold privateCost
      refine Finset.sum_congr rfl (fun e he => ?_)
      rw [hcost e, Aux9a.load_eq, split3 G c0.s R u huR e, if_pos he, hwdef]
    have hY : ∑ e ∈ (c0.s u).val, groupLoad G cl.s R e *
        (P e).eval (groupLoad G c0.s (Rᶜ.erase u) e + groupLoad G cl.s R e + w) ≤
        partialPot G R c0.s := by
      have hrw : ∑ e ∈ (c0.s u).val, groupLoad G cl.s R e *
          (P e).eval (groupLoad G c0.s (Rᶜ.erase u) e + groupLoad G cl.s R e + w) =
          ∑ e ∈ (c0.s u).val, groupLoad G cl.s R e * (P e).eval (groupLoad G cl.s Finset.univ e) := by
        refine Finset.sum_congr rfl (fun e he => ?_)
        have he' : e ∈ (cl.s u).val := by rw [hsu]; exact he
        rw [split3 G cl.s R u huR e, hZeq e, if_pos he', hwdef]
      rw [hrw]
      exact le_trans (hCR cl.s _) hPot
    have hterm : ∀ e ∈ (c0.s u).val,
        w * (P e).eval (groupLoad G c0.s (Rᶜ.erase u) e + groupLoad G cl.s R e + w) ≤
          (1 + ε) * w * (P e).eval (groupLoad G c0.s (Rᶜ.erase u) e + groupLoad G c0.s R e + w) +
          ξ * groupLoad G cl.s R e *
            (P e).eval (groupLoad G c0.s (Rᶜ.erase u) e + groupLoad G cl.s R e + w) := by
      intro e _
      have h14 := Aux14.mainL d hd (P e) ⟨hdeg e, hcoef e⟩ ε hε (groupLoad G cl.s R e)
        (groupLoad G c0.s R e) w w (groupLoad G c0.s (Rᶜ.erase u) e) (hZnn _ _ e) (hZnn _ _ e)
        hw0 hw0 (hZnn _ _ e)
      rw [← hξ] at h14
      exact h14
    have hsum := Finset.sum_le_sum hterm
    have hsplit : ∑ e ∈ (c0.s u).val,
        ((1 + ε) * w * (P e).eval (groupLoad G c0.s (Rᶜ.erase u) e + groupLoad G c0.s R e + w) +
          ξ * groupLoad G cl.s R e *
            (P e).eval (groupLoad G c0.s (Rᶜ.erase u) e + groupLoad G cl.s R e + w)) =
        (1 + ε) * ∑ e ∈ (c0.s u).val,
            w * (P e).eval (groupLoad G c0.s (Rᶜ.erase u) e + groupLoad G c0.s R e + w) +
          ξ * ∑ e ∈ (c0.s u).val, groupLoad G cl.s R e *
            (P e).eval (groupLoad G c0.s (Rᶜ.erase u) e + groupLoad G cl.s R e + w) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl (fun e _ => by ring)
      · exact Finset.sum_congr rfl (fun e _ => by ring)
    rw [hsplit, ← hc_eq, ← hcl_eq] at hsum
    have hξY := mul_le_mul_of_nonneg_left hY hξ0
    linarith
  · -- (19)
    intro t
    have hct_eq : privateCost G (Function.update c0.s u t) u = ∑ e ∈ t.val,
        w * (P e).eval (groupLoad G c0.s (Rᶜ.erase u) e + groupLoad G c0.s R e + w) := by
      unfold privateCost
      rw [Function.update_self]
      refine Finset.sum_congr rfl (fun e he => ?_)
      rw [hcost e, Aux9a.load_eq, split3 G (Function.update c0.s u t) R u huR e, hupdZ c0.s t e,
        hupdR c0.s t e, Function.update_self, if_pos he, hwdef]
    have hclt_eq : privateCost G (Function.update cl.s u t) u = ∑ e ∈ t.val,
        w * (P e).eval (groupLoad G c0.s (Rᶜ.erase u) e + groupLoad G cl.s R e + w) := by
      unfold privateCost
      rw [Function.update_self]
      refine Finset.sum_congr rfl (fun e he => ?_)
      rw [hcost e, Aux9a.load_eq, split3 G (Function.update cl.s u t) R u huR e, hupdZ cl.s t e,
        hupdR cl.s t e, hZeq e, Function.update_self, if_pos he, hwdef]
    have hX : ∑ e ∈ t.val, groupLoad G c0.s R e *
        (P e).eval (groupLoad G c0.s (Rᶜ.erase u) e + groupLoad G c0.s R e + 0) ≤
        partialPot G R c0.s := by
      refine le_trans (Finset.sum_le_sum (fun e _ => ?_)) (hCR c0.s t.val)
      refine mul_le_mul_of_nonneg_left ?_ (hZnn _ _ e)
      refine eval_mono (P e) (hcoef e) _ _ (by linarith [hZnn c0.s (Rᶜ.erase u) e, hZnn c0.s R e]) ?_
      rw [split3 G c0.s R u huR e]
      have hite : (0 : ℝ) ≤ (if e ∈ (c0.s u).val then (G.demand u : ℝ) else 0) := by
        split_ifs
        · exact NNReal.coe_nonneg _
        · exact le_rfl
      linarith
    have hterm : ∀ e ∈ t.val,
        w * (P e).eval (groupLoad G c0.s (Rᶜ.erase u) e + groupLoad G c0.s R e + w) ≤
          (1 + ε) * w * (P e).eval (groupLoad G c0.s (Rᶜ.erase u) e + groupLoad G cl.s R e + w) +
          ξ * groupLoad G c0.s R e *
            (P e).eval (groupLoad G c0.s (Rᶜ.erase u) e + groupLoad G c0.s R e + 0) := by
      intro e _
      have h14 := Aux14.mainL d hd (P e) ⟨hdeg e, hcoef e⟩ ε hε (groupLoad G c0.s R e)
        (groupLoad G cl.s R e) w 0 (groupLoad G c0.s (Rᶜ.erase u) e) (hZnn _ _ e) (hZnn _ _ e)
        hw0 le_rfl (hZnn _ _ e)
      rw [← hξ] at h14
      exact h14
    have hsum := Finset.sum_le_sum hterm
    have hsplit : ∑ e ∈ t.val,
        ((1 + ε) * w * (P e).eval (groupLoad G c0.s (Rᶜ.erase u) e + groupLoad G cl.s R e + w) +
          ξ * groupLoad G c0.s R e *
            (P e).eval (groupLoad G c0.s (Rᶜ.erase u) e + groupLoad G c0.s R e + 0)) =
        (1 + ε) * ∑ e ∈ t.val,
            w * (P e).eval (groupLoad G c0.s (Rᶜ.erase u) e + groupLoad G cl.s R e + w) +
          ξ * ∑ e ∈ t.val, groupLoad G c0.s R e *
            (P e).eval (groupLoad G c0.s (Rᶜ.erase u) e + groupLoad G c0.s R e + 0) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl (fun e _ => by ring)
      · exact Finset.sum_congr rfl (fun e _ => by ring)
    rw [hsplit, ← hct_eq, ← hclt_eq] at hsum
    have hξX := mul_le_mul_of_nonneg_left hX hξ0
    have h1e : (0 : ℝ) < 1 + ε := by linarith
    have hkey : privateCost G (Function.update c0.s u t) u ≤
        (1 + ε) * privateCost G (Function.update cl.s u t) u + ξ * partialPot G R c0.s := by
      linarith
    have hfin : 1 / (1 + ε) * privateCost G (Function.update c0.s u t) u -
        ξ / (1 + ε) * partialPot G R c0.s =
        (privateCost G (Function.update c0.s u t) u - ξ * partialPot G R c0.s) / (1 + ε) := by
      ring
    rw [hfin, div_le_iff₀ h1e]
    linarith
