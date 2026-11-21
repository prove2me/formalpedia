-- Prove2me | solution 1 for WeightedCongestionBR.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T03:30:11.87918+00:00
-- url     : https://prove2.me/submissions/56f6ffb0-3c2c-4d3f-9f67-0ddfb4f61689

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_privateCost
import Definitions.Def_CongestionApproxPNE_IsPolyGame
import Definitions.Def_WeightedCongestionBR_partialPot
import Definitions.Def_WeightedCongestionBR_alphaC
set_option autoImplicit false
open scoped NNReal
open HarksKlimm.Consistency

namespace Aux_WCBR_l6

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

end Aux_WCBR_l6

open WeightedCongestionBR Aux_WCBR_l6 in
theorem solution {n r : ℕ} (G : Game n r) (d : ℕ) (hd : 1 ≤ d)
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
