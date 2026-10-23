-- Prove2me | solution 1 for SensitivityPoA.NoUniform.theorem_8_b
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T20:35:39.867012+00:00
-- url     : https://prove2.me/submissions/71891c27-02f0-402f-baea-cdd7682ca87d

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_NoUniform_Setting

set_option autoImplicit false

namespace P851

open KellyStochasticNetworks SensitivityPoA.NoUniform

/-- Arc flows of any flow of a unit-demand game lie in `[0, 1]`. -/
lemma linkFlow_bounds (N : SensitivityPoA.NoUniform.Network) (hN : N.Standing)
    (d : Fin N.Sd → ℝ) (hd : ∑ σ, d σ = 1) (f : Fin N.R → ℝ)
    (hf : f ∈ wardropFeasible N.s d) (j : Fin N.J) :
    0 ≤ linkFlow N.A f j ∧ linkFlow N.A f j ≤ 1 := by
  have hA0 : ∀ r, 0 ≤ N.A j r := fun r => by
    rcases hN.1 j r with h | h <;> rw [h] <;> norm_num
  have hA1 : ∀ r, N.A j r ≤ 1 := fun r => by
    rcases hN.1 j r with h | h <;> rw [h] <;> norm_num
  have htot : ∑ r, f r = 1 := by
    rw [← Finset.sum_fiberwise Finset.univ N.s f, ← hd]
    refine Finset.sum_congr rfl fun σ _ => ?_
    exact hf.2 σ
  refine ⟨Finset.sum_nonneg fun r _ => mul_nonneg (hA0 r) (hf.1 r), ?_⟩
  unfold linkFlow
  calc ∑ r, N.A j r * f r ≤ ∑ r, f r :=
        Finset.sum_le_sum fun r _ => by
          have := hf.1 r
          nlinarith [hA1 r]
    _ = 1 := htot

/-- The distance bound: a unit-demand game with costs in `[0,1]` on `[0,1]` stays at bounded
distance from a fixed game of the game space. -/
lemma gameDist_le (N : SensitivityPoA.NoUniform.Network) (Γ Γ' : Game N)
    (hΓ : Γ ∈ gameSpace N) (hT : totalDemand Γ'.d = 1) (hd' : ∀ σ, |Γ'.d σ| ≤ 1)
    (hτ' : ∀ j x, 0 ≤ x → x ≤ 1 → 0 ≤ Γ'.τ j x ∧ Γ'.τ j x ≤ 1) :
    gameDist Γ Γ' ≤ ‖Γ.d‖ + ‖fun j => Γ.τ j (totalDemand Γ.d)‖ + 1 := by
  set K := ‖fun j => Γ.τ j (totalDemand Γ.d)‖ with hK
  have hK0 : 0 ≤ K := norm_nonneg _
  have hTpos : 0 < totalDemand Γ.d := hΓ.2.1
  have hτK : ∀ j x, 0 ≤ x → x ≤ totalDemand Γ.d → |Γ.τ j x| ≤ K := by
    intro j x hx hxT
    have hc := hΓ.1.1 j
    have h0 : 0 ≤ Γ.τ j x := hc.2.2 x hx
    have hmono : Γ.τ j x ≤ Γ.τ j (totalDemand Γ.d) :=
      hc.2.1 (Set.mem_Ici.2 hx) (Set.mem_Ici.2 hTpos.le) hxT
    have hnorm : ‖Γ.τ j (totalDemand Γ.d)‖ ≤ K :=
      norm_le_pi_norm (fun j => Γ.τ j (totalDemand Γ.d)) j
    rw [Real.norm_eq_abs] at hnorm
    rw [abs_of_nonneg h0]
    exact hmono.trans ((le_abs_self _).trans hnorm)
  have hd'n : ‖Γ'.d‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun σ => ?_
    rw [Real.norm_eq_abs]; exact hd' σ
  have h1 : ‖Γ.d - Γ'.d‖ ≤ ‖Γ.d‖ + K + 1 := by
    have := norm_sub_le Γ.d Γ'.d
    linarith
  have h2 : sSup ((fun p : Fin N.J × ℝ => |Γ.τ p.1 p.2 - Γ'.τ p.1 p.2|) ''
        (Set.univ ×ˢ Set.Icc 0 (min (totalDemand Γ.d) (totalDemand Γ'.d)))) ≤
      ‖Γ.d‖ + K + 1 := by
    refine Real.sSup_le ?_ (by positivity)
    rintro _ ⟨⟨j, x⟩, ⟨-, hx⟩, rfl⟩
    rw [hT] at hx
    obtain ⟨hx0, hx1⟩ := hx
    have hxT : x ≤ totalDemand Γ.d := hx1.trans (min_le_left _ _)
    have hx1' : x ≤ 1 := hx1.trans (min_le_right _ _)
    have ha := hτK j x hx0 hxT
    obtain ⟨hb0, hb1⟩ := hτ' j x hx0 hx1'
    have := abs_sub (Γ.τ j x) (Γ'.τ j x)
    rw [abs_of_nonneg hb0] at this
    have := norm_nonneg Γ.d
    simp only
    linarith
  have h3 : ‖fun j => Γ.τ j (totalDemand Γ.d) - Γ'.τ j (totalDemand Γ'.d)‖ ≤
      ‖Γ.d‖ + K + 1 := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
    rw [Real.norm_eq_abs, hT]
    have ha := hτK j (totalDemand Γ.d) hTpos.le le_rfl
    obtain ⟨hb0, hb1⟩ := hτ' j 1 zero_le_one le_rfl
    have := abs_sub (Γ.τ j (totalDemand Γ.d)) (Γ'.τ j 1)
    rw [abs_of_nonneg hb0] at this
    have := norm_nonneg Γ.d
    linarith
  unfold gameDist
  exact max_le h1 (max_le h2 h3)

/-- Pigou-type games on any standing antichain network have arbitrarily large price of anarchy,
with unit total demand and costs in `[0,1]` on `[0,1]`. -/
lemma exists_large_poa (N : SensitivityPoA.NoUniform.Network) (hN : N.Standing)
    (hAc : N.Antichain) (Q : ℝ) (hQ : 1 ≤ Q) :
    ∃ Γ' : Game N, Γ' ∈ gameSpace N ∧ totalDemand Γ'.d = 1 ∧ (∀ σ, |Γ'.d σ| ≤ 1) ∧
      (∀ j x, 0 ≤ x → x ≤ 1 → 0 ≤ Γ'.τ j x ∧ Γ'.τ j x ≤ 1) ∧ Q ≤ PoA Γ' := by
  classical
  -- two distinct routes of one O/D pair
  obtain ⟨hA01, hRarc, hSd, hJarc, hcard⟩ := hN
  set k : Fin N.Sd := ⟨0, hSd⟩
  obtain ⟨r1, hr1, r2, hr2, hne⟩ := Finset.one_lt_card.1 (hcard k)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr1 hr2
  have hs12 : N.s r1 = N.s r2 := hr1.trans hr2.symm
  -- an arc of r2 not on r1
  obtain ⟨b, hb2, hb1⟩ : ∃ b, N.A b r2 = 1 ∧ N.A b r1 ≠ 1 := by
    have := hAc r2 r1 hs12.symm (Ne.symm hne)
    push_neg at this
    exact this
  have hJpos : 0 < N.J := Fin.pos b
  set m : ℝ := (N.J : ℝ) with hm
  have hm1 : 1 ≤ m := by rw [hm]; exact_mod_cast hJpos
  have hm0 : 0 < m := by linarith
  set e : ℝ := 1 / (3 * m ^ 2 * Q) with he
  have hden : 0 < 3 * m ^ 2 * Q := by positivity
  have he0 : 0 < e := by rw [he]; positivity
  have hem : e ≤ 1 / m := by
    rw [he, div_le_div_iff₀ hden hm0]
    nlinarith
  have he1 : e ≤ 1 / 3 := by
    rw [he, div_le_div_iff₀ hden (by norm_num)]
    nlinarith
  have he1' : e < 1 := by linarith
  obtain ⟨p, hp⟩ : ∃ p : ℕ, (1 - e) ^ p < e :=
    exists_pow_lt_of_lt_one he0 (by linarith)
  -- the game
  let τ' : Fin N.J → ℝ → ℝ := fun j x =>
    if N.A j r2 = 1 then (if N.A j r1 = 1 then e else x ^ p / m) else 1
  let d' : Fin N.Sd → ℝ := fun σ => if σ = N.s r2 then 1 else 0
  let Γ' : Game N := ⟨τ', d'⟩
  have hT : totalDemand Γ'.d = 1 := by
    simp [Γ', d', totalDemand]
  have hτb : ∀ j x, 0 ≤ x → x ≤ 1 → e * x ^ p ≤ τ' j x ∧ τ' j x ≤ 1 := by
    intro j x hx0 hx1
    have hxp0 : 0 ≤ x ^ p := pow_nonneg hx0 p
    have hxp1 : x ^ p ≤ 1 := pow_le_one₀ hx0 hx1
    have hmi : 1 / m ≤ 1 := by rw [div_le_one hm0]; exact hm1
    simp only [τ']
    split_ifs
    · constructor <;> nlinarith
    · constructor
      · rw [mul_comm, div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_left hem hxp0
      · rw [div_le_one hm0]; linarith
    · constructor <;> nlinarith
  have hτnn : ∀ j x, 0 ≤ x → x ≤ 1 → 0 ≤ τ' j x := fun j x h0 h1 =>
    le_trans (mul_nonneg he0.le (pow_nonneg h0 p)) (hτb j x h0 h1).1
  have hmem : Γ' ∈ gameSpace N := by
    refine ⟨⟨fun j => ⟨?_, ?_, ?_⟩, fun σ => ?_⟩, ⟨by rw [hT]; norm_num, fun j x hx hxT => ?_⟩⟩
    · simp only [Γ', τ']
      split_ifs
      · exact continuousOn_const
      · exact ((continuous_pow p).div_const m).continuousOn
      · exact continuousOn_const
    · intro x hx y hy hxy
      simp only [Γ', τ']
      split_ifs
      · exact le_rfl
      · exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hx hxy p) hm0.le
      · exact le_rfl
    · intro x hx
      simp only [Γ', τ']
      split_ifs
      · exact he0.le
      · exact div_nonneg (pow_nonneg hx p) hm0.le
      · exact zero_le_one
    · simp only [Γ', d']; split_ifs <;> norm_num
    · simp only [Γ', τ']
      split_ifs
      · exact he0
      · exact div_pos (pow_pos hx p) hm0
      · exact zero_lt_one
  have hd'abs : ∀ σ, |Γ'.d σ| ≤ 1 := fun σ => by
    simp only [Γ', d']; split_ifs <;> norm_num
  have hdsum : ∑ σ, d' σ = 1 := by simp [d']
  have hA0 : ∀ j r, 0 ≤ N.A j r := fun j r => by
    rcases hA01 j r with h | h <;> rw [h] <;> norm_num
  -- cost bounds for arbitrary flows
  have hflow : ∀ f, IsFlow Γ' f → ∀ j, 0 ≤ linkFlow N.A f j ∧ linkFlow N.A f j ≤ 1 :=
    fun f hf j => linkFlow_bounds N ⟨hA01, hRarc, hSd, hJarc, hcard⟩ d' hdsum f hf j
  have hcost_le : ∀ f, IsFlow Γ' f → cost Γ' f ≤ m := by
    intro f hf
    unfold cost
    calc ∑ j, linkFlow N.A f j * Γ'.τ j (linkFlow N.A f j) ≤ ∑ _j : Fin N.J, (1 : ℝ) := by
          refine Finset.sum_le_sum fun j _ => ?_
          obtain ⟨h0, h1⟩ := hflow f hf j
          obtain ⟨-, h2⟩ := hτb j _ h0 h1
          have := hτnn j _ h0 h1
          simp only [Γ']
          nlinarith
      _ = m := by simp [hm]
  have hcost_nn : ∀ f, IsFlow Γ' f → 0 ≤ cost Γ' f := by
    intro f hf
    refine Finset.sum_nonneg fun j _ => ?_
    obtain ⟨h0, h1⟩ := hflow f hf j
    exact mul_nonneg h0 (hτnn j _ h0 h1)
  set L : ℝ := e * (1 / (N.R : ℝ)) ^ (p + 1) with hL
  have hRpos : 0 < (N.R : ℝ) := by exact_mod_cast Fin.pos r1
  have hL0 : 0 < L := by rw [hL]; positivity
  have hcost_ge : ∀ f, IsFlow Γ' f → L ≤ cost Γ' f := by
    intro f hf
    have htot : ∑ r, f r = 1 := by
      rw [← Finset.sum_fiberwise Finset.univ N.s f, ← hdsum]
      exact Finset.sum_congr rfl fun σ _ => hf.2 σ
    obtain ⟨r0, hr0⟩ : ∃ r0, 1 / (N.R : ℝ) ≤ f r0 := by
      by_contra hcon
      push_neg at hcon
      have : ∑ r, f r < ∑ _r : Fin N.R, 1 / (N.R : ℝ) :=
        Finset.sum_lt_sum_of_nonempty ⟨r1, Finset.mem_univ _⟩ fun r _ => hcon r
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one_div_cancel hRpos.ne'] at this
      linarith
    obtain ⟨j0, hj0⟩ := hRarc r0
    have hy : f r0 ≤ linkFlow N.A f j0 := by
      unfold linkFlow
      have := Finset.single_le_sum (f := fun r => N.A j0 r * f r)
        (fun r _ => mul_nonneg (hA0 j0 r) (hf.1 r)) (Finset.mem_univ r0)
      simp only [hj0, one_mul] at this
      exact this
    obtain ⟨h0, h1⟩ := hflow f hf j0
    have hterm : L ≤ linkFlow N.A f j0 * Γ'.τ j0 (linkFlow N.A f j0) := by
      have hb := (hτb j0 _ h0 h1).1
      have hR0 : 0 ≤ 1 / (N.R : ℝ) := by positivity
      have hpow : (1 / (N.R : ℝ)) ^ (p + 1) ≤ (linkFlow N.A f j0) ^ (p + 1) :=
        pow_le_pow_left₀ hR0 (hr0.trans hy) _
      simp only [Γ']
      rw [hL, pow_succ]
      calc e * ((1 / (N.R : ℝ)) ^ p * (1 / (N.R : ℝ)))
          ≤ e * (linkFlow N.A f j0 ^ p * linkFlow N.A f j0) := by
            rw [← pow_succ, ← pow_succ]
            exact mul_le_mul_of_nonneg_left hpow he0.le
        _ = linkFlow N.A f j0 * (e * linkFlow N.A f j0 ^ p) := by ring
        _ ≤ linkFlow N.A f j0 * τ' j0 (linkFlow N.A f j0) :=
            mul_le_mul_of_nonneg_left hb h0
    unfold cost
    refine hterm.trans ?_
    exact Finset.single_le_sum (f := fun j => linkFlow N.A f j * Γ'.τ j (linkFlow N.A f j))
      (fun j _ => mul_nonneg (hflow f hf j).1 (hτnn j _ (hflow f hf j).1 (hflow f hf j).2))
      (Finset.mem_univ j0)
  -- the Wardrop equilibrium: everything on r2
  let f0 : Fin N.R → ℝ := fun r => if r = r2 then 1 else 0
  have hf0flow : IsFlow Γ' f0 := by
    refine ⟨fun r => by simp only [f0]; split_ifs <;> norm_num, fun σ => ?_⟩
    simp only [f0, Γ', d']
    rw [Finset.sum_ite_eq']
    simp [eq_comm]
  have hy0 : ∀ j, linkFlow N.A f0 j = N.A j r2 := by
    intro j
    simp [linkFlow, f0]
  have hf0WE : IsWE Γ' f0 := by
    refine ⟨hf0flow, fun r r' hs hpos => ?_⟩
    have hr : r = r2 := by
      by_contra h
      simp [f0, h] at hpos
    subst hr
    simp only [hy0]
    by_cases hrr : r' = r
    · rw [hrr]
    -- route r has cost at most 1
    have hle1 : ∑ j, Γ'.τ j (N.A j r) * N.A j r ≤ 1 := by
      calc ∑ j, Γ'.τ j (N.A j r) * N.A j r ≤ ∑ _j : Fin N.J, 1 / m := by
            refine Finset.sum_le_sum fun j _ => ?_
            rcases hA01 j r with h | h
            · rw [h]; simp; positivity
            · rw [h, mul_one]
              simp only [Γ', τ', h, if_true, one_pow]
              split_ifs
              · exact hem
              · exact le_rfl
        _ = 1 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← hm,
              mul_one_div_cancel hm0.ne']
    obtain ⟨j1, hj1r', hj1r⟩ : ∃ j, N.A j r' = 1 ∧ N.A j r ≠ 1 := by
      have := hAc r' r hs hrr
      push_neg at this
      exact this
    have hge1 : 1 ≤ ∑ j, Γ'.τ j (N.A j r) * N.A j r' := by
      have hnn : ∀ j, 0 ≤ Γ'.τ j (N.A j r) * N.A j r' := by
        intro j
        refine mul_nonneg ?_ (hA0 j r')
        rcases hA01 j r with h | h <;> rw [h]
        · exact hτnn j 0 le_rfl zero_le_one
        · exact hτnn j 1 zero_le_one le_rfl
      have := Finset.single_le_sum (f := fun j => Γ'.τ j (N.A j r) * N.A j r')
        (fun j _ => hnn j) (Finset.mem_univ j1)
      refine le_trans ?_ this
      simp only [Γ', τ', hj1r, hj1r', if_false, mul_one, le_refl]
    linarith
  have hWEcost : 1 / m ≤ cost Γ' f0 := by
    unfold cost
    have hnn : ∀ j, 0 ≤ linkFlow N.A f0 j * Γ'.τ j (linkFlow N.A f0 j) := fun j =>
      mul_nonneg (hflow f0 hf0flow j).1
        (hτnn j _ (hflow f0 hf0flow j).1 (hflow f0 hf0flow j).2)
    have := Finset.single_le_sum (f := fun j => linkFlow N.A f0 j * Γ'.τ j (linkFlow N.A f0 j))
      (fun j _ => hnn j) (Finset.mem_univ b)
    refine le_trans ?_ this
    simp only [hy0, hb2, Γ', τ', hb1, if_true, if_false, one_pow, one_mul, le_refl]
  -- the cheap flow: 1 - e on r2, e on r1
  let g : Fin N.R → ℝ := fun r => (1 - e) * (if r = r2 then 1 else 0) + e * (if r = r1 then 1 else 0)
  have hgflow : IsFlow Γ' g := by
    refine ⟨fun r => ?_, fun σ => ?_⟩
    · simp only [g]
      have h1 : 0 ≤ 1 - e := by linarith
      split_ifs <;> nlinarith
    · simp only [g, Γ', d']
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_ite_eq',
        Finset.sum_ite_eq']
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hσ : N.s r2 = σ
      · rw [if_pos hσ, if_pos (hs12.trans hσ), if_pos hσ.symm]; ring
      · rw [if_neg hσ, if_neg (fun h => hσ (hs12.symm.trans h)), if_neg (Ne.symm hσ)]; ring
  have hyg : ∀ j, linkFlow N.A g j = (1 - e) * N.A j r2 + e * N.A j r1 := by
    intro j
    simp only [linkFlow, g, mul_add, Finset.sum_add_distrib]
    simp [mul_comm]
  have hgcost : cost Γ' g ≤ 3 * m * e := by
    unfold cost
    calc ∑ j, linkFlow N.A g j * Γ'.τ j (linkFlow N.A g j) ≤ ∑ _j : Fin N.J, 3 * e := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [hyg j]
          have hp0 : 0 ≤ (1 - e) ^ p := pow_nonneg (by linarith) p
          rcases hA01 j r2 with h2 | h2 <;> rcases hA01 j r1 with h1 | h1
          · rw [h2, h1, show (1 - e) * (0:ℝ) + e * 0 = 0 by ring, zero_mul]; linarith
          · rw [h2, h1, show (1 - e) * (0:ℝ) + e * 1 = e by ring]
            have hτj : Γ'.τ j e = 1 := by
              show τ' j e = 1
              simp only [τ']; rw [if_neg (by rw [h2]; norm_num)]
            rw [hτj]; linarith
          · rw [h2, h1, show (1 - e) * (1:ℝ) + e * 0 = 1 - e by ring]
            have hτj : Γ'.τ j (1 - e) = (1 - e) ^ p / m := by
              show τ' j (1 - e) = _
              simp only [τ']; rw [if_pos h2, if_neg (by rw [h1]; norm_num)]
            rw [hτj]
            have hq : (1 - e) * ((1 - e) ^ p / m) ≤ (1 - e) ^ p := by
              rw [mul_div_assoc', div_le_iff₀ hm0]
              nlinarith
            linarith
          · rw [h2, h1, show (1 - e) * (1:ℝ) + e * 1 = 1 by ring]
            have hτj : Γ'.τ j 1 = e := by
              show τ' j 1 = e
              simp only [τ']; rw [if_pos h2, if_pos h1]
            rw [hτj]; linarith
      _ = 3 * m * e := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← hm]; ring
  -- assemble the price of anarchy bound
  have hbdd : BddBelow (cost Γ' '' {f | IsFlow Γ' f}) :=
    ⟨0, by rintro _ ⟨f, hf, rfl⟩; exact hcost_nn f hf⟩
  have hSO_le : SOCost Γ' ≤ 3 * m * e :=
    (csInf_le hbdd ⟨g, hgflow, rfl⟩).trans hgcost
  have hSO_ge : L ≤ SOCost Γ' :=
    le_csInf ⟨_, ⟨g, hgflow, rfl⟩⟩ (by rintro _ ⟨f, hf, rfl⟩; exact hcost_ge f hf)
  have hWE_ge : 1 / m ≤ WECost Γ' := by
    refine hWEcost.trans (le_csSup ⟨m, ?_⟩ ⟨f0, hf0WE, rfl⟩)
    rintro _ ⟨f, hf, rfl⟩
    exact hcost_le f hf.1
  refine ⟨Γ', hmem, hT, hd'abs, fun j x h0 h1 => ⟨hτnn j x h0 h1, (hτb j x h0 h1).2⟩, ?_⟩
  have hSOpos : 0 < SOCost Γ' := lt_of_lt_of_le hL0 hSO_ge
  unfold PoA
  rw [le_div_iff₀ hSOpos]
  have hkey : Q * (3 * m * e) = 1 / m := by
    rw [he]; field_simp
  calc Q * SOCost Γ' ≤ Q * (3 * m * e) := mul_le_mul_of_nonneg_left hSO_le (by linarith)
    _ = 1 / m := hkey
    _ ≤ WECost Γ' := hWE_ge

end P851

open SensitivityPoA.NoUniform in
theorem solution (N : Network) (hN : N.Standing) (hA : N.Antichain)
    (Γ : Game N) (hΓ : Γ ∈ gameSpace N) (γ : ℝ) (hγ : 0 < γ) :
    ¬ ∃ κ : ℝ, 0 < κ ∧ ∀ Γ' ∈ gameSpace N, |PoA Γ - PoA Γ'| ≤ κ * gameDist Γ Γ' ^ γ := by
  rintro ⟨κ, hκ, hall⟩
  set D : ℝ := ‖Γ.d‖ + ‖fun j => Γ.τ j (totalDemand Γ.d)‖ + 1 with hD
  have hD0 : 0 ≤ D := by positivity
  have hQ : 1 ≤ |PoA Γ| + κ * D ^ γ + 1 := by
    have := Real.rpow_nonneg hD0 γ
    have := abs_nonneg (PoA Γ)
    nlinarith
  obtain ⟨Γ', hmem, hT, hd', hτ', hPoA⟩ := P851.exists_large_poa N hN hA _ hQ
  have hdist := P851.gameDist_le N Γ Γ' hΓ hT hd' hτ'
  have hdist0 : 0 ≤ gameDist Γ Γ' := (norm_nonneg _).trans (le_max_left _ _)
  have h1 := hall Γ' hmem
  have h2 : gameDist Γ Γ' ^ γ ≤ D ^ γ := Real.rpow_le_rpow hdist0 hdist hγ.le
  have h3 : PoA Γ' - PoA Γ ≤ |PoA Γ - PoA Γ'| := by
    rw [abs_sub_comm]; exact le_abs_self _
  have h4 := le_abs_self (PoA Γ)
  have h5 := mul_le_mul_of_nonneg_left h2 hκ.le
  linarith
