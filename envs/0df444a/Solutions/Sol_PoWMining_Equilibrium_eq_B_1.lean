-- Prove2me | solution 1 for PoWMining.Equilibrium.eq_B_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:12:14.60791+00:00
-- url     : https://prove2.me/submissions/bebc0904-5b99-451c-b734-af405f525116

import Mathlib
import Definitions.Def_PoWMining_Equilibrium_Setting
set_option autoImplicit false
open PoWMining.Equilibrium

lemma vv_aggH_update {N : ℕ} (h : Fin N → ℝ) (i : Fin N) (x : ℝ) :
    aggH (Function.update h i x) = aggH h - h i + x := by
  unfold aggH
  rw [Finset.sum_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]
  have := Finset.add_sum_erase Finset.univ h (Finset.mem_univ i)
  linarith

lemma vv_payoff_update {N : ℕ} (P : Params N) (h : Fin N → ℝ) (i : Fin N) (x : ℝ)
    (hx : aggH h - h i + x ≠ 0) :
    payoff P (Function.update h i x) i =
      x / (aggH h - h i + x) * P.R - P.c i * x - P.γ / 2 * x ^ 2 := by
  unfold payoff
  rw [vv_aggH_update, if_neg hx]
  simp

lemma vv_S_nonneg {N : ℕ} (h : Fin N → ℝ) (hnn : ∀ i, 0 ≤ h i) (i : Fin N) :
    0 ≤ aggH h - h i := by
  have := vv_aggH_update h i 0
  have h2 : 0 ≤ aggH (Function.update h i 0) := by
    unfold aggH
    apply Finset.sum_nonneg
    intro j _
    by_cases hj : j = i
    · subst hj; simp
    · rw [Function.update_of_ne hj]; exact hnn j
  linarith

lemma vv_pos {N : ℕ} (P : Params N) (hP : P.Standing) (h : Fin N → ℝ)
    (hh : IsMiningEq P h) : 0 < aggH h := by
  obtain ⟨hN2, hR, hγ, hc, hmono⟩ := hP
  obtain ⟨hnn, hdev⟩ := hh
  by_contra hcon
  have hcon' : aggH h ≤ 0 := not_lt.1 hcon
  have hH0 : aggH h = 0 := le_antisymm hcon' (Finset.sum_nonneg (fun j _ => hnn j))
  have hz : ∀ j, h j = 0 := by
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn j)).1 hH0
    intro j; exact this j (Finset.mem_univ j)
  let i0 : Fin N := ⟨0, by omega⟩
  have hci := hc i0
  have hD : 0 < P.c i0 + P.γ := by linarith
  set x := min 1 (P.R / (2 * (P.c i0 + P.γ))) with hx
  have hxpos : 0 < x := lt_min one_pos (by positivity)
  have hx1 : x ≤ 1 := min_le_left _ _
  have hx2 : x ≤ P.R / (2 * (P.c i0 + P.γ)) := min_le_right _ _
  have hx3 : x * (P.c i0 + P.γ) ≤ P.R / 2 := by
    rw [le_div_iff₀ (by positivity)] at hx2; linarith
  have h1 : payoff P (Function.update h i0 x) i0 ≤ payoff P h i0 := hdev i0 x hxpos.le
  have hne : aggH h - h i0 + x ≠ 0 := by rw [hH0, hz i0]; simp [hxpos.ne']
  have h2 := vv_payoff_update P h i0 x hne
  have h3 : payoff P h i0 = 0 := by unfold payoff; rw [if_pos hH0]
  have h4 : x / (aggH h - h i0 + x) = 1 := by
    rw [hH0, hz i0]; simp [hxpos.ne']
  rw [h2, h3, h4] at h1
  nlinarith [mul_pos hxpos hxpos, mul_nonneg hγ hxpos.le, mul_nonneg hγ (mul_nonneg hxpos.le (sub_nonneg.2 hx1))]

lemma vv_foc {N : ℕ} (P : Params N) (hP : P.Standing) (h : Fin N → ℝ)
    (hh : IsMiningEq P h) (i : Fin N) (hi : 0 < h i) :
    (aggH h - h i) * P.R / (aggH h) ^ 2 = P.c i + P.γ * h i := by
  have hH := vv_pos P hP h hh
  obtain ⟨hnn, hdev⟩ := hh
  have hS := vv_S_nonneg h hnn i
  set S := aggH h - h i with hSdef
  let g : ℝ → ℝ := fun x => x / (S + x) * P.R - P.c i * x - P.γ / 2 * x ^ 2
  have hg : ∀ x, 0 < x → payoff P (Function.update h i x) i = g x := by
    intro x hx
    have hpos : 0 < S + x := by linarith
    exact vv_payoff_update P h i x hpos.ne'
  have hgi : payoff P h i = g (h i) := by
    have hpos : 0 < S + h i := by linarith
    have := vv_payoff_update P h i (h i) hpos.ne'
    rw [Function.update_eq_self] at this
    exact this
  have hmax : IsLocalMax g (h i) := by
    filter_upwards [Ioi_mem_nhds hi] with x hx
    have h1 : payoff P (Function.update h i x) i ≤ payoff P h i := hdev i x (le_of_lt hx)
    rw [hg x hx, hgi] at h1
    exact h1
  have hSh : S + h i = aggH h := by rw [hSdef]; ring
  have hd : HasDerivAt g (S * P.R / (S + h i) ^ 2 - P.c i - P.γ * h i) (h i) := by
    have hne : S + h i ≠ 0 := by rw [hSh]; exact hH.ne'
    have d1 := ((hasDerivAt_id (h i)).div ((hasDerivAt_id (h i)).const_add S) hne).mul_const P.R
    have d2 := (hasDerivAt_id (h i)).const_mul (P.c i)
    have d3 := ((hasDerivAt_id (h i)).pow 2).const_mul (P.γ / 2)
    have d4 := (d1.sub d2).sub d3
    have hval : (1 * (S + id (h i)) - id (h i) * 1) / (S + id (h i)) ^ 2 * P.R - P.c i * 1 -
        P.γ / 2 * ((2:ℕ) * id (h i) ^ (2 - 1) * 1) = S * P.R / (S + h i) ^ 2 - P.c i - P.γ * h i := by
      simp only [id]
      push_cast
      field_simp
      ring
    have d5 : HasDerivAt g ((1 * (S + id (h i)) - id (h i) * 1) / (S + id (h i)) ^ 2 * P.R - P.c i * 1 -
        P.γ / 2 * ((2:ℕ) * id (h i) ^ (2 - 1) * 1)) (h i) := d4
    rw [hval] at d5
    exact d5
  have := hmax.hasDerivAt_eq_zero hd
  rw [hSh] at this
  linarith

lemma vv_inactive {N : ℕ} (P : Params N) (hP : P.Standing) (h : Fin N → ℝ)
    (hh : IsMiningEq P h) (j : Fin N) (hj : h j = 0) :
    P.R / aggH h ≤ P.c j := by
  have hH := vv_pos P hP h hh
  obtain ⟨hN2, hR, hγ, hc, hmono⟩ := hP
  obtain ⟨hnn, hdev⟩ := hh
  by_contra hcon
  have hcon' : P.c j < P.R / aggH h := not_le.1 hcon
  let φ : ℝ → ℝ := fun x => P.R / (aggH h + x) - P.c j - P.γ / 2 * x
  have hφ0 : 0 < φ 0 := by simp only [φ]; simp; linarith
  have hφc : ContinuousAt φ 0 := by
    apply ContinuousAt.sub (ContinuousAt.sub _ continuousAt_const)
    · exact continuousAt_const.mul continuousAt_id
    · exact ContinuousAt.div continuousAt_const (continuousAt_const.add continuousAt_id)
        (by simp; exact hH.ne')
  have hev : ∀ᶠ x in nhdsWithin (0:ℝ) (Set.Ioi 0), 0 < φ x :=
    (hφc.eventually (Ioi_mem_nhds hφ0)).filter_mono nhdsWithin_le_nhds
  obtain ⟨x, hx1, hx2⟩ := (hev.and self_mem_nhdsWithin).exists
  have hx2 : 0 < x := hx2
  have h1 : payoff P (Function.update h j x) j ≤ payoff P h j := hdev j x hx2.le
  have hpos0 : 0 < aggH h + x := by linarith
  have hne : aggH h - h j + x ≠ 0 := by
    rw [hj, sub_zero]; exact hpos0.ne'
  rw [vv_payoff_update P h j x hne] at h1
  have h3 : payoff P h j = 0 := by unfold payoff; rw [if_neg hH.ne', hj]; simp
  rw [h3, hj] at h1
  simp only [φ] at hx1
  have hpos : 0 < aggH h + x := by linarith
  have : x / (aggH h - 0 + x) * P.R = x * (P.R / (aggH h + x)) := by
    rw [sub_zero]; ring
  rw [this] at h1
  have : x * φ x ≤ 0 := by simp only [φ]; nlinarith
  nlinarith [mul_pos hx2 hx1]

lemma vv_down {N : ℕ} (P : Params N) (hP : P.Standing) (h : Fin N → ℝ)
    (hh : IsMiningEq P h) (i j : Fin N) (hij : i ≤ j) (hj : 0 < h j) : 0 < h i := by
  have hH := vv_pos P hP h hh
  have hnn := hh.1
  have hmono := hP.2.2.2.2
  have hγ := hP.2.2.1
  have hR := hP.2.1
  by_contra hi
  have hi0 : h i = 0 := le_antisymm (not_lt.1 hi) (hnn i)
  have a := vv_inactive P hP h hh i hi0
  have b := vv_foc P hP h hh j hj
  have hcij : P.c i ≤ P.c j := hmono hij
  have e : (aggH h - h j) * P.R / aggH h ^ 2 = P.R / aggH h - h j * P.R / aggH h ^ 2 := by
    field_simp
  have hp : 0 < h j * P.R / aggH h ^ 2 := by positivity
  have := mul_nonneg hγ (hnn j)
  linarith

theorem solution {N : ℕ} (P : Params N) (hP : P.Standing) (h : Fin N → ℝ)
    (hh : IsMiningEq P h) :
    0 < aggH h ∧
      ((activeCount h : ℝ) - 1) / aggH h * P.R - cumCost P (activeCount h) - P.γ * aggH h = 0 ∧
      1 / aggH h * (((activeCount h : ℝ) - 1) * P.R - cumCost P (activeCount h) * aggH h
        - P.γ * aggH h ^ 2) = 0 := by
  have hH := vv_pos P hP h hh
  have hnn := hh.1
  have hc := hP.2.2.2.1
  refine ⟨hH, ?_⟩
  set A := active h with hA
  set n := activeCount h with hn
  have hmemA : ∀ i, i ∈ A ↔ 0 < h i := by
    intro i; simp [hA, active]
  have hseg : ∀ i : Fin N, i ∈ A ↔ i.val < n := by
    intro i
    constructor
    · intro hi
      have hsub : Finset.Iic i ⊆ A := by
        intro j hj
        rw [Finset.mem_Iic] at hj
        exact (hmemA j).2 (vv_down P hP h hh j i hj ((hmemA i).1 hi))
      have := Finset.card_le_card hsub
      rw [Fin.card_Iic] at this
      exact Nat.lt_of_succ_le this
    · intro hi
      by_contra hni
      have hsub : A ⊆ Finset.Iio i := by
        intro j hj
        rw [Finset.mem_Iio]
        by_contra hji
        have hij : i ≤ j := not_lt.1 hji
        exact hni ((hmemA i).2 (vv_down P hP h hh i j hij ((hmemA j).1 hj)))
      have := Finset.card_le_card hsub
      rw [Fin.card_Iio] at this
      exact absurd hi (not_lt.2 this)
  have hAeq : A = Finset.univ.filter (fun i : Fin N => i.val < n) := by
    ext i; simp [hseg]
  have hcum : cumCost P n = ∑ i ∈ A, P.c i := by
    unfold cumCost; rw [hAeq]
  have hsumh : ∑ i ∈ A, h i = aggH h := by
    unfold aggH
    rw [hA]; unfold active
    exact Finset.sum_filter_of_ne (fun x _ hx => lt_of_le_of_ne (hnn x) (fun h0 => hx h0.symm))
  have e1 : ∑ i ∈ A, (aggH h - h i) * P.R / aggH h ^ 2 = ∑ i ∈ A, (P.c i + P.γ * h i) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact vv_foc P hP h hh i ((hmemA i).1 hi)
  have e2 : ∑ i ∈ A, (aggH h - h i) * P.R / aggH h ^ 2 = ((n : ℝ) * aggH h - aggH h) * P.R / aggH h ^ 2 := by
    rw [← Finset.sum_div, ← Finset.sum_mul, Finset.sum_sub_distrib, hsumh]
    simp [hn, hA, activeCount]
  have e3 : ∑ i ∈ A, (P.c i + P.γ * h i) = cumCost P n + P.γ * aggH h := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsumh, hcum]
  rw [e2, e3] at e1
  have key : ((n : ℝ) - 1) / aggH h * P.R - cumCost P n - P.γ * aggH h = 0 := by
    have : ((n : ℝ) * aggH h - aggH h) * P.R / aggH h ^ 2 = ((n : ℝ) - 1) / aggH h * P.R := by
      field_simp
    linarith
  refine ⟨key, ?_⟩
  have : ((n : ℝ) - 1) * P.R - cumCost P n * aggH h - P.γ * aggH h ^ 2
      = aggH h * (((n : ℝ) - 1) / aggH h * P.R - cumCost P n - P.γ * aggH h) := by
    field_simp
  rw [this, key]; simp
