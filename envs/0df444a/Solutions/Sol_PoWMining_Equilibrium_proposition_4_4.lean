-- Prove2me | solution 1 for PoWMining.Equilibrium.proposition_4_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T07:06:15.946543+00:00
-- url     : https://prove2.me/submissions/cd1d8333-8bcf-4749-95a4-3f6fee100bbc

import Mathlib
import Definitions.Def_PoWMining_Equilibrium_Setting

set_option autoImplicit false

namespace PoWAux7a4f

open PoWMining.Equilibrium

lemma aggH_update {N : ℕ} (h : Fin N → ℝ) (i : Fin N) (x : ℝ) :
    aggH (Function.update h i x) = aggH h - h i + x := by
  unfold aggH
  rw [Finset.sum_update_of_mem (Finset.mem_univ i),
    ← Finset.add_sum_erase Finset.univ h (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]
  ring

lemma payoff_update {N : ℕ} (P : Params N) (h : Fin N → ℝ) (i : Fin N) (x : ℝ) :
    payoff P (Function.update h i x) i =
      if aggH h - h i + x = 0 then 0
      else x / (aggH h - h i + x) * P.R - P.c i * x - P.γ / 2 * x ^ 2 := by
  unfold payoff
  rw [aggH_update, Function.update_self]

lemma aggH_sub_nonneg {N : ℕ} (h : Fin N → ℝ) (hnn : ∀ j, 0 ≤ h j) (i : Fin N) :
    0 ≤ aggH h - h i := by
  unfold aggH
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have : 0 ≤ ∑ j ∈ Finset.univ.erase i, h j := Finset.sum_nonneg (fun j _ => hnn j)
  linarith

/-- Tangent-line bound for the concave miner objective. -/
lemma tangent (R S c γ hh x : ℝ) (hS : 0 < S) (hh0 : 0 ≤ hh) (hx : 0 ≤ x) (hγ : 0 ≤ γ)
    (hR : 0 ≤ R) (hcond : (x - hh) * (R * S / (S + hh) ^ 2 - c - γ * hh) ≤ 0) :
    x / (S + x) * R - c * x - γ / 2 * x ^ 2 ≤ hh / (S + hh) * R - c * hh - γ / 2 * hh ^ 2 := by
  have h1 : 0 < S + x := by linarith
  have h2 : 0 < S + hh := by linarith
  have e : (x / (S + x) * R - c * x - γ / 2 * x ^ 2) - (hh / (S + hh) * R - c * hh - γ / 2 * hh ^ 2)
      = -(R * S * (x - hh) ^ 2 / ((S + x) * (S + hh) ^ 2))
        + (x - hh) * (R * S / (S + hh) ^ 2 - c - γ * hh) - γ / 2 * (x - hh) ^ 2 := by
    field_simp
    ring
  have t1 : 0 ≤ R * S * (x - hh) ^ 2 / ((S + x) * (S + hh) ^ 2) := by positivity
  have t2 : 0 ≤ γ / 2 * (x - hh) ^ 2 := by positivity
  linarith

/-- First-order condition at an interior maximiser. -/
lemma foc_active (R S c γ hh : ℝ) (hS : 0 < S) (hh0 : 0 < hh)
    (hmax : ∀ x, 0 ≤ x → x / (S + x) * R - c * x - γ / 2 * x ^ 2
        ≤ hh / (S + hh) * R - c * hh - γ / 2 * hh ^ 2) :
    R * S / (S + hh) ^ 2 = c + γ * hh := by
  have hne : S + hh ≠ 0 := by linarith
  have hd : HasDerivAt (fun x : ℝ => x / (S + x) * R - c * x - γ / 2 * x ^ 2)
      (S / (S + hh) ^ 2 * R - c - γ * hh) hh := by
    have a := (((hasDerivAt_id' hh).div ((hasDerivAt_id' hh).const_add S) hne).mul_const R)
    have b := (hasDerivAt_id' hh).const_mul c
    have d := (hasDerivAt_pow 2 hh).const_mul (γ / 2)
    exact ((a.sub b).sub d).congr_deriv (by ring)
  have hloc : IsLocalMax (fun x : ℝ => x / (S + x) * R - c * x - γ / 2 * x ^ 2) hh := by
    filter_upwards [Ioi_mem_nhds hh0] with x hx
    exact hmax x (le_of_lt hx)
  have h0 := hloc.hasDerivAt_eq_zero hd
  have e : R * S / (S + hh) ^ 2 = S / (S + hh) ^ 2 * R := by ring
  rw [e]
  linarith

/-- Boundary condition at a zero maximiser. -/
lemma foc_zero (R S c γ : ℝ) (hS : 0 < S) (hγ : 0 ≤ γ) (hR : 0 ≤ R)
    (hmax : ∀ x, 0 ≤ x → x / (S + x) * R - c * x - γ / 2 * x ^ 2 ≤ 0) :
    R / S ≤ c := by
  by_contra hlt
  push Not at hlt
  set d := R / S - c with hd
  have hdpos : 0 < d := by linarith
  set a := R / S ^ 2 + γ / 2 + 1 with ha
  have hapos : 0 < a := by positivity
  set x := d / (2 * a) with hx
  have hxpos : 0 < x := by positivity
  have hxa : x * a = d / 2 := by rw [hx]; field_simp
  have h1 : R / S - R * x / S ^ 2 ≤ R / (S + x) := by
    have : R / (S + x) - (R / S - R * x / S ^ 2) = R * x ^ 2 / (S ^ 2 * (S + x)) := by
      field_simp
      ring
    have : 0 ≤ R * x ^ 2 / (S ^ 2 * (S + x)) := by positivity
    linarith
  have key := hmax x hxpos.le
  have e1 : x / (S + x) * R = x * (R / (S + x)) := by ring
  have e2 : x * (R / (S + x)) ≥ x * (R / S - R * x / S ^ 2) :=
    mul_le_mul_of_nonneg_left h1 hxpos.le
  have e3 : R * x / S ^ 2 = x * (R / S ^ 2) := by ring
  have e4 : x * (R / S - R * x / S ^ 2) - c * x - γ / 2 * x ^ 2
      = x * (d - x * (a - 1)) := by
    rw [e3, ha, hd]; ring
  have e5 : x * (d - x * (a - 1)) > 0 := by
    have : d - x * (a - 1) = d / 2 + x := by
      have : x * (a - 1) = x * a - x := by ring
      rw [this, hxa]; ring
    rw [this]; positivity
  linarith

/-- Key equivalence between the participation inequality and `c < t`. -/
lemma key_iff (C t c G k1 : ℝ) (ht : 0 < t) (hc : 0 < c) (hk1 : 0 < k1) (hG : 0 ≤ G)
    (heq : k1 * t = C + G / t) : (k1 * c < C + G / c ↔ c < t) := by
  constructor
  · intro h
    by_contra hct
    push Not at hct
    have : G / c ≤ G / t := div_le_div_of_nonneg_left hG ht hct
    have : k1 * t ≤ k1 * c := mul_le_mul_of_nonneg_left hct hk1.le
    linarith
  · intro hct
    have : G / t ≤ G / c := div_le_div_of_nonneg_left hG hc hct.le
    have : k1 * c < k1 * t := mul_lt_mul_of_pos_left hct hk1
    linarith

lemma cumCost_succ {N : ℕ} (P : Params N) (k : ℕ) (hk : k < N) :
    cumCost P (k + 1) = cumCost P k + P.c ⟨k, hk⟩ := by
  unfold cumCost
  have : Finset.univ.filter (fun i : Fin N => i.val < k + 1)
      = insert ⟨k, hk⟩ (Finset.univ.filter (fun i : Fin N => i.val < k)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [this, Finset.sum_insert (by simp)]
  ring

lemma cumCost_succ' {N : ℕ} (P : Params N) (k : ℕ) (i : Fin N) (hi : i.val = k) :
    cumCost P (k + 1) = cumCost P k + P.c i := by
  rw [cumCost_succ P k (by rw [← hi]; exact i.isLt)]
  congr 2
  exact Fin.ext hi.symm

lemma card_lt {N : ℕ} (k : ℕ) (hk : k ≤ N) :
    (Finset.univ.filter (fun i : Fin N => i.val < k)).card = k := by
  have := Fin.card_filter_val_lt (n := N) (m := k)
  rw [this]; omega

lemma cumCost_pos {N : ℕ} (P : Params N) (hc : ∀ i, 0 < P.c i) (k : ℕ) (hk1 : 1 ≤ k)
    (hkN : k ≤ N) : 0 < cumCost P k := by
  unfold cumCost
  apply Finset.sum_pos (fun i _ => hc i)
  exact ⟨⟨0, by omega⟩, by simp; omega⟩

lemma lowerset_eq {N : ℕ} (A : Finset (Fin N)) (hA : ∀ i j : Fin N, j ≤ i → i ∈ A → j ∈ A) :
    A = Finset.univ.filter (fun i : Fin N => i.val < A.card) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hi
    have hsub : Finset.Iic i ⊆ A := by
      intro j hj
      exact hA i j (Finset.mem_Iic.1 hj) hi
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
  · intro hi
    by_contra hni
    have hsub : A ⊆ Finset.Iio i := by
      intro j hj
      rw [Finset.mem_Iio]
      by_contra hle
      push Not at hle
      exact hni (hA j i hle hj)
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega

/-- Downward closure of the participation condition. -/
lemma partCond_down {N : ℕ} (P : Params N) (hP : P.Standing) (m : ℕ) (hm : 2 ≤ m)
    (hmN : m + 1 ≤ N) (hpc : partCond P (m + 1)) : partCond P m := by
  obtain ⟨hN, hR, hγ, hc, hmono⟩ := hP
  obtain ⟨_, i', hi', hlt⟩ := hpc
  have hi'v : i'.val = m := by omega
  refine ⟨hm, ⟨m - 1, by omega⟩, by simp; omega, ?_⟩
  rw [cumCost_succ' P m i' hi'v] at hlt
  set c' := P.c i'
  set c := P.c ⟨m - 1, by omega⟩
  have hcc : c ≤ c' := hmono (by rw [Fin.le_def]; show m - 1 ≤ i'.val; omega)
  have hcpos : 0 < c := hc _
  have hc'pos : 0 < c' := hc _
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hcast : ((m + 1 : ℕ) : ℝ) - 1 = (m : ℝ) := by push_cast; ring
  rw [hcast, lt_div_iff₀ (by linarith)] at hlt
  rw [lt_div_iff₀ hm1]
  have hG : 0 ≤ P.R * P.γ := mul_nonneg hR.le hγ
  have h1 : P.R * P.γ / c' ≤ P.R * P.γ / c := div_le_div_of_nonneg_left hG hcpos hcc
  have h2 : c * ((m : ℝ) - 1) ≤ c' * ((m : ℝ) - 1) := mul_le_mul_of_nonneg_right hcc hm1.le
  nlinarith

lemma partCond_down_many {N : ℕ} (P : Params N) (hP : P.Standing) (k : ℕ) (hk : 2 ≤ k) :
    ∀ d : ℕ, k + 1 + d ≤ N → partCond P (k + 1 + d) → partCond P (k + 1) := by
  intro d
  induction d with
  | zero => intro _ h; simpa using h
  | succ d ih =>
    intro hN hpc
    apply ih (by omega)
    have := partCond_down P hP (k + 1 + d) (by omega) (by omega)
      (by rw [show k + 1 + d + 1 = k + 1 + (d + 1) by ring]; exact hpc)
    exact this

/-- The structure of an arbitrary equilibrium. -/
lemma eq_props {N : ℕ} (P : Params N) (hP : P.Standing) (h : Fin N → ℝ)
    (he : IsMiningEq P h) :
    2 ≤ activeCount h ∧ activeCount h ≤ N ∧ partCond P (activeCount h) ∧
      (activeCount h + 1 ≤ N → ¬ partCond P (activeCount h + 1)) := by
  obtain ⟨hN, hR, hγ, hc, hmono⟩ := hP
  unfold IsMiningEq CachonCoord.Proportional.IsNash at he
  obtain ⟨hnn, hnash⟩ := he
  have hnash' : ∀ i x, 0 ≤ x → payoff P (Function.update h i x) i ≤ payoff P h i :=
    fun i x hx => hnash i x hx
  clear hnash
  have hH0 : 0 ≤ aggH h := Finset.sum_nonneg (fun i _ => hnn i)
  -- aggregate is positive
  have hHpos : 0 < aggH h := by
    rcases hH0.lt_or_eq with hlt | heq
    · exact hlt
    exfalso
    have hall : ∀ i, h i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn j)).1 heq.symm i (Finset.mem_univ i)
    let i0 : Fin N := ⟨0, by omega⟩
    have hc0 := hc i0
    set x := P.R / (P.c i0 + P.γ + P.R) with hx
    have hxpos : 0 < x := by positivity
    have hx1 : x < 1 := by rw [hx, div_lt_one (by positivity)]; linarith
    have hxe : (P.c i0 + P.γ + P.R) * x = P.R := by rw [hx]; field_simp
    have := hnash' i0 x hxpos.le
    rw [payoff_update] at this
    unfold payoff at this
    rw [← heq, hall i0] at this
    simp only [sub_zero, zero_add, hxpos.ne', if_false, if_true] at this
    rw [div_self hxpos.ne'] at this
    nlinarith [mul_nonneg hγ hxpos.le, mul_pos hc0 hxpos]
  set H := aggH h with hHdef
  -- per-miner conditions
  have hphi : ∀ i, 0 < H - h i → ∀ x, 0 ≤ x →
      x / ((H - h i) + x) * P.R - P.c i * x - P.γ / 2 * x ^ 2
        ≤ h i / ((H - h i) + h i) * P.R - P.c i * h i - P.γ / 2 * h i ^ 2 := by
    intro i hS x hx
    have := hnash' i x hx
    rw [payoff_update, if_neg (by linarith)] at this
    unfold payoff at this
    rw [if_neg hHpos.ne'] at this
    rw [show H - h i + h i = H by ring]
    exact this
  have hSpos : ∀ i, 0 < h i → 0 < H - h i := by
    intro i hi
    rcases (aggH_sub_nonneg h hnn i).lt_or_eq with hlt | heq
    · exact hlt
    exfalso
    have := hnash' i (h i / 2) (by linarith)
    rw [payoff_update] at this
    unfold payoff at this
    rw [← hHdef, ← heq, if_neg (by linarith), if_neg hHpos.ne'] at this
    have hHi : H = h i := by linarith
    rw [hHi, div_self hi.ne', zero_add, div_self (by linarith)] at this
    nlinarith [hc i]
  set t := P.R / H with htdef
  have htpos : 0 < t := div_pos hR hHpos
  have hact : ∀ i, 0 < h i → P.R * (H - h i) / H ^ 2 = P.c i + P.γ * h i := by
    intro i hi
    have := foc_active P.R (H - h i) (P.c i) P.γ (h i) (hSpos i hi) hi (hphi i (hSpos i hi))
    rwa [show H - h i + h i = H by ring] at this
  have hactlt : ∀ i, 0 < h i → P.c i < t := by
    intro i hi
    have e := hact i hi
    have : P.R * (H - h i) / H ^ 2 < t := by
      rw [htdef, div_lt_div_iff₀ (by positivity) hHpos]
      have : 0 < P.R * h i * H := by have := mul_pos hR hi; positivity
      nlinarith
    nlinarith [mul_nonneg hγ (hnn i)]
  have hinact : ∀ i, ¬ 0 < h i → t ≤ P.c i := by
    intro i hi
    have hi0 : h i = 0 := le_antisymm (not_lt.1 hi) (hnn i)
    have hS : 0 < H - h i := by rw [hi0]; linarith
    have := foc_zero P.R (H - h i) (P.c i) P.γ hS hγ hR.le (by
      intro x hx
      have := hphi i hS x hx
      rw [hi0] at this ⊢
      simpa using this)
    rwa [hi0, sub_zero] at this
  have hmem : ∀ i, i ∈ active h ↔ P.c i < t := by
    intro i
    unfold active
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact hactlt i
    · intro hci
      by_contra hn
      have := hinact i hn
      linarith
  have hlow : ∀ i j : Fin N, j ≤ i → i ∈ active h → j ∈ active h := by
    intro i j hji hi
    rw [hmem] at hi ⊢
    exact lt_of_le_of_lt (hmono hji) hi
  set k := activeCount h with hkdef
  have hAeq : active h = Finset.univ.filter (fun i : Fin N => i.val < k) := lowerset_eq _ hlow
  have hsumA : ∑ i ∈ active h, h i = H := by
    unfold active
    exact Finset.sum_filter_of_ne (s := Finset.univ) (p := fun i => 0 < h i) (f := h)
      (fun i _ hi => lt_of_le_of_ne (hnn i) (Ne.symm hi))
  have hkN : k ≤ N := by
    have := Finset.card_le_univ (active h)
    rw [Fintype.card_fin] at this
    exact this
  have hCA : ∑ i ∈ active h, P.c i = cumCost P k := by
    rw [hAeq]; rfl
  -- summed first-order conditions
  have hsumfoc : ∑ i ∈ active h, (P.c i + P.γ * h i) = ∑ i ∈ active h, P.R * (H - h i) / H ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    unfold active at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact (hact i hi).symm
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsumA, hCA] at hsumfoc
  have hterm : ∀ i, P.R * (H - h i) / H ^ 2 = t - (P.R / H ^ 2) * h i := by
    intro i; rw [htdef]; field_simp
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib, Finset.sum_const,
    ← Finset.mul_sum, hsumA, nsmul_eq_mul] at hsumfoc
  have hcardk : ((active h).card : ℝ) = (k : ℝ) := rfl
  rw [hcardk] at hsumfoc
  have hRH : P.R / H ^ 2 * H = t := by rw [htdef]; field_simp
  rw [hRH] at hsumfoc
  have hG : 0 ≤ P.R * P.γ := mul_nonneg hR.le hγ
  have hγt : P.R * P.γ / t = P.γ * H := by rw [htdef]; field_simp
  have heq : ((k : ℝ) - 1) * t = cumCost P k + P.R * P.γ / t := by rw [hγt]; linarith
  -- at least two active miners
  have hk1 : 1 ≤ k := by
    by_contra hk0
    have hk0' : active h = ∅ := by
      rw [← Finset.card_eq_zero]; show activeCount h = 0; omega
    rw [hk0', Finset.sum_empty] at hsumA
    linarith
  have hk2 : 2 ≤ k := by
    by_contra hk
    have hk1' : k = 1 := by omega
    have hpos := cumCost_pos P hc k hk1 hkN
    have hkr : ((k : ℝ) - 1) = 0 := by rw [hk1']; norm_num
    rw [hkr, zero_mul] at heq
    have : 0 ≤ P.R * P.γ / t := div_nonneg hG htpos.le
    linarith
  have hk1r : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    linarith
  refine ⟨hk2, hkN, ?_, ?_⟩
  · refine ⟨hk2, ⟨k - 1, by omega⟩, by simp; omega, ?_⟩
    have hin : (⟨k - 1, by omega⟩ : Fin N) ∈ active h := by
      rw [hAeq]; simp; omega
    rw [hmem] at hin
    rw [lt_div_iff₀ hk1r]
    have := (key_iff (cumCost P k) t (P.c ⟨k - 1, by omega⟩) (P.R * P.γ) ((k : ℝ) - 1) htpos
      (hc _) hk1r hG heq).2 hin
    linarith
  · intro hk1N hpc
    obtain ⟨_, i, hi, hlt⟩ := hpc
    have hiv : i.val = k := by omega
    have hnin : i ∉ active h := by
      rw [hAeq]; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]; omega
    rw [hmem] at hnin
    rw [cumCost_succ' P k i hiv] at hlt
    have hcast : ((k + 1 : ℕ) : ℝ) - 1 = (k : ℝ) := by push_cast; ring
    have hkpos : (0 : ℝ) < k := by linarith
    rw [hcast, lt_div_iff₀ hkpos] at hlt
    have := (key_iff (cumCost P k) t (P.c i) (P.R * P.γ) ((k : ℝ) - 1) htpos
      (hc _) hk1r hG heq).1 (by linarith)
    exact hnin this

lemma exists_root (C R γ K1 : ℝ) (hC : 0 < C) (hR : 0 < R) (hγ : 0 ≤ γ) (hK : 0 < K1) :
    ∃ H, 0 < H ∧ γ * H ^ 2 + C * H = K1 * R := by
  have hb : (0 : ℝ) ≤ K1 * R / C := by positivity
  have hcont : ContinuousOn (fun H : ℝ => γ * H ^ 2 + C * H) (Set.Icc 0 (K1 * R / C)) := by
    fun_prop
  have hKR : 0 < K1 * R := mul_pos hK hR
  have hmem : K1 * R ∈ Set.Icc ((fun H : ℝ => γ * H ^ 2 + C * H) 0)
      ((fun H : ℝ => γ * H ^ 2 + C * H) (K1 * R / C)) := by
    simp only
    constructor
    · nlinarith
    · have : C * (K1 * R / C) = K1 * R := by field_simp
      nlinarith [mul_nonneg hγ (sq_nonneg (K1 * R / C))]
  obtain ⟨H, hH, hfH⟩ := intermediate_value_Icc hb hcont hmem
  simp only at hfH
  refine ⟨H, ?_, hfH⟩
  rcases hH.1.lt_or_eq with h | h
  · exact h
  · rw [← h] at hfH
    nlinarith

lemma partCond_two {N : ℕ} (P : Params N) (hP : P.Standing) : partCond P 2 := by
  obtain ⟨hN, hR, hγ, hc, hmono⟩ := hP
  refine ⟨le_refl 2, ⟨1, by omega⟩, rfl, ?_⟩
  have h1 := cumCost_succ P 1 (by omega)
  have h0 := cumCost_pos P hc 1 le_rfl (by omega)
  have hG : 0 ≤ P.R * P.γ / P.c ⟨1, by omega⟩ := div_nonneg (mul_nonneg hR.le hγ) (hc _).le
  have : ((2 : ℕ) : ℝ) - 1 = 1 := by norm_num
  rw [this, div_one]
  linarith

lemma exists_eq {N : ℕ} (P : Params N) (hP : P.Standing) (K : ℕ) (hK2 : 2 ≤ K) (hKN : K ≤ N)
    (hpc : partCond P K) (hnext : K + 1 ≤ N → ¬ partCond P (K + 1)) :
    ∃ h : Fin N → ℝ, IsMiningEq P h := by
  obtain ⟨hN, hR, hγ, hc, hmono⟩ := hP
  have hCpos := cumCost_pos P hc K (by omega) hKN
  have hK1 : (0 : ℝ) < (K : ℝ) - 1 := by
    have : (2 : ℝ) ≤ K := by exact_mod_cast hK2
    linarith
  obtain ⟨H, hHpos, hroot⟩ := exists_root (cumCost P K) P.R P.γ ((K : ℝ) - 1) hCpos hR hγ hK1
  set C := cumCost P K with hCdef
  set t := P.R / H with htdef
  have htpos : 0 < t := div_pos hR hHpos
  have hG : 0 ≤ P.R * P.γ := mul_nonneg hR.le hγ
  have hγt : P.R * P.γ / t = P.γ * H := by rw [htdef]; field_simp
  have heq : ((K : ℝ) - 1) * t = C + P.R * P.γ / t := by
    rw [hγt, htdef, mul_div_assoc', div_eq_iff hHpos.ne']
    linear_combination (-1 : ℝ) * hroot
  obtain ⟨_, i0, hi0, hlt0⟩ := hpc
  have hci0 : P.c i0 < t := by
    rw [lt_div_iff₀ hK1] at hlt0
    exact (key_iff C t (P.c i0) (P.R * P.γ) ((K : ℝ) - 1) htpos (hc _) hK1 hG heq).1
      (by linarith)
  have hcsmall : ∀ j : Fin N, j.val < K → P.c j < t := by
    intro j hj
    exact lt_of_le_of_lt (hmono (by rw [Fin.le_def]; omega)) hci0
  have hcbig : ∀ j : Fin N, K ≤ j.val → t ≤ P.c j := by
    intro j hj
    have hKN' : K < N := by omega
    by_contra hlt
    push Not at hlt
    have hle : P.c ⟨K, hKN'⟩ ≤ P.c j := hmono (by rw [Fin.le_def]; exact hj)
    have hlt' : P.c ⟨K, hKN'⟩ < t := lt_of_le_of_lt hle hlt
    apply hnext (by omega)
    refine ⟨by omega, ⟨K, hKN'⟩, rfl, ?_⟩
    rw [cumCost_succ P K hKN']
    have hcast : ((K + 1 : ℕ) : ℝ) - 1 = (K : ℝ) := by push_cast; ring
    have hKpos : (0 : ℝ) < K := by linarith
    rw [hcast, lt_div_iff₀ hKpos]
    have := (key_iff C t (P.c ⟨K, hKN'⟩) (P.R * P.γ) ((K : ℝ) - 1) htpos (hc _) hK1 hG heq).2 hlt'
    linarith
  set D := P.γ + P.R / H ^ 2 with hDdef
  have hDpos : 0 < D := by positivity
  set h : Fin N → ℝ := fun i => if i.val < K then (t - P.c i) / D else 0 with hhdef
  have hsum : aggH h = H := by
    unfold aggH
    rw [hhdef]
    simp only
    rw [← Finset.sum_filter, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const,
      card_lt K hKN, nsmul_eq_mul]
    have hCC : ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < K), P.c i = C := rfl
    rw [hCC, div_eq_iff hDpos.ne']
    have : H * D = P.γ * H + t := by rw [hDdef, htdef]; field_simp
    rw [this]
    linarith
  have hnn : ∀ i, 0 ≤ h i := by
    intro i
    by_cases hi : i.val < K
    · simp only [hhdef, hi, if_true]
      exact div_nonneg (sub_nonneg.2 (hcsmall i hi).le) hDpos.le
    · simp only [hhdef, hi, if_false, le_refl]
  refine ⟨h, ?_⟩
  unfold IsMiningEq CachonCoord.Proportional.IsNash
  refine ⟨hnn, ?_⟩
  intro i x hx
  show payoff P (Function.update h i x) i ≤ payoff P h i
  rw [payoff_update, hsum]
  unfold payoff
  rw [hsum, if_neg hHpos.ne']
  by_cases hi : i.val < K
  · have hval : h i = (t - P.c i) / D := by simp only [hhdef, hi, if_true]
    have hpos : 0 < h i := by
      rw [hval]; exact div_pos (sub_pos.2 (hcsmall i hi)) hDpos
    have hDh : D * h i = t - P.c i := by rw [hval]; field_simp
    have hfoc : P.R * (H - h i) / H ^ 2 = P.c i + P.γ * h i := by
      have e1 : P.R * (H - h i) / H ^ 2 = t - (P.R / H ^ 2) * h i := by
        rw [htdef]; field_simp
      have e2 : (P.R / H ^ 2) * h i = D * h i - P.γ * h i := by rw [hDdef]; ring
      rw [e1, e2, hDh]; ring
    have hS : 0 < H - h i := by
      by_contra hS
      push Not at hS
      have : P.R * (H - h i) / H ^ 2 ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hR.le hS) (by positivity)
      nlinarith [hc i, mul_nonneg hγ hpos.le]
    rw [if_neg (by linarith)]
    have := tangent P.R (H - h i) (P.c i) P.γ (h i) x hS hpos.le hx hγ hR.le (by
      have : P.R * (H - h i) / (H - h i + h i) ^ 2 - P.c i - P.γ * h i = 0 := by
        rw [show H - h i + h i = H by ring, hfoc]; ring
      rw [this, mul_zero])
    rwa [show H - h i + h i = H by ring] at this
  · have hval : h i = 0 := by simp only [hhdef, hi, if_false]
    rw [hval]
    rw [if_neg (by linarith)]
    have hcb := hcbig i (by omega)
    have := tangent P.R H (P.c i) P.γ 0 x hHpos le_rfl hx hγ hR.le (by
      have : P.R * H / (H + 0) ^ 2 = t := by rw [htdef, add_zero]; field_simp
      rw [this]
      nlinarith)
    simpa using this

lemma partCond_mono {N : ℕ} (P P' : Params N) (hcpos : ∀ i, 0 < P.c i) (hc : P'.c = P.c)
    (hRγ : P.R * P.γ ≤ P'.R * P'.γ) (k : ℕ) (hpc : partCond P k) : partCond P' k := by
  obtain ⟨hk, i, hi, hlt⟩ := hpc
  refine ⟨hk, i, hi, ?_⟩
  have hcc : cumCost P' k = cumCost P k := by unfold cumCost; rw [hc]
  rw [hcc, hc]
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  rw [lt_div_iff₀ hk1] at hlt ⊢
  have : P.R * P.γ / P.c i ≤ P'.R * P'.γ / P.c i := div_le_div_of_nonneg_right hRγ (hcpos i).le
  linarith

lemma greatest {N : ℕ} (P : Params N) (hP : P.Standing) (h : Fin N → ℝ) (he : IsMiningEq P h) :
    IsGreatest {k : ℕ | 2 ≤ k ∧ k ≤ N ∧ partCond P k} (activeCount h) := by
  obtain ⟨h2, hN, hpc, hnot⟩ := eq_props P hP h he
  refine ⟨⟨h2, hN, hpc⟩, ?_⟩
  rintro m ⟨hm2, hmN, hmpc⟩
  by_contra hlt
  push Not at hlt
  have := partCond_down_many P hP (activeCount h) h2 (m - (activeCount h + 1)) (by omega)
    (by rw [show activeCount h + 1 + (m - (activeCount h + 1)) = m by omega]; exact hmpc)
  exact hnot (by omega) this

end PoWAux7a4f

open PoWMining.Equilibrium in
theorem solution {N : ℕ} (P : Params N) (hP : P.Standing) :
    (∃ h : Fin N → ℝ, IsMiningEq P h) ∧
      (∀ h : Fin N → ℝ, IsMiningEq P h →
        IsGreatest {k : ℕ | 2 ≤ k ∧ k ≤ N ∧ partCond P k} (activeCount h)) ∧
      (∀ P' : Params N, P'.Standing → P'.c = P.c → P.R ≤ P'.R → P.γ ≤ P'.γ →
        ∀ h h' : Fin N → ℝ, IsMiningEq P h → IsMiningEq P' h' →
          activeCount h ≤ activeCount h') := by
  classical
  refine ⟨?_, fun h he => PoWAux7a4f.greatest P hP h he, ?_⟩
  · let S := (Finset.range (N + 1)).filter (fun k => 2 ≤ k ∧ k ≤ N ∧ partCond P k)
    have h2mem : 2 ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_range]
      exact ⟨by have := hP.1; omega, le_refl 2, hP.1, PoWAux7a4f.partCond_two P hP⟩
    have hne : S.Nonempty := ⟨2, h2mem⟩
    obtain ⟨K, hKmem, hKmax⟩ : ∃ K ∈ S, ∀ m ∈ S, m ≤ K :=
      ⟨S.max' hne, S.max'_mem hne, fun m hm => S.le_max' m hm⟩
    simp only [S, Finset.mem_filter, Finset.mem_range] at hKmem
    obtain ⟨_, hK2, hKN, hKpc⟩ := hKmem
    refine PoWAux7a4f.exists_eq P hP K hK2 hKN hKpc ?_
    intro hK1 hpc1
    have hmem : K + 1 ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, by omega, hK1, hpc1⟩
    have := hKmax _ hmem
    omega
  · intro P' hP' hc hR hγ h h' he he'
    have g1 := PoWAux7a4f.greatest P hP h he
    have g2 := PoWAux7a4f.greatest P' hP' h' he'
    have hRγ : P.R * P.γ ≤ P'.R * P'.γ := mul_le_mul hR hγ hP.2.2.1 hP'.2.1.le
    obtain ⟨⟨a1, a2, a3⟩, _⟩ := g1
    exact g2.2 ⟨a1, a2, PoWAux7a4f.partCond_mono P P' hP.2.2.2.1 hc hRγ _ a3⟩
