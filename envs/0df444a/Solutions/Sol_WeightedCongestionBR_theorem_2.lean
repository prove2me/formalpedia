-- Prove2me | solution 1 for WeightedCongestionBR.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T04:04:54.844615+00:00
-- url     : https://prove2.me/submissions/46693511-8e9d-488c-bbb0-50a5bcd7c45d

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_privateCost
import Definitions.Def_CongestionApproxPNE_IsPolyGame
import Definitions.Def_WeightedCongestionBR_groupCost
import Definitions.Def_WeightedCongestionBR_IsGroupEq
import Definitions.Def_WeightedCongestionBR_genGolden
set_option autoImplicit false
open scoped NNReal
open HarksKlimm.Consistency

namespace Aux_WCBR_t2

open WeightedCongestionBR

theorem root_exists (N : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ r : ℝ, 0 < r ∧ ρ * (r + 1) ^ N = r ^ (N + 1) := by
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = ρ * 2 ^ N + 1 := ⟨_, rfl⟩
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  have hX1 : 1 ≤ X := by rw [hX]; nlinarith
  have hX0 : 0 ≤ X := by linarith
  have hcont : ContinuousOn (fun t : ℝ => t ^ (N + 1) - ρ * (t + 1) ^ N) (Set.Icc 0 X) := by
    fun_prop
  have hiv := intermediate_value_Icc hX0 hcont
  have hg0 : (fun t : ℝ => t ^ (N + 1) - ρ * (t + 1) ^ N) 0 = -ρ := by simp
  have hgX : 0 ≤ (fun t : ℝ => t ^ (N + 1) - ρ * (t + 1) ^ N) X := by
    show 0 ≤ X ^ (N + 1) - ρ * (X + 1) ^ N
    have h1 : (X + 1) ^ N ≤ (2 * X) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
    rw [mul_pow] at h1
    have hXN : 0 < X ^ N := by positivity
    have h3 : ρ * 2 ^ N ≤ X := by rw [hX]; linarith
    have h4 : ρ * 2 ^ N * X ^ N ≤ X * X ^ N := mul_le_mul_of_nonneg_right h3 hXN.le
    have h5 := mul_le_mul_of_nonneg_left h1 hρ.le
    rw [pow_succ]
    linarith
  have hmem : (0 : ℝ) ∈ Set.Icc ((fun t : ℝ => t ^ (N + 1) - ρ * (t + 1) ^ N) 0)
      ((fun t : ℝ => t ^ (N + 1) - ρ * (t + 1) ^ N) X) := by
    rw [hg0]; exact ⟨by linarith, hgX⟩
  obtain ⟨r, ⟨hr0, _⟩, hr⟩ := hiv hmem
  have hr' : r ^ (N + 1) - ρ * (r + 1) ^ N = 0 := hr
  refine ⟨r, ?_, by linarith⟩
  rcases hr0.lt_or_eq with h | h
  · exact h
  · subst h
    rw [zero_pow (show N + 1 ≠ 0 by omega), zero_add, one_pow] at hr'
    linarith

theorem strict_mono_aux (N : ℕ) (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    a ^ (N + 1) * (b + 1) ^ N < b ^ (N + 1) * (a + 1) ^ N := by
  have hb : 0 < b := by linarith
  have h1 : a * (b + 1) ≤ b * (a + 1) := by nlinarith
  have h2 : (a * (b + 1)) ^ N ≤ (b * (a + 1)) ^ N := pow_le_pow_left₀ (by positivity) h1 N
  have h3 : 0 < (b * (a + 1)) ^ N := by positivity
  calc a ^ (N + 1) * (b + 1) ^ N = a * (a * (b + 1)) ^ N := by rw [mul_pow]; ring
    _ ≤ a * (b * (a + 1)) ^ N := mul_le_mul_of_nonneg_left h2 ha.le
    _ < b * (b * (a + 1)) ^ N := mul_lt_mul_of_pos_right hab h3
    _ = b ^ (N + 1) * (a + 1) ^ N := by rw [mul_pow]; ring

theorem root_unique (N : ℕ) (ρ : ℝ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hra : ρ * (a + 1) ^ N = a ^ (N + 1)) (hrb : ρ * (b + 1) ^ N = b ^ (N + 1)) : a = b := by
  have key : a ^ (N + 1) * (b + 1) ^ N = b ^ (N + 1) * (a + 1) ^ N := by
    rw [← hra, ← hrb]; ring
  rcases lt_trichotomy a b with h | h | h
  · have := strict_mono_aux N a b ha h; linarith
  · exact h
  · have := strict_mono_aux N b a hb h; linarith

theorem genGolden_eq (N : ℕ) (ρ r : ℝ) (hr : 0 < r) (hroot : ρ * (r + 1) ^ N = r ^ (N + 1)) :
    genGolden N ρ = r := by
  unfold genGolden
  have hset : {x : ℝ | 0 < x ∧ ρ * (x + 1) ^ N = x ^ (N + 1)} = {r} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, hxr⟩
      exact root_unique N ρ x r hx hr hxr hroot
    · rintro rfl
      exact ⟨hr, hroot⟩
  rw [hset, csSup_singleton]



theorem wpow (q : ℝ) (i d : ℕ) : (q ^ i) ^ (d + 1) = (q ^ (d + 1)) ^ i := by
  rw [← pow_mul, ← pow_mul, mul_comm]

/-- The lower-bound game: players `0..M` on a path of resources `0..M+1`. -/
noncomputable def LB (M d : ℕ) (Φ K : ℝ) (hΦ : 0 < Φ) : Game (M + 1) (M + 1 + 1) where
  players_pos := Nat.succ_pos M
  facilities_pos := Nat.succ_pos (M + 1)
  strategies := fun i => {{Fin.castSucc i}, {Fin.succ i}}
  strategies_nonempty := fun i =>
    ⟨{Fin.succ i}, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
  demand := fun i => ⟨Φ⁻¹ ^ (i : ℕ), pow_nonneg (inv_nonneg.mpr hΦ.le) _⟩
  demand_pos := fun i => NNReal.coe_pos.mp (pow_pos (inv_pos.mpr hΦ) _)
  cost := fun k x => K ^ (max (k : ℕ) 1) * (x : ℝ) ^ d

noncomputable def sR (M d : ℕ) (Φ K : ℝ) (hΦ : 0 < Φ) : (LB M d Φ K hΦ).Profile :=
  fun i => ⟨{Fin.succ i}, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩

noncomputable def sL (M d : ℕ) (Φ K : ℝ) (hΦ : 0 < Φ) : (LB M d Φ K hΦ).Profile :=
  fun i => ⟨{Fin.castSucc i}, Finset.mem_insert_self _ _⟩

noncomputable def Lr (M d : ℕ) (Φ K : ℝ) (hΦ : 0 < Φ) (t : (LB M d Φ K hΦ).Profile)
    (e : Fin (M + 1 + 1)) : ℝ :=
  ∑ j : Fin (M + 1), if e ∈ (t j).val then Φ⁻¹ ^ (j : ℕ) else 0

theorem load_eq' (M d : ℕ) (Φ K : ℝ) (hΦ : 0 < Φ) (t : (LB M d Φ K hΦ).Profile)
    (e : Fin (M + 1 + 1)) :
    ((load (LB M d Φ K hΦ) t e : ℝ≥0) : ℝ) = Lr M d Φ K hΦ t e := by
  unfold load Lr
  rw [NNReal.coe_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs
  · rfl
  · simp

theorem pc_eq (M d : ℕ) (Φ K : ℝ) (hΦ : 0 < Φ) (t : (LB M d Φ K hΦ).Profile) (u : Fin (M + 1)) :
    privateCost (LB M d Φ K hΦ) t u = ∑ f ∈ (t u).val,
      Φ⁻¹ ^ (u : ℕ) * (K ^ (max (f : ℕ) 1) * (Lr M d Φ K hΦ t f) ^ d) := by
  unfold privateCost
  refine Finset.sum_congr rfl (fun f _ => ?_)
  show Φ⁻¹ ^ (u : ℕ) * (K ^ (max (f : ℕ) 1) * ((load (LB M d Φ K hΦ) t f : ℝ≥0) : ℝ) ^ d) = _
  rw [load_eq']

theorem L_ge_one (M d : ℕ) (Φ K : ℝ) (hΦ : 0 < Φ) (t : (LB M d Φ K hΦ).Profile)
    (j : Fin (M + 1)) (e : Fin (M + 1 + 1)) (he : e ∈ (t j).val) :
    Φ⁻¹ ^ (j : ℕ) ≤ Lr M d Φ K hΦ t e := by
  unfold Lr
  have hle := Finset.single_le_sum
    (f := fun j : Fin (M + 1) => if e ∈ (t j).val then Φ⁻¹ ^ (j : ℕ) else 0)
    (fun j _ => by
      show 0 ≤ (if e ∈ (t j).val then Φ⁻¹ ^ (j : ℕ) else 0)
      split_ifs
      · exact pow_nonneg (inv_nonneg.mpr hΦ.le) _
      · exact le_rfl) (Finset.mem_univ j)
  simp only [he, ↓reduceIte] at hle
  exact hle

theorem L_ge_two (M d : ℕ) (Φ K : ℝ) (hΦ : 0 < Φ) (t : (LB M d Φ K hΦ).Profile)
    (j j' : Fin (M + 1)) (hjj : j ≠ j') (e : Fin (M + 1 + 1)) (he : e ∈ (t j).val)
    (he' : e ∈ (t j').val) :
    Φ⁻¹ ^ (j : ℕ) + Φ⁻¹ ^ (j' : ℕ) ≤ Lr M d Φ K hΦ t e := by
  unfold Lr
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ {j, j'})
    (f := fun j : Fin (M + 1) => if e ∈ (t j).val then Φ⁻¹ ^ (j : ℕ) else 0)
    (fun j _ _ => by
      show 0 ≤ (if e ∈ (t j).val then Φ⁻¹ ^ (j : ℕ) else 0)
      split_ifs
      · exact pow_nonneg (inv_nonneg.mpr hΦ.le) _
      · exact le_rfl)
  rw [Finset.sum_pair hjj] at hle
  simp only [he, he', ↓reduceIte] at hle
  exact hle

theorem L_sR (M d : ℕ) (Φ K : ℝ) (hΦ : 0 < Φ) (i : Fin (M + 1)) :
    Lr M d Φ K hΦ (sR M d Φ K hΦ) (Fin.succ i) = Φ⁻¹ ^ (i : ℕ) := by
  simp [Lr, sR]

theorem L_sL (M d : ℕ) (Φ K : ℝ) (hΦ : 0 < Φ) (i : Fin (M + 1)) :
    Lr M d Φ K hΦ (sL M d Φ K hΦ) (Fin.castSucc i) = Φ⁻¹ ^ (i : ℕ) := by
  simp [Lr, sL]

theorem pc_sR (M d : ℕ) (Φ K : ℝ) (hΦ : 0 < Φ) (hKq : K * Φ⁻¹ ^ (d + 1) = 1) (i : Fin (M + 1)) :
    privateCost (LB M d Φ K hΦ) (sR M d Φ K hΦ) i = K := by
  rw [pc_eq]
  have hv : ((sR M d Φ K hΦ) i).val = {Fin.succ i} := rfl
  rw [hv, Finset.sum_singleton, L_sR, Fin.val_succ, max_eq_left (by omega : 1 ≤ (i : ℕ) + 1)]
  calc Φ⁻¹ ^ (i : ℕ) * (K ^ ((i : ℕ) + 1) * (Φ⁻¹ ^ (i : ℕ)) ^ d)
      = K * (K * Φ⁻¹ ^ (d + 1)) ^ (i : ℕ) := by rw [mul_pow, ← wpow]; ring
    _ = K := by rw [hKq, one_pow, mul_one]

theorem pc_sL (M d : ℕ) (Φ K : ℝ) (hΦ : 0 < Φ) (hKq : K * Φ⁻¹ ^ (d + 1) = 1) (i : Fin (M + 1)) :
    privateCost (LB M d Φ K hΦ) (sL M d Φ K hΦ) i = if (i : ℕ) = 0 then K else 1 := by
  rw [pc_eq]
  have hv : ((sL M d Φ K hΦ) i).val = {Fin.castSucc i} := rfl
  rw [hv, Finset.sum_singleton, L_sL, Fin.coe_castSucc]
  split_ifs with h
  · rw [h]; simp
  · rw [max_eq_left (by omega : 1 ≤ (i : ℕ))]
    calc Φ⁻¹ ^ (i : ℕ) * (K ^ (i : ℕ) * (Φ⁻¹ ^ (i : ℕ)) ^ d)
        = (K * Φ⁻¹ ^ (d + 1)) ^ (i : ℕ) := by rw [mul_pow, ← wpow]; ring
      _ = 1 := by rw [hKq, one_pow]

theorem pc_pos (M d : ℕ) (Φ K : ℝ) (hΦ : 0 < Φ) (hK : 0 < K) (t : (LB M d Φ K hΦ).Profile)
    (u : Fin (M + 1)) : 0 < privateCost (LB M d Φ K hΦ) t u := by
  rw [pc_eq]
  have hmem : (t u).val ∈ ({{Fin.castSucc u}, {Fin.succ u}} : Finset (Finset (Fin (M + 1 + 1)))) :=
    (t u).property
  have hne : (t u).val.Nonempty := by
    rcases Finset.mem_insert.mp hmem with h | h
    · rw [h]; exact Finset.singleton_nonempty _
    · rw [Finset.mem_singleton.mp h]; exact Finset.singleton_nonempty _
  refine Finset.sum_pos (fun f hf => ?_) hne
  have hq : 0 < Φ⁻¹ ^ (u : ℕ) := pow_pos (inv_pos.mpr hΦ) _
  have hL := L_ge_one M d Φ K hΦ t u f hf
  have hL0 : 0 < Lr M d Φ K hΦ t f := lt_of_lt_of_le hq hL
  positivity

theorem gc_pos (M d : ℕ) (Φ K : ℝ) (hΦ : 0 < Φ) (hK : 0 < K) (t : (LB M d Φ K hΦ).Profile) :
    0 < groupCost (LB M d Φ K hΦ) Finset.univ t := by
  unfold groupCost
  exact Finset.sum_pos (fun u _ => pc_pos M d Φ K hΦ hK t u) Finset.univ_nonempty

theorem gc_sR (M d : ℕ) (Φ K : ℝ) (hΦ : 0 < Φ) (hKq : K * Φ⁻¹ ^ (d + 1) = 1) :
    groupCost (LB M d Φ K hΦ) Finset.univ (sR M d Φ K hΦ) = ((M : ℝ) + 1) * K := by
  unfold groupCost
  simp only [pc_sR M d Φ K hΦ hKq]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

theorem gc_sL (M d : ℕ) (Φ K : ℝ) (hΦ : 0 < Φ) (hKq : K * Φ⁻¹ ^ (d + 1) = 1) :
    groupCost (LB M d Φ K hΦ) Finset.univ (sL M d Φ K hΦ) = K + M := by
  unfold groupCost
  simp only [pc_sL M d Φ K hΦ hKq]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, ↓reduceIte, Nat.add_one_ne_zero]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

theorem isEq (M d : ℕ) (Φ K ρ : ℝ) (hΦ : 0 < Φ) (hK : 0 < K) (hρ : 1 ≤ ρ)
    (hKq : K * Φ⁻¹ ^ (d + 1) = 1) (hroot : ρ * (Φ + 1) ^ d = K) :
    IsGroupEq (LB M d Φ K hΦ) ρ Finset.univ (sR M d Φ K hΦ) := by
  intro u _ t
  have hmem : t.val ∈ ({{Fin.castSucc u}, {Fin.succ u}} : Finset (Finset (Fin (M + 1 + 1)))) :=
    t.property
  have hq0 : 0 < Φ⁻¹ := inv_pos.mpr hΦ
  rcases Finset.mem_insert.mp hmem with hL | hR
  · have hu_mem : Fin.castSucc u ∈ ((Function.update (sR M d Φ K hΦ) u t) u).val := by
      rw [Function.update_self, hL]; exact Finset.mem_singleton_self _
    have hL1 := L_ge_one M d Φ K hΦ (Function.update (sR M d Φ K hΦ) u t) u _ hu_mem
    obtain ⟨L, hLdef⟩ : ∃ L, L = Lr M d Φ K hΦ (Function.update (sR M d Φ K hΦ) u t)
        (Fin.castSucc u) := ⟨_, rfl⟩
    rw [← hLdef] at hL1
    rw [pc_sR M d Φ K hΦ hKq, pc_eq, Function.update_self, hL, Finset.sum_singleton,
      Fin.coe_castSucc, ← hLdef]
    rcases Nat.eq_zero_or_pos (u : ℕ) with h0 | hpos
    · rw [h0] at hL1 ⊢
      norm_num at hL1 ⊢
      have hLd : 1 ≤ L ^ d := one_le_pow₀ hL1
      have a1 : K ≤ K * L ^ d := le_mul_of_one_le_right hK.le hLd
      have a2 : 0 ≤ K * L ^ d := by linarith
      nlinarith
    · obtain ⟨k, hk⟩ : ∃ k, (u : ℕ) = k + 1 := ⟨(u : ℕ) - 1, by omega⟩
      have hkN : k < M + 1 := by have := u.isLt; omega
      obtain ⟨j', hj'⟩ : ∃ j' : Fin (M + 1), j' = ⟨k, hkN⟩ := ⟨_, rfl⟩
      have hj'v : (j' : ℕ) = k := by rw [hj']
      have hjne : u ≠ j' := by
        intro h
        have := congrArg Fin.val h
        omega
      have hj'mem : Fin.castSucc u ∈ ((Function.update (sR M d Φ K hΦ) u t) j').val := by
        rw [Function.update_of_ne (Ne.symm hjne)]
        show Fin.castSucc u ∈ ({Fin.succ j'} : Finset (Fin (M + 1 + 1)))
        rw [Finset.mem_singleton, Fin.ext_iff, Fin.coe_castSucc, Fin.val_succ, hj'v, hk]
      have hL2 := L_ge_two M d Φ K hΦ (Function.update (sR M d Φ K hΦ) u t) u j' hjne _ hu_mem
        hj'mem
      rw [← hLdef, hj'v] at hL2
      rw [max_eq_left (by omega : 1 ≤ (u : ℕ))]
      have hqk : Φ⁻¹ ^ k = Φ * Φ⁻¹ ^ (u : ℕ) := by
        rw [hk, pow_succ, ← mul_assoc, mul_comm Φ, mul_assoc, mul_inv_cancel₀ hΦ.ne', mul_one]
      rw [hqk] at hL2
      have hb : Φ⁻¹ ^ (u : ℕ) * (Φ + 1) ≤ L := by linarith
      have hb' : (Φ⁻¹ ^ (u : ℕ)) ^ d * (Φ + 1) ^ d ≤ L ^ d := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hb d
      have hval : Φ⁻¹ ^ (u : ℕ) * (K ^ (u : ℕ) * ((Φ⁻¹ ^ (u : ℕ)) ^ d * (Φ + 1) ^ d)) =
          (Φ + 1) ^ d := by
        calc Φ⁻¹ ^ (u : ℕ) * (K ^ (u : ℕ) * ((Φ⁻¹ ^ (u : ℕ)) ^ d * (Φ + 1) ^ d))
            = (K * Φ⁻¹ ^ (d + 1)) ^ (u : ℕ) * (Φ + 1) ^ d := by rw [mul_pow, ← wpow]; ring
          _ = (Φ + 1) ^ d := by rw [hKq, one_pow, one_mul]
      have hmono : Φ⁻¹ ^ (u : ℕ) * (K ^ (u : ℕ) * ((Φ⁻¹ ^ (u : ℕ)) ^ d * (Φ + 1) ^ d)) ≤
          Φ⁻¹ ^ (u : ℕ) * (K ^ (u : ℕ) * L ^ d) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hb' (by positivity)
      rw [hval] at hmono
      have := mul_le_mul_of_nonneg_left hmono (by linarith : (0:ℝ) ≤ ρ)
      linarith
  · have hts : t = sR M d Φ K hΦ u := Subtype.ext (Finset.mem_singleton.mp hR)
    rw [hts, Function.update_eq_self]
    have h0 := (pc_pos M d Φ K hΦ hK (sR M d Φ K hΦ) u).le
    nlinarith

end Aux_WCBR_t2

open WeightedCongestionBR Aux_WCBR_t2 in
theorem solution (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n r : ℕ) (G : Game n r), CongestionApproxPNE.IsPolyGame d G ∧
      (∀ u : Fin n, ∀ t ∈ G.strategies u, t.card = 1) ∧
      ∃ s sStar : G.Profile, IsGroupEq G ρ Finset.univ s ∧
        (∀ s' : G.Profile, groupCost G Finset.univ sStar ≤ groupCost G Finset.univ s') ∧
        0 < groupCost G Finset.univ sStar ∧
        genGolden d ρ ^ (d + 1) - ε ≤ groupCost G Finset.univ s / groupCost G Finset.univ sStar := by
  have hρ0 : 0 < ρ := by linarith
  obtain ⟨Φ, hΦ, hroot⟩ := root_exists d ρ hρ0
  rw [genGolden_eq d ρ Φ hΦ hroot]
  obtain ⟨K, hKdef⟩ : ∃ K, K = Φ ^ (d + 1) := ⟨_, rfl⟩
  rw [← hKdef]
  have hK : 0 < K := by rw [hKdef]; positivity
  have hKq : K * Φ⁻¹ ^ (d + 1) = 1 := by
    rw [hKdef, ← mul_pow, mul_inv_cancel₀ hΦ.ne', one_pow]
  have hroot' : ρ * (Φ + 1) ^ d = K := by rw [hKdef]; exact hroot
  have hK1 : 1 ≤ K := by
    rw [← hroot']
    have : 1 ≤ (Φ + 1) ^ d := one_le_pow₀ (by linarith)
    nlinarith
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = Nat.ceil (K ^ 2 / ε) := ⟨_, rfl⟩
  have hMb : K ^ 2 / ε ≤ M := by rw [hM]; exact Nat.le_ceil _
  have hMb' : K ^ 2 ≤ ε * M := by
    rw [div_le_iff₀ hε] at hMb; linarith
  refine ⟨M + 1, M + 1 + 1, LB M d Φ K hΦ, ?_, ?_, ?_⟩
  · intro f
    refine ⟨Polynomial.C (K ^ (max (f : ℕ) 1)) * Polynomial.X ^ d,
      Polynomial.natDegree_C_mul_X_pow_le _ _, fun j => ?_, fun x => ?_⟩
    · rw [Polynomial.coeff_C_mul_X_pow]
      split_ifs
      · positivity
      · exact le_rfl
    · simp [LB]
  · intro u t ht
    have hmem : t ∈ ({{Fin.castSucc u}, {Fin.succ u}} : Finset (Finset (Fin (M + 1 + 1)))) := ht
    rcases Finset.mem_insert.mp hmem with h | h
    · rw [h, Finset.card_singleton]
    · rw [Finset.mem_singleton.mp h, Finset.card_singleton]
  · obtain ⟨sStar, _, hmin⟩ := Finset.exists_min_image Finset.univ
      (fun t => groupCost (LB M d Φ K hΦ) Finset.univ t) ⟨sR M d Φ K hΦ, Finset.mem_univ _⟩
    refine ⟨sR M d Φ K hΦ, sStar, isEq M d Φ K ρ hΦ hK hρ hKq hroot',
      fun s' => hmin s' (Finset.mem_univ _), gc_pos M d Φ K hΦ hK sStar, ?_⟩
    have hopt : groupCost (LB M d Φ K hΦ) Finset.univ sStar ≤
        groupCost (LB M d Φ K hΦ) Finset.univ (sL M d Φ K hΦ) := hmin _ (Finset.mem_univ _)
    have hpos := gc_pos M d Φ K hΦ hK sStar
    rw [gc_sL M d Φ K hΦ hKq] at hopt
    rw [gc_sR M d Φ K hΦ hKq]
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have h1 : ((M : ℝ) + 1) * K / (K + M) ≤
        ((M : ℝ) + 1) * K / groupCost (LB M d Φ K hΦ) Finset.univ sStar :=
      div_le_div_of_nonneg_left (by positivity) hpos hopt
    have h2 : K - ε ≤ ((M : ℝ) + 1) * K / (K + M) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    linarith
