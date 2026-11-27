-- Prove2me | solution 1 for UpperTheory.rowBound_le_Fnum_sum_add_error
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:34:07.294006+00:00
-- url     : https://prove2.me/submissions/f6ef1d67-b955-4bff-b40c-49ea7138d953

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_RowDefs
import Definitions.Def_Formalism_DropLevelBounds_ThBounds
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_AttainsBlockListOfWeightsAlongOrbits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DropLevelsBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MulFlowValLe
import Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_RowBoundLeFnumSumAddError
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Cart_Good_bound
import Theorems.Thm_GlobalTheory_BasicFlow_dropLevelsBasic
import Theorems.Thm_GlobalTheory_FlowScaling_maxFlow_le
import Theorems.Thm_GlobalTheory_FlowScaling_maxFlow_mul
import Theorems.Thm_UpperTheory_attains_blockListOfWeights_along_orbits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped BigOperators
open Classical
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral UpperTheory.G2
namespace UpperTheory.G2.RowBd
open Formalism.L2.FormalSeriesBounds.RF (i0 blockBd chBd Windows)
private theorem exists_ev (d : ℕ) [NeZero d] (hd : Odd d) :
    ∃ ev : ZMod d → ZMod (2 * d), ∀ a, Even (ev a).val ∧ (((ev a).val : ℕ) : ZMod d) = a := by
  have h : ∀ a : ZMod d, ∃ s : ZMod (2 * d), Even s.val ∧ ((s.val : ℕ) : ZMod d) = a := by
    intro a
    have ha := ZMod.val_lt a
    by_cases he : Even a.val
    · refine ⟨(a.val : ℕ), ?_⟩
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
      exact ⟨he, ZMod.natCast_zmod_val a⟩
    · refine ⟨(a.val + d : ℕ), ?_⟩
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
      refine ⟨(Nat.not_even_iff_odd.1 he).add_odd hd, ?_⟩
      rw [Nat.cast_add, ZMod.natCast_self, add_zero, ZMod.natCast_zmod_val]
  choose ev hev using h
  exact ⟨ev, hev⟩
private theorem levels_nonempty (k l : ℕ) (hl : 2 ≤ l) :
    {i : ℕ | Odd i ∧ 3 ≤ i ∧ (k : ℝ) ^ ((3 : ℝ) / 2) < (l : ℝ) ^ i}.Nonempty := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((k : ℝ) ^ ((3 : ℝ) / 2)) hl1
  refine ⟨2 * n + 3, ⟨⟨n + 1, by ring⟩, by omega, ?_⟩⟩
  exact lt_of_lt_of_le hn (pow_le_pow_right₀ hl1.le (by omega))
private theorem thlEq : ∀ k l : ℕ, 1 ≤ k → 2 ≤ l →
    Odd (i0 k l) ∧ 3 ≤ i0 k l ∧ (k : ℝ) ^ ((3 : ℝ) / 2) < (l : ℝ) ^ i0 k l ∧ thl k l = ((l : ℝ) ^ i0 k l)⁻¹ := by
  intro k l hk hl
  have hne := levels_nonempty k l hl
  have hmem : i0 k l ∈ {i : ℕ | Odd i ∧ 3 ≤ i ∧ (k : ℝ) ^ ((3 : ℝ) / 2) < (l : ℝ) ^ i} :=
    Nat.sInf_mem hne
  refine ⟨hmem.1, hmem.2.1, hmem.2.2, ?_⟩
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast (by omega : 1 ≤ l)
  have hgr : IsGreatest {t : ℝ | ∃ i, Odd i ∧ 3 ≤ i ∧ (k : ℝ) ^ ((3 : ℝ) / 2) < (l : ℝ) ^ i ∧
      t = ((l : ℝ) ^ i)⁻¹} ((l : ℝ) ^ i0 k l)⁻¹ := by
    refine ⟨⟨i0 k l, hmem.1, hmem.2.1, hmem.2.2, rfl⟩, ?_⟩
    rintro t ⟨i, hi1, hi2, hi3, rfl⟩
    have hle : i0 k l ≤ i := Nat.sInf_le ⟨hi1, hi2, hi3⟩
    exact inv_anti₀ (pow_pos (by linarith) _) (pow_le_pow_right₀ hl1 hle)
  exact hgr.csSup_eq
private theorem levelBound : ∀ k l : ℕ, 1 ≤ k → 5 ≤ l → ((i0 k l : ℝ) - 1) ≤ 2 + 2 * Real.log k := by
  intro k l hk hl
  obtain ⟨hodd, h3, _, _⟩ := thlEq k l hk (by omega)
  have hlogk : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk)
  by_cases hj : i0 k l = 3
  · rw [hj]
    norm_num
    linarith
  · have h5 : 5 ≤ i0 k l := by
      obtain ⟨t, ht⟩ := hodd
      omega
    have hnot : ¬ (Odd (i0 k l - 2) ∧ 3 ≤ i0 k l - 2 ∧
        (k : ℝ) ^ ((3 : ℝ) / 2) < (l : ℝ) ^ (i0 k l - 2)) := by
      intro h
      have : i0 k l ≤ i0 k l - 2 := Nat.sInf_le h
      omega
    have hodd2 : Odd (i0 k l - 2) := Nat.Odd.sub_even (by omega) hodd even_two
    have hle : (l : ℝ) ^ (i0 k l - 2) ≤ (k : ℝ) ^ ((3 : ℝ) / 2) := by
      by_contra hc
      exact hnot ⟨hodd2, by omega, lt_of_not_ge hc⟩
    have hl0 : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hlog := Real.log_le_log (pow_pos hl0 _) hle
    rw [Real.log_pow, Real.log_rpow hk0] at hlog
    have hlogl : 1 ≤ Real.log l := by
      rw [Real.le_log_iff_exp_le hl0]
      have := Real.exp_one_lt_d9
      have : (5 : ℝ) ≤ l := by exact_mod_cast hl
      linarith
    have hcast : ((i0 k l - 2 : ℕ) : ℝ) = (i0 k l : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [hcast] at hlog
    have hpos : (0 : ℝ) ≤ (i0 k l : ℝ) - 2 := by
      have : (5 : ℝ) ≤ i0 k l := by exact_mod_cast h5
      linarith
    nlinarith
private theorem exists_good {S : ℕ} {G : Set ℕ} (h : Windows S G) {r : ℝ} (hr : 0 ≤ r) :
    ∃ y ∈ G, (y : ℝ) ≤ r ∧ r - y ≤ S := by
  obtain ⟨h0, hw⟩ := h
  set F := (Finset.range (⌊r⌋₊ + 1)).filter (· ∈ G) with hF
  have h0F : 0 ∈ F := by simp [F, h0]
  have hFne : F.Nonempty := ⟨0, h0F⟩
  set y := F.max' hFne
  have hyF : y ∈ F := F.max'_mem hFne
  have hyG : y ∈ G := (Finset.mem_filter.mp hyF).2
  have hyr : y ≤ ⌊r⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hyF).1)
  have hyr' : (y : ℝ) ≤ r := le_trans (Nat.cast_le.mpr hyr) (Nat.floor_le hr)
  obtain ⟨y', hy'G, hy'1, hy'2⟩ := hw (y + 1)
  refine ⟨y, hyG, hyr', ?_⟩
  have hry' : r < y' := by
    by_contra hc
    have hc' : (y' : ℝ) ≤ r := le_of_not_gt hc
    have hy'F : y' ∈ F := by
      simp only [F, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le (Nat.le_floor hc'), hy'G⟩
    have := F.le_max' y' hy'F
    omega
  have : (y' : ℝ) ≤ y + S := by exact_mod_cast (by omega : y' ≤ y + S)
  linarith
section
variable {l d : ℕ} [NeZero d]
private theorem succ_mul_flowVal_le (hl : 1 ≤ l) {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ}
    (hx : IsFlow l d D x) : ((l : ℝ) + 1) * flowVal d x ≤ ∑ a, D a := by
  obtain ⟨hx0, hxD⟩ := hx
  have hsum := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => hxD s
  rw [Finset.sum_add_distrib] at hsum
  have hshift : ∑ s : ZMod d, ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i = flowVal d x := by
    unfold flowVal
    rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ)]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Fintype.sum_equiv (Equiv.subRight (i : ZMod d)) _ _ fun s => rfl
  have hlow : ((l : ℝ)) * flowVal d x ≤ ∑ s : ZMod d, ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i := by
    unfold flowVal
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hodd : Odd i := (Finset.mem_filter.mp hi).2
    have hi1 : 1 ≤ i := hodd.pos
    have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
    have : (l : ℝ) ≤ (l : ℝ) ^ i := by
      calc (l : ℝ) = (l : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (l : ℝ) ^ i := pow_le_pow_right₀ hl1 hi1
    exact mul_le_mul_of_nonneg_right this (hx0 s i)
  rw [hshift] at hsum
  linarith
private theorem rho_mul_le_Fnum (hl : 2 ≤ l) {D : ZMod d → ℝ} (hD : ∀ a, 0 ≤ D a) :
    Formalism.IncomingBounds.rho l * ∑ a, D a ≤ Fnum l d D := by
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hden : (0 : ℝ) < (l : ℝ) ^ 2 - 1 := by nlinarith
  have hsum0 : 0 ≤ ∑ a, D a := Finset.sum_nonneg fun a _ => hD a
  have hmf : maxFlow l d D ≤ (∑ a, D a) / ((l : ℝ) + 1) :=
    GlobalTheory.FlowScaling.maxFlow_le hD fun x hx => by
      have := succ_mul_flowVal_le (by omega) hx
      rw [le_div_iff₀ (by linarith)]
      linarith
  unfold Fnum Formalism.IncomingBounds.rho gam
  have hkey : 1 / ((l : ℝ) ^ 2 - 1) * ∑ a, D a + (∑ a, D a) / ((l : ℝ) + 1) =
      (l : ℝ) / ((l : ℝ) ^ 2 - 1) * ∑ a, D a := by
    field_simp
    ring
  linarith
private theorem Fnum_mul (hl : 2 ≤ l) {D : ZMod d → ℝ} (hD : ∀ a, 0 ≤ D a) (t : ℝ) (ht : 0 ≤ t) :
    Fnum l d (fun a => t * D a) = t * Fnum l d D := by
  unfold Fnum
  rw [GlobalTheory.FlowScaling.maxFlow_mul (by omega) ht hD, ← Finset.mul_sum]
  ring
end
private theorem blockBd_le {l n m i y I S : ℕ} {x : ℝ} (hl : 5 ≤ l) (hn : 1 ≤ n)
    (hi : x ≠ 0 → i < I) (h1 : (n : ℝ) * y ≤ x) (h2 : x - n * y ≤ n * S) :
    blockBd l n m i y ≤ n * gam l * ((l : ℝ) ^ i * y) + n * gam l * y - x +
      (if x ≠ 0 then (n : ℝ) * ((S : ℝ) + Real.logb l n + 1) else 0) +
      2 * (I : ℝ) * m / ((l : ℝ) - 1) * ((l : ℝ) ^ i * y) := by
  have hl1 : (1:ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have hlm : (0:ℝ) < (l:ℝ) - 1 := by linarith
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.logb l n := Real.logb_nonneg hl1 hnR
  have hS0 : (0:ℝ) ≤ S := Nat.cast_nonneg S
  have hnl : 0 ≤ (n:ℝ) * (Real.logb l n + 1) := mul_nonneg (by linarith) (by linarith)
  unfold blockBd bdP
  by_cases hy : y = 0
  · subst hy
    rw [if_pos rfl]
    push_cast at h1 h2 ⊢
    split_ifs with hx
    · nlinarith
    · push_neg at hx
      subst hx
      simp
  · rw [if_neg hy]
    have hy1 : (1:ℝ) ≤ y := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hy
    have hx : x ≠ 0 := by
      intro h
      rw [h] at h1
      nlinarith
    rw [if_pos hx]
    have hiI : (i:ℝ) + 1 ≤ I := by exact_mod_cast Nat.succ_le_of_lt (hi hx)
    have hpow : (1:ℝ) ≤ (l:ℝ) ^ i := one_le_pow₀ hl1.le
    have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
    have hy0 : (0:ℝ) ≤ y := by linarith
    have k1 : ((i:ℝ) + 1) * ((l:ℝ) ^ i + 1) ≤ I * (2 * (l:ℝ) ^ i) :=
      mul_le_mul hiI (by linarith) (by positivity) (by linarith)
    have k2 : ((i:ℝ) + 1) * m * ((l:ℝ) ^ i + 1) * y ≤ 2 * I * m * ((l:ℝ) ^ i * y) := by
      have := mul_le_mul_of_nonneg_right k1 (mul_nonneg hm0 hy0)
      calc ((i:ℝ) + 1) * m * ((l:ℝ) ^ i + 1) * y = ((i:ℝ) + 1) * ((l:ℝ) ^ i + 1) * (m * y) := by ring
        _ ≤ I * (2 * (l:ℝ) ^ i) * (m * y) := this
        _ = 2 * I * m * ((l:ℝ) ^ i * y) := by ring
    have k3 : ((i:ℝ) + 1) * m * ((l:ℝ) ^ i + 1) * y / ((l:ℝ) - 1)
        ≤ 2 * I * m / ((l:ℝ) - 1) * ((l:ℝ) ^ i * y) := by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right k2 hlm.le
    linarith [k3, h2]
private theorem exists_plan : ∀ (l d : ℕ) [NeZero d], 5 ≤ l → ∀ (n m k S : ℕ), 1 ≤ n → 1 ≤ k → ∀ (W : ZMod d → ℕ) (Ws : ZMod d → ℝ) (Good : ZMod d → ℕ → Set ℕ),
  (∀ a, 0 ≤ Ws a ∧ Ws a ≤ W a) → (∀ a, ∀ i ∈ oddLevels d, i < i0 k l → Windows S (Good a i)) →
  ∃ p : Plan l d W, (∀ a i, i0 k l ≤ i → p.y a i = 0) ∧ (∀ a i, p.y a i ≠ 0 → p.y a i ∈ Good a i) ∧
    p.bound n m ≤ Fnum l d (fun a => (n : ℝ) * Ws a) + thl k l * n * (∑ a, Ws a) + n * gam l * (∑ a, ((W a : ℝ) - Ws a)) +
      m * (∑ a, (W a : ℝ)) / ((l : ℝ) - 1) + 2 * (i0 k l : ℝ) * m * (∑ a, Ws a) / ((l : ℝ) - 1) + d * (i0 k l : ℝ) * (n * ((S : ℝ) + Real.logb l n + 1)) := by
  intro l d _ hl n m k S hn hk W Ws Good hWs hG
  obtain ⟨_, hI3, _, hthl⟩ := thlEq k l hk (by omega)
  have hl1 : (1:ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have hlm : (0:ℝ) < (l:ℝ) - 1 := by linarith
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hD0 : 0 ≤ (fun a => (n:ℝ) * Ws a) := by
    intro a
    exact mul_nonneg hn0.le (hWs a).1
  obtain ⟨ys, hflow, hsupp, hcard, hval⟩ :=
    GlobalTheory.BasicFlow.dropLevelsBasic l d (by omega) (fun a => (n:ℝ) * Ws a) hD0 (i0 k l)
  have hys0 : ∀ a i, 0 ≤ ys a i := hflow.1
  have hgood : ∀ a i, ∃ y : ℕ, (i ∈ oddLevels d ∧ i < i0 k l → y ∈ Good a i) ∧
      (n:ℝ) * y ≤ ys a i ∧ ys a i - n * y ≤ n * S ∧
      (¬ (i ∈ oddLevels d ∧ i < i0 k l) → y = 0) := by
    intro a i
    by_cases h : i ∈ oddLevels d ∧ i < i0 k l
    · obtain ⟨y, hyG, hy1, hy2⟩ := exists_good (hG a i h.1 h.2)
        (div_nonneg (hys0 a i) hn0.le : 0 ≤ ys a i / n)
      have e : (n:ℝ) * (ys a i / n) = ys a i := by field_simp
      refine ⟨y, fun _ => hyG, ?_, ?_, fun h' => absurd h h'⟩
      · have := mul_le_mul_of_nonneg_left hy1 hn0.le
        rw [e] at this
        exact this
      · have := mul_le_mul_of_nonneg_left hy2 hn0.le
        rw [mul_sub, e] at this
        exact this
    · have hz : ys a i = 0 := by
        apply hsupp a i
        by_contra hc
        push_neg at hc
        exact h ⟨hc.2, hc.1⟩
      refine ⟨0, fun h' => absurd h' h, by simp [hz], ?_, fun _ => rfl⟩
      simp only [hz, Nat.cast_zero, mul_zero, sub_zero]
      positivity
  choose y hyG hy1 hy2 hy0 using hgood
  have hyodd : ∀ a i, i ∉ oddLevels d → y a i = 0 := fun a i hi => hy0 a i (fun h => hi h.1)
  have hWsa : ∀ a, (∑ i ∈ oddLevels d, (l:ℝ) ^ i * (y a i : ℝ)) +
      (∑ i ∈ oddLevels d, (y (a - (i : ZMod d)) i : ℝ)) ≤ Ws a := by
    intro a
    have hfa := hflow.2 a
    have : (n:ℝ) * ((∑ i ∈ oddLevels d, (l:ℝ) ^ i * (y a i : ℝ)) +
        ∑ i ∈ oddLevels d, (y (a - (i : ZMod d)) i : ℝ)) ≤ n * Ws a := by
      calc _ = (∑ i ∈ oddLevels d, (l:ℝ) ^ i * ((n:ℝ) * y a i)) +
            ∑ i ∈ oddLevels d, (n:ℝ) * (y (a - (i : ZMod d)) i : ℝ) := by
            rw [mul_add, Finset.mul_sum, Finset.mul_sum]
            congr 1
            apply Finset.sum_congr rfl
            intro i _
            ring
        _ ≤ (∑ i ∈ oddLevels d, (l:ℝ) ^ i * ys a i) + ∑ i ∈ oddLevels d, ys (a - (i : ZMod d)) i :=
            add_le_add
              (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hy1 a i) (by positivity))
              (Finset.sum_le_sum fun i _ => hy1 _ i)
        _ ≤ n * Ws a := hfa
    exact le_of_mul_le_mul_left this hn0
  have hsum_le : ∀ a, (∑ i ∈ oddLevels d, l ^ i * y a i) +
      (∑ i ∈ oddLevels d, y (a - (i : ZMod d)) i) ≤ W a := by
    intro a
    have h' := (hWsa a).trans (hWs a).2
    exact_mod_cast h'
  let p : Plan l d W :=
    { y := y
      u := fun a => W a - ((∑ i ∈ oddLevels d, l ^ i * y a i) +
        (∑ i ∈ oddLevels d, y (a - (i : ZMod d)) i))
      supp := hyodd
      bal := by
        intro a
        have := hsum_le a
        omega }
  refine ⟨p, ?_, ?_, ?_⟩
  · intro a i hi
    exact hy0 a i (fun h => absurd h.2 (not_lt.mpr hi))
  · intro a i hne
    by_cases h : i ∈ oddLevels d ∧ i < i0 k l
    · exact hyG a i h
    · exact absurd (hy0 a i h) hne
  ·
    have hlog : 0 ≤ Real.logb l n := Real.logb_nonneg hl1 hnR
    have hB : 0 ≤ (n:ℝ) * ((S:ℝ) + Real.logb l n + 1) := by positivity
    have hblk : ∀ a, ∀ i ∈ oddLevels d, blockBd l n m i (y a i) ≤
        n * gam l * ((l : ℝ) ^ i * y a i) + n * gam l * y a i - ys a i +
        (if ys a i ≠ 0 then (n : ℝ) * ((S : ℝ) + Real.logb l n + 1) else 0) +
        2 * (i0 k l : ℝ) * m / ((l : ℝ) - 1) * ((l : ℝ) ^ i * y a i) := by
      intro a i _
      refine blockBd_le hl hn ?_ (hy1 a i) (hy2 a i)
      intro h
      by_contra hc
      push_neg at hc
      exact h (hsupp a i (Or.inl hc))
    have hsumblk : (∑ a, ∑ i ∈ oddLevels d, blockBd l n m i (y a i)) ≤
        n * gam l * (∑ a, ∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i) +
        n * gam l * (∑ a, ∑ i ∈ oddLevels d, (y a i : ℝ)) -
        (∑ a, ∑ i ∈ oddLevels d, ys a i) +
        (∑ a, ∑ i ∈ oddLevels d,
          (if ys a i ≠ 0 then (n : ℝ) * ((S : ℝ) + Real.logb l n + 1) else 0)) +
        2 * (i0 k l : ℝ) * m / ((l : ℝ) - 1) * (∑ a, ∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i) := by
      calc _ ≤ ∑ a, ∑ i ∈ oddLevels d, (n * gam l * ((l : ℝ) ^ i * y a i) + n * gam l * y a i - ys a i +
            (if ys a i ≠ 0 then (n : ℝ) * ((S : ℝ) + Real.logb l n + 1) else 0) +
            2 * (i0 k l : ℝ) * m / ((l : ℝ) - 1) * ((l : ℝ) ^ i * y a i)) :=
            Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun i hi => hblk a i hi
        _ = _ := by
            simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hC : (∑ a, ∑ i ∈ oddLevels d,
        (if ys a i ≠ 0 then (n : ℝ) * ((S : ℝ) + Real.logb l n + 1) else 0)) ≤
        d * (i0 k l : ℝ) * ((n : ℝ) * ((S : ℝ) + Real.logb l n + 1)) := by
      rw [← Finset.sum_product (f := fun q : ZMod d × ℕ =>
        if ys q.1 q.2 ≠ 0 then (n : ℝ) * ((S : ℝ) + Real.logb l n + 1) else 0)]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have hc : (((Finset.univ ×ˢ oddLevels d).filter (fun q : ZMod d × ℕ => ys q.1 q.2 ≠ 0)).card : ℝ) ≤ d := by
        exact_mod_cast hcard
      have hdI : (d:ℝ) ≤ d * (i0 k l : ℝ) := by
        have : (1:ℝ) ≤ (i0 k l : ℝ) := by exact_mod_cast (by omega : 1 ≤ i0 k l)
        nlinarith [Nat.cast_nonneg (α := ℝ) d]
      calc _ ≤ (d:ℝ) * ((n : ℝ) * ((S : ℝ) + Real.logb l n + 1)) := mul_le_mul_of_nonneg_right hc hB
        _ ≤ _ := mul_le_mul_of_nonneg_right hdI hB
    have hch : (∑ a, chBd l n m (p.u a)) =
        (∑ a, (p.u a : ℝ)) * (n * gam l + m / ((l : ℝ) - 1)) := by
      unfold chBd
      rw [Finset.sum_mul]
    have hreidx : (∑ a, ∑ i ∈ oddLevels d, (y (a - (i : ZMod d)) i : ℝ)) =
        ∑ a, ∑ i ∈ oddLevels d, (y a i : ℝ) := by
      rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ)]
      apply Finset.sum_congr rfl
      intro i _
      exact (Equiv.subRight (i : ZMod d)).sum_comp (fun a => (y a i : ℝ))
    have hbal : (∑ a, (W a : ℝ)) = (∑ a, ∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i) +
        (∑ a, ∑ i ∈ oddLevels d, (y a i : ℝ)) + ∑ a, (p.u a : ℝ) := by
      rw [← hreidx, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      have := p.bal a
      exact_mod_cast this
    have hA : (∑ a, ∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i) ≤ ∑ a, Ws a := by
      apply Finset.sum_le_sum
      intro a _
      have h2 : 0 ≤ ∑ i ∈ oddLevels d, (y (a - (i : ZMod d)) i : ℝ) := by positivity
      linarith [hWsa a]
    have hY : 0 ≤ ∑ a, ∑ i ∈ oddLevels d, (y a i : ℝ) := by positivity
    have hA0 : 0 ≤ ∑ a, ∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i := by positivity
    have hU : (∑ a, (p.u a : ℝ)) ≤ ∑ a, (W a : ℝ) := by linarith
    have hX : maxFlow l d (fun a => (n:ℝ) * Ws a) - thl k l * n * (∑ a, Ws a) ≤
        ∑ a, ∑ i ∈ oddLevels d, ys a i := by
      have e : (∑ a, (fun a => (n:ℝ) * Ws a) a) / (l:ℝ) ^ (i0 k l) = thl k l * n * (∑ a, Ws a) := by
        rw [hthl, ← Finset.mul_sum, div_eq_mul_inv]
        ring
      have := hval
      rw [e] at this
      exact this
    have hcoef : 0 ≤ 2 * (i0 k l : ℝ) * m / ((l : ℝ) - 1) := by positivity
    have hAm : 2 * (i0 k l : ℝ) * m / ((l : ℝ) - 1) * (∑ a, ∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i) ≤
        2 * (i0 k l : ℝ) * m / ((l : ℝ) - 1) * (∑ a, Ws a) := mul_le_mul_of_nonneg_left hA hcoef
    have hmc : 0 ≤ (m : ℝ) / ((l : ℝ) - 1) := by positivity
    have hUm : (m : ℝ) / ((l : ℝ) - 1) * (∑ a, (p.u a : ℝ)) ≤ (m : ℝ) / ((l : ℝ) - 1) * ∑ a, (W a : ℝ) :=
      mul_le_mul_of_nonneg_left hU hmc
    have hF : Fnum l d (fun a => (n : ℝ) * Ws a) =
        gam l * ((n:ℝ) * ∑ a, Ws a) - maxFlow l d (fun a => (n:ℝ) * Ws a) := by
      unfold Fnum
      rw [← Finset.mul_sum]
    have hsub : (∑ a, ((W a : ℝ) - Ws a)) = (∑ a, (W a : ℝ)) - ∑ a, Ws a := Finset.sum_sub_distrib ..
    show (∑ a, ∑ i ∈ oddLevels d, blockBd l n m i (y a i)) + ∑ a, chBd l n m (p.u a) ≤ _
    rw [hch, hF, hsub]
    have e1 : 2 * (i0 k l : ℝ) * m * (∑ a, Ws a) / ((l : ℝ) - 1) =
        2 * (i0 k l : ℝ) * m / ((l : ℝ) - 1) * (∑ a, Ws a) := by ring
    have e2 : (m : ℝ) * (∑ a, (W a : ℝ)) / ((l : ℝ) - 1) =
        (m : ℝ) / ((l : ℝ) - 1) * ∑ a, (W a : ℝ) := by ring
    rw [e1, e2]
    have hbal' : (n:ℝ) * gam l * (∑ a, (W a : ℝ)) = n * gam l * (∑ a, ∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i) +
        n * gam l * (∑ a, ∑ i ∈ oddLevels d, (y a i : ℝ)) + n * gam l * ∑ a, (p.u a : ℝ) := by
      rw [hbal]
      ring
    linarith [hsumblk, hC, hX, hAm, hUm, hbal']
private theorem sum_reps (P : RF.Par) (Z : Finset P.Pl) (hZ : RF.IsReps P Z) (g : P.Pl → ℝ) :
    ∑ z ∈ Z, ∑ a : ZMod P.d, g (P.pos z a.val) = ∑ z, g z := by
  rw [← Finset.sum_product']
  refine Finset.sum_bij (fun p _ => P.pos p.1 p.2.val) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
  · intro p hp q hq hpq
    simp only [Finset.mem_product] at hp hq
    obtain ⟨_, _, huniq⟩ := hZ (P.pos q.1 q.2.val)
    exact (huniq p ⟨hp.1, hpq⟩).trans (huniq q ⟨hq.1, rfl⟩).symm
  · intro z _
    obtain ⟨p, ⟨hp1, hp2⟩, _⟩ := hZ z
    exact ⟨p, Finset.mem_product.mpr ⟨hp1, Finset.mem_univ _⟩, hp2⟩
private theorem one_le_log {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith
private theorem logb_le {l : ℕ} (hl : 5 ≤ l) {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) : Real.logb l x ≤ Real.log y := by
  have h5 : (5 : ℝ) ≤ l := by exact_mod_cast hl
  have h1 : 1 ≤ Real.log l := one_le_log (by linarith)
  have h2 : 0 ≤ Real.log x := Real.log_nonneg hx
  have h3 : Real.log x ≤ Real.log y := Real.log_le_log (by linarith) hxy
  unfold Real.logb
  exact (div_le_self h2 h1).trans h3
private theorem mono_resι_var (l n : ℕ) {i j : ℕ} (h : i ≤ j) : S0 l i n ≤ S0 l j n := by
  unfold S0
  apply Nat.ceil_mono
  have : (i : ℝ) ≤ j := by exact_mod_cast h
  gcongr
private theorem add_le (l k i : ℕ) (hl : 5 ≤ l) (hk : 4 ≤ k) (hi : (i : ℝ) ≤ 5 * Real.log k) :
    (S0 l i (k - 1) : ℝ) + Real.logb l ((k - 1 : ℕ) : ℝ) + 1 ≤ 707 * ((k : ℝ) - 1) ^ 2 * Real.log k := by
  have hk1 : 1 ≤ k := by omega
  have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub hk1, Nat.cast_one]
  have hk4 : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog1 : 1 ≤ Real.log k := one_le_log (by linarith)
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (show 1 < l by omega)
  have hb1 : Real.logb l (((k - 1 : ℕ) : ℝ) + 1) ≤ Real.log k :=
    logb_le hl (by rw [hcast]; linarith) (by rw [hcast]; linarith)
  have hb2 : Real.logb l ((k - 1 : ℕ) : ℝ) ≤ Real.log k :=
    logb_le hl (by rw [hcast]; linarith) (by rw [hcast]; linarith)
  have hlogb0 : 0 ≤ Real.logb l (((k - 1 : ℕ) : ℝ) + 1) := by
    apply Real.logb_nonneg hl1
    have : (0 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  have hS : (S0 l i (k - 1) : ℝ) < 64 * ((k - 1 : ℕ) : ℝ) ^ 2 *
      ((i : ℝ) + 3 + 3 * Real.logb l (((k - 1 : ℕ) : ℝ) + 1)) + 1 := by
    unfold S0
    apply Nat.ceil_lt_add_one
    exact mul_nonneg (by positivity) (by linarith)
  rw [hcast] at hS hb1 hb2 ⊢
  have hn3 : (3 : ℝ) ≤ (k : ℝ) - 1 := by linarith
  have hn2 : (9 : ℝ) ≤ ((k : ℝ) - 1) ^ 2 := by nlinarith
  have e1 : 64 * ((k : ℝ) - 1) ^ 2 * ((i : ℝ) + 3 + 3 * Real.logb l ((k : ℝ) - 1 + 1)) ≤
      64 * ((k : ℝ) - 1) ^ 2 * (11 * Real.log k) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have e2 : 9 * Real.log k ≤ ((k : ℝ) - 1) ^ 2 * Real.log k :=
    mul_le_mul_of_nonneg_right hn2 (by linarith)
  linarith
private theorem inv_le {l : ℕ} (hl : 5 ≤ l) : ((l : ℝ) - 1)⁻¹ ≤ 2 * (l : ℝ)⁻¹ ∧ gam l ≤ 2 * (l : ℝ)⁻¹ ∧ 0 ≤ gam l ∧ 0 ≤ rho l := by
  have h5 : (5 : ℝ) ≤ l := by exact_mod_cast hl
  have h1 : 0 < (l : ℝ) ^ 2 - 1 := by nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by linarith) (by linarith)]; linarith
  · unfold gam
    rw [← div_eq_mul_inv, div_le_div_iff₀ h1 (by linarith)]; nlinarith
  · unfold gam; positivity
  · unfold rho; positivity
set_option maxHeartbeats 800000 in

private theorem orbit (l d : ℕ) [NeZero d] (hl : 5 ≤ l) (m k : ℕ) (hmk : m + 3 ≤ k) (hm : 1 ≤ m) (W : ZMod d → ℕ) (w : ZMod d → ℝ)
    (T θ E : ℝ) (hT : 1 ≤ T) (hw : ∀ a, 0 < w a) (hlo : ∀ a, (1 - θ) * w a ≤ T * W a) (hhi : ∀ a, T * W a ≤ w a + E)
    (hE : 0 ≤ E) (hθ : 0 ≤ θ ∧ θ ≤ 1) (hθm : ((k : ℝ) - 1) * θ ≤ 5 * m) (Good : ZMod d → ℕ → Set ℕ)
    (hG : ∀ a, ∀ i ∈ oddLevels d, i < i0 k l → Windows (S0 l (i0 k l) (k - 1)) (Good a i)) :
    ∃ p : Plan l d W, (∀ a i, i0 k l ≤ i → p.y a i = 0) ∧ (∀ a i, p.y a i ≠ 0 → p.y a i ∈ Good a i) ∧
      T * p.bound (k - 1) m ≤ Fnum l d (fun a => ((k : ℝ) - 1) * w a) +
        (32 * Real.log k * m / l + k * thl k l) * (∑ a, w a) +
        d * (4 * k * E / l + 3535 * T * ((k : ℝ) - 1) ^ 3 * Real.log k ^ 2) := by
  have hk1 : 1 ≤ k := by omega
  have hl2 : 2 ≤ l := by omega
  have hkR : (4 : ℝ) ≤ k := by exact_mod_cast (show 4 ≤ k by omega)
  have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub hk1, Nat.cast_one]
  have hT0 : 0 < T := by linarith
  set Ws : ZMod d → ℝ := fun a => (1 - θ) * w a / T with hWsdef
  have hTWs : ∀ a, T * Ws a = (1 - θ) * w a := by
    intro a
    simp only [Ws]
    field_simp
  have hWs : ∀ a, 0 ≤ Ws a ∧ Ws a ≤ W a := by
    intro a
    refine ⟨div_nonneg (mul_nonneg (by linarith [hθ.2]) (hw a).le) hT0.le, ?_⟩
    rw [div_le_iff₀ hT0]
    linarith [hlo a]
  obtain ⟨p, hp1, hp2, hpb⟩ := exists_plan l d hl (k - 1) m k (S0 l (i0 k l) (k - 1)) (by omega) hk1
    W Ws Good hWs hG
  refine ⟨p, hp1, hp2, ?_⟩
  rw [← hcast] at hθm ⊢
  set nR : ℝ := ((k - 1 : ℕ) : ℝ) with hnR
  have hnR0 : 3 ≤ nR := by rw [hcast]; linarith
  have hnRk : nR ≤ k := by rw [hcast]; linarith
  have hL : 1 ≤ Real.log k := one_le_log (by linarith)
  obtain ⟨hinv, hg2, hg0, hrho⟩ := inv_le hl
  have hthl : 0 ≤ thl k l := by rw [(thlEq k l hk1 hl2).2.2.2]; positivity
  have hi0 : (i0 k l : ℝ) ≤ 5 * Real.log k := by have := levelBound k l hk1 hl; linarith
  have hl5 : (5 : ℝ) ≤ l := by exact_mod_cast hl
  have hq0 : 0 ≤ (l : ℝ)⁻¹ := inv_nonneg.mpr (by linarith)
  have hl1inv0 : 0 ≤ ((l : ℝ) - 1)⁻¹ := inv_nonneg.mpr (by linarith)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hmk : (m : ℝ) ≤ k := by exact_mod_cast (show m ≤ k by omega)
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hdE : 0 ≤ (d : ℝ) * E := mul_nonneg hd0 hE
  have hcard : ∑ _a : ZMod d, E = (d : ℝ) * E := by
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  have A1 : T * ∑ a, Ws a = (1 - θ) * ∑ a, w a := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun a _ => hTWs a)
  have A2 : T * ∑ a, ((W a : ℝ) - Ws a) ≤ θ * ∑ a, w a + d * E := by
    rw [Finset.mul_sum, Finset.mul_sum, ← hcard, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a _
    rw [mul_sub, hTWs a]
    linarith [hhi a]
  have A3 : T * ∑ a, (W a : ℝ) ≤ ∑ a, w a + d * E := by
    rw [Finset.mul_sum, ← hcard, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun a _ => hhi a)
  have hSw0 : 0 ≤ ∑ a, w a := Finset.sum_nonneg (fun a _ => (hw a).le)
  set Sw := ∑ a, w a with hSw
  have hDw : ∀ a, 0 ≤ nR * w a := fun a => mul_nonneg (by linarith) (hw a).le
  have hDWs : ∀ a, 0 ≤ nR * Ws a := fun a => mul_nonneg (by linarith) (hWs a).1
  have e1 := Fnum_mul hl2 (D := fun a => nR * Ws a) hDWs T hT0.le
  have e2 := Fnum_mul hl2 (D := fun a => nR * w a) hDw (1 - θ) (by linarith [hθ.2])
  have hF : T * Fnum l d (fun a => nR * Ws a) = (1 - θ) * Fnum l d (fun a => nR * w a) := by
    rw [← e1, ← e2]
    congr 1
    funext a
    show T * (nR * Ws a) = (1 - θ) * (nR * w a)
    linear_combination nR * hTWs a
  have hFn0 : 0 ≤ Fnum l d (fun a => nR * w a) :=
    le_trans (mul_nonneg hrho (Finset.sum_nonneg (fun a _ => hDw a))) (rho_mul_le_Fnum hl2 hDw)
  have t1 : T * Fnum l d (fun a => nR * Ws a) ≤ Fnum l d (fun a => nR * w a) := by
    rw [hF]
    have := mul_nonneg hθ.1 hFn0
    linarith
  have t2 : T * (thl k l * nR * ∑ a, Ws a) ≤ k * thl k l * Sw := by
    have h1 : nR * (1 - θ) ≤ k := by
      have := mul_nonneg (show (0:ℝ) ≤ nR by linarith) hθ.1
      linarith
    calc T * (thl k l * nR * ∑ a, Ws a) = thl k l * (nR * (1 - θ)) * Sw := by
          rw [show T * (thl k l * nR * ∑ a, Ws a) = thl k l * nR * (T * ∑ a, Ws a) by ring, A1]
          ring
      _ ≤ thl k l * k * Sw :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hthl) hSw0
      _ = k * thl k l * Sw := by ring
  have t3 : T * (nR * gam l * ∑ a, ((W a : ℝ) - Ws a)) ≤
      10 * (m * (l : ℝ)⁻¹ * Sw) + 2 * (k * (l : ℝ)⁻¹ * (d * E)) := by
    have hnθ : 0 ≤ nR * θ := mul_nonneg (by linarith) hθ.1
    calc T * (nR * gam l * ∑ a, ((W a : ℝ) - Ws a))
        = nR * gam l * (T * ∑ a, ((W a : ℝ) - Ws a)) := by ring
      _ ≤ nR * gam l * (θ * Sw + d * E) :=
          mul_le_mul_of_nonneg_left A2 (mul_nonneg (by linarith) hg0)
      _ = gam l * (nR * θ) * Sw + gam l * nR * (d * E) := by ring
      _ ≤ (2 * (l : ℝ)⁻¹) * (5 * m) * Sw + (2 * (l : ℝ)⁻¹) * k * (d * E) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right (mul_le_mul hg2 hθm hnθ (by positivity)) hSw0
          · exact mul_le_mul_of_nonneg_right (mul_le_mul hg2 hnRk (by linarith) (by positivity)) hdE
      _ = _ := by ring
  have t4 : T * (m * (∑ a, (W a : ℝ)) / ((l : ℝ) - 1)) ≤
      2 * (m * (l : ℝ)⁻¹ * Sw) + 2 * (k * (l : ℝ)⁻¹ * (d * E)) := by
    have hmq := mul_le_mul_of_nonneg_right hmk (mul_nonneg hq0 hdE)
    calc T * (m * (∑ a, (W a : ℝ)) / ((l : ℝ) - 1))
        = m * (T * ∑ a, (W a : ℝ)) * ((l : ℝ) - 1)⁻¹ := by ring
      _ ≤ m * (Sw + d * E) * (2 * (l : ℝ)⁻¹) :=
          mul_le_mul (mul_le_mul_of_nonneg_left A3 hm0) hinv hl1inv0
            (mul_nonneg hm0 (add_nonneg hSw0 hdE))
      _ ≤ _ := by linarith
  have t5 : T * (2 * (i0 k l : ℝ) * m * (∑ a, Ws a) / ((l : ℝ) - 1)) ≤
      20 * (Real.log k * (m * (l : ℝ)⁻¹ * Sw)) := by
    have h1 : (1 - θ) * Sw ≤ Sw := by
      have := mul_nonneg hθ.1 hSw0
      linarith
    have hX : 0 ≤ 2 * (i0 k l : ℝ) * m := by positivity
    have h2 : 2 * (i0 k l : ℝ) * m * Sw ≤ 2 * (5 * Real.log k) * m * Sw := by
      have := mul_le_mul_of_nonneg_right hi0 (mul_nonneg hm0 hSw0)
      linarith
    calc T * (2 * (i0 k l : ℝ) * m * (∑ a, Ws a) / ((l : ℝ) - 1))
        = 2 * (i0 k l : ℝ) * m * (T * ∑ a, Ws a) * ((l : ℝ) - 1)⁻¹ := by ring
      _ = 2 * (i0 k l : ℝ) * m * ((1 - θ) * Sw) * ((l : ℝ) - 1)⁻¹ := by rw [A1]
      _ ≤ 2 * (i0 k l : ℝ) * m * Sw * (2 * (l : ℝ)⁻¹) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 hX) hinv hl1inv0 (mul_nonneg hX hSw0)
      _ ≤ 2 * (5 * Real.log k) * m * Sw * (2 * (l : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = _ := by ring
  have hadd : (S0 l (i0 k l) (k - 1) : ℝ) + Real.logb l nR + 1 ≤ 707 * nR ^ 2 * Real.log k := by
    have := add_le l k (i0 k l) hl (by omega) hi0
    rw [← hcast] at this
    exact this
  have hZ : 0 ≤ (S0 l (i0 k l) (k - 1) : ℝ) + Real.logb l nR + 1 := by
    have : 0 ≤ Real.logb l nR :=
      Real.logb_nonneg (by exact_mod_cast (show 1 < l by omega)) (by linarith)
    have : (0 : ℝ) ≤ (S0 l (i0 k l) (k - 1) : ℝ) := Nat.cast_nonneg _
    linarith
  have t6 : T * ((d : ℝ) * (i0 k l : ℝ) * (nR * ((S0 l (i0 k l) (k - 1) : ℝ) + Real.logb l nR + 1))) ≤
      d * (3535 * T * nR ^ 3 * Real.log k ^ 2) := by
    calc T * ((d : ℝ) * (i0 k l : ℝ) * (nR * ((S0 l (i0 k l) (k - 1) : ℝ) + Real.logb l nR + 1)))
        = (d : ℝ) * T * ((i0 k l : ℝ) * (nR * ((S0 l (i0 k l) (k - 1) : ℝ) + Real.logb l nR + 1))) := by
          ring
      _ ≤ (d : ℝ) * T * ((5 * Real.log k) * (nR * (707 * nR ^ 2 * Real.log k))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hi0 (mul_le_mul_of_nonneg_left hadd (by linarith))
              (mul_nonneg (by linarith) hZ) (by linarith))
            (mul_nonneg hd0 hT0.le)
      _ = _ := by ring
  have hpb' := mul_le_mul_of_nonneg_left hpb hT0.le
  have hmq : m * (l : ℝ)⁻¹ * Sw ≤ Real.log k * (m * (l : ℝ)⁻¹ * Sw) :=
    le_mul_of_one_le_left (by positivity) hL
  simp only [div_eq_mul_inv] at hpb' t4 t5 ⊢
  linarith only [t1, t2, t3, t4, t5, t6, hpb', hmq]
end UpperTheory.G2.RowBd
end

set_option autoImplicit false
open scoped BigOperators
open Classical
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral UpperTheory.G2
open UpperTheory.G2.RowBd
namespace UpperTheory
theorem _root_.solution :
    RF.BiSupply → RF.CHSupply → RF.MONSupply → ∀ C1 : ℝ, 0 ≤ C1 → ∃ Cc : ℝ, 0 < Cc ∧ ∀ (P : RF.Par) (l : ℕ),
    Fintype.card P.Pl = P.f → 1 ≤ P.m → P.m + 3 ≤ P.k → P.r = P.k - 1 + P.m → 0 ≤ P.SE → l.Prime → 5 ≤ l → ∀ Pk : PkgCs P l C1,
    Pk.T * Pk.ν ≤ (∑ z ∈ Pk.Z, Fnum l P.d fun s => ((P.k : ℝ) - 1) * RF.alongOrb P z P.w s) +
      Cc * (Real.log P.k * P.m * (∑ z, P.w z) / l + P.f * P.k * P.SE / l + P.k * thl P.k l * (∑ z, P.w z) +
        Pk.T * P.f * ((P.k : ℝ) - 1) ^ 3 * Real.log P.k ^ 2) := by
  intro hBi hCH hMON C1 hC1
  refine ⟨3567 + 6 * C1, by linarith, ?_⟩
  intro P l hcard hm hmk hr hSE hlp hl Pk
  haveI := P.nz
  obtain ⟨ev, hev⟩ := exists_ev P.d Pk.odd
  have hdeg := Pk.deg
  have hk1 : 1 ≤ P.k - 1 := by omega
  have hex : ∀ o : ↥Pk.Z, ∃ p : Plan l P.d (RF.alongOrb P o Pk.W),
      (∀ a i, RF.i0 P.k l ≤ i → p.y a i = 0) ∧
      (∀ a i, p.y a i ≠ 0 → p.y a i ∈ {y : ℕ | RF.GlobalTheory.Attains (Pk.R.X o) (Pk.R.F o)
        (RF.GlobalTheory.bi 0 (ev a) i y) (RF.blockBd l (P.k - 1) P.m i y)}) ∧
      Pk.T * p.bound (P.k - 1) P.m ≤ Fnum l P.d (fun a => ((P.k : ℝ) - 1) * RF.alongOrb P o P.w a) +
        (32 * Real.log P.k * P.m / l + P.k * thl P.k l) * (∑ a, RF.alongOrb P o P.w a) +
        P.d * (4 * P.k * (C1 * P.SE) / l + 3535 * Pk.T * ((P.k : ℝ) - 1) ^ 3 * Real.log P.k ^ 2) := by
    intro o
    refine orbit l P.d hl P.m P.k hmk hm (RF.alongOrb P o Pk.W) (RF.alongOrb P o P.w) Pk.T Pk.θ0
      (C1 * P.SE) hdeg.T_one (fun a => hdeg.w_pos _) (fun a => hdeg.TW_lo _) (fun a => hdeg.TW_hi _)
      (mul_nonneg hC1 hSE) hdeg.th_rng hdeg.th_m _ ?_
    intro a i hi hlt
    have hiodd := Finset.mem_filter.mp hi
    have hid : i < P.d := Finset.mem_range.mp hiodd.1
    have halt := Pk.R.alt o
    have hW := hBi Pk.R.C Pk.R.V (2 * P.d) (Pk.R.I o) (Pk.R.J o) (Pk.R.X o) (Pk.R.F o) halt
      (by rw [Pk.R.hVl]; exact hl) (by rw [(Pk.R.hn o).1]; exact hk1) 0 (ev a)
      ((halt.2 (ev a)).mpr (hev a).1) i hiodd.2 (by omega)
    rw [Pk.R.hVl, (Pk.R.hn o).1, (Pk.R.hn o).2] at hW
    refine ⟨hW.1, fun Y0 => ?_⟩
    obtain ⟨y, hy, h1, h2⟩ := hW.2 Y0
    have hmono := mono_resι_var l (P.k - 1) hlt.le
    exact ⟨y, hy, h1, by omega⟩
  choose pl hpl using hex
  let y : P.Pl → ZMod P.d → ℕ → ℕ := fun z => if h : z ∈ Pk.Z then (pl ⟨z, h⟩).y else fun _ _ => 0
  let u : P.Pl → ZMod P.d → ℕ := fun z => if h : z ∈ Pk.Z then (pl ⟨z, h⟩).u else fun _ => 0
  have hν := UpperTheory.attains_blockListOfWeights_along_orbits hCH hMON P l C1 hcard hm hmk hr hl Pk y u ev hev
    (by
      intro z hz a
      simp only [y, u, dif_pos hz]
      exact (pl ⟨z, hz⟩).bal a)
    (by
      intro z hz a i hi
      simp only [y, dif_pos hz]
      exact (hpl ⟨z, hz⟩).1 a i hi)
    (by
      intro o a i _ hne
      simp only [y, dif_pos o.2, Subtype.coe_eta] at hne ⊢
      exact (hpl o).2.1 a i hne)
  have hsum : ∑ z ∈ Pk.Z, ((∑ a, ∑ i ∈ oddLevels P.d, RF.blockBd l (P.k - 1) P.m i (y z a i)) +
      ∑ a, RF.chBd l (P.k - 1) P.m (u z a)) = ∑ o : ↥Pk.Z, (pl o).bound (P.k - 1) P.m := by
    rw [← Finset.sum_coe_sort Pk.Z]
    refine Finset.sum_congr rfl fun o _ => ?_
    simp only [y, u, dif_pos o.2, Subtype.coe_eta, Plan.bound]
  have hT0 : 0 < Pk.T := by linarith [hdeg.T_one]
  have hbound : Pk.T * Pk.ν ≤ ∑ o : ↥Pk.Z, Pk.T * (pl o).bound (P.k - 1) P.m +
      Pk.T * Pk.rest / ((l : ℝ) - 1) := by
    have := mul_le_mul_of_nonneg_left hν hT0.le
    rw [hsum, mul_add, Finset.mul_sum] at this
    rw [mul_div_assoc]
    exact this
  have hle := Finset.sum_le_sum (fun o (_ : o ∈ (Finset.univ : Finset ↥Pk.Z)) => (hpl o).2.2)
  set A : ℝ := 32 * Real.log P.k * P.m / l + P.k * thl P.k l with hA
  set X : ℝ := 4 * P.k * (C1 * P.SE) / l + 3535 * Pk.T * ((P.k : ℝ) - 1) ^ 3 * Real.log P.k ^ 2 with hX
  have hreps := sum_reps P Pk.Z Pk.hZ P.w
  have hcnt := sum_reps P Pk.Z Pk.hZ (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one] at hcnt
  have hZd : ∑ o : ↥Pk.Z, ((P.d : ℝ) * X) = P.f * X := by
    rw [Finset.sum_coe_sort Pk.Z (fun _ => (P.d : ℝ) * X), ← Finset.sum_mul]
    congr 1
    rw [← hcard]
    simpa using hcnt
  have hRsum : ∑ o : ↥Pk.Z, (Fnum l P.d (fun a => ((P.k : ℝ) - 1) * RF.alongOrb P o P.w a) +
      A * (∑ a, RF.alongOrb P o P.w a) + P.d * X) =
      (∑ z ∈ Pk.Z, Fnum l P.d (fun s => ((P.k : ℝ) - 1) * RF.alongOrb P z P.w s)) +
        A * (∑ z, P.w z) + P.f * X := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hZd, ← Finset.mul_sum,
      Finset.sum_coe_sort Pk.Z (fun z => Fnum l P.d (fun s => ((P.k : ℝ) - 1) * RF.alongOrb P z P.w s)),
      Finset.sum_coe_sort Pk.Z (fun z => ∑ a, RF.alongOrb P z P.w a)]
    simp only [RF.alongOrb] at hreps ⊢
    rw [hreps]
  rw [hRsum] at hle
  have hl0 : (0 : ℝ) < (l : ℝ) - 1 := by
    have : (5 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have hrest : Pk.T * Pk.rest / ((l : ℝ) - 1) ≤ C1 * (P.f * P.k * P.SE) * (2 * (l : ℝ)⁻¹) := by
    rw [div_eq_mul_inv]
    have hinv := (inv_le hl).1
    have hCn : 0 ≤ C1 * (P.f * P.k * P.SE) := by positivity
    calc Pk.T * Pk.rest * ((l : ℝ) - 1)⁻¹ ≤ C1 * (P.f * P.k * P.SE) * ((l : ℝ) - 1)⁻¹ :=
          mul_le_mul_of_nonneg_right hdeg.rest_le (inv_nonneg.mpr hl0.le)
      _ ≤ _ := mul_le_mul_of_nonneg_left hinv hCn
  have hk4 : (1 : ℝ) ≤ P.k := by exact_mod_cast (show 1 ≤ P.k by omega)
  have hlog : 0 ≤ Real.log P.k := Real.log_nonneg hk4
  have hw : 0 ≤ ∑ z, P.w z := Finset.sum_nonneg fun z _ => (hdeg.w_pos z).le
  have hthl : 0 ≤ thl P.k l := by
    rw [(thlEq P.k l (by omega) (by omega)).2.2.2]
    positivity
  have ha : 0 ≤ Real.log P.k * P.m * (∑ z, P.w z) / l := by positivity
  have hb : 0 ≤ (P.f : ℝ) * P.k * P.SE / l := by positivity
  have hc : 0 ≤ (P.k : ℝ) * thl P.k l * (∑ z, P.w z) := by positivity
  have hk1r : (0 : ℝ) ≤ (P.k : ℝ) - 1 := by linarith
  have he : 0 ≤ Pk.T * P.f * ((P.k : ℝ) - 1) ^ 3 * Real.log P.k ^ 2 := by positivity
  have hid : A * (∑ z, P.w z) + P.f * X + C1 * (P.f * P.k * P.SE) * (2 * (l : ℝ)⁻¹) =
      32 * (Real.log P.k * P.m * (∑ z, P.w z) / l) + 6 * C1 * ((P.f : ℝ) * P.k * P.SE / l) +
        (P.k : ℝ) * thl P.k l * (∑ z, P.w z) + 3535 * (Pk.T * P.f * ((P.k : ℝ) - 1) ^ 3 * Real.log P.k ^ 2) := by
    rw [hA, hX]
    ring
  nlinarith [mul_nonneg hC1 ha, mul_nonneg hC1 hc, mul_nonneg hC1 he, mul_nonneg hC1 hb]
end UpperTheory
