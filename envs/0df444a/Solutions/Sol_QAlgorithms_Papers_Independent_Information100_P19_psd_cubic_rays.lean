-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P19.psd_cubic_rays
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T13:44:13.065039+00:00
-- url     : https://prove2.me/submissions/67367055-4162-4fdf-acdb-7872584d6d15

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section
open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder
open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

theorem PCR_parts (p : Part 3) :
    p = ⟨[3], by decide⟩ ∨ p = ⟨[2,1], by decide⟩ ∨ p = ⟨[1,1,1], by decide⟩ := by
  obtain ⟨l, h1, h2, h3⟩ := p
  match l, h1, h2, h3 with
  | [], _, _, h3 => simp at h3
  | [a], _, _, h3 => left; simp at h3; subst h3; rfl
  | [a, b], h1, h2, h3 =>
    right; left
    simp at h1 h2 h3
    have : a = 2 := by omega
    have : b = 1 := by omega
    subst a; subst b; rfl
  | [a, b, c], h1, h2, h3 =>
    right; right
    simp at h1 h2 h3
    have : a = 1 := by omega
    have : b = 1 := by omega
    have : c = 1 := by omega
    subst a; subst b; subst c; rfl
  | a :: b :: c :: e :: t, _, h2, h3 =>
    exfalso
    simp at h2 h3
    omega

theorem PCR_smA {d : ℕ} (x : Fin d → ℝ) :
    spectralMoments x (⟨[3], by decide⟩ : Part 3) = ∑ i, x i ^ 3 := by
  simp [spectralMoments]

theorem PCR_smB {d : ℕ} (x : Fin d → ℝ) :
    spectralMoments x (⟨[2,1], by decide⟩ : Part 3) = (∑ i, x i ^ 2) * ∑ i, x i := by
  simp [spectralMoments]

theorem PCR_smC {d : ℕ} (x : Fin d → ℝ) :
    spectralMoments x (⟨[1,1,1], by decide⟩ : Part 3) = (∑ i, x i) ^ 3 := by
  simp [spectralMoments]; ring

/-- two-level bound -/
theorem PCR_two (m k : ℕ) (hm : 1 ≤ m) (w u : ℝ) (hu : 0 ≤ u) (huw : u ≤ w)
    (hs : (m:ℝ) * w + u = 1) :
    0 ≤ 1 - (2*(k:ℝ)+1) * ((m:ℝ) * w^2 + u^2) + (k:ℝ)*(k+1) * ((m:ℝ) * w^3 + u^3) := by
  have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hmk : 0 ≤ ((m:ℝ) - k) * ((m:ℝ) - k - 1) := by
    rcases le_or_gt m k with h | h
    · have : (m:ℝ) ≤ k := by exact_mod_cast h
      nlinarith
    · have : (k:ℝ) + 1 ≤ m := by exact_mod_cast h
      nlinarith
  have hmk2 : 0 ≤ ((m:ℝ) + 1 - k) * ((m:ℝ) - k) := by
    rcases le_or_gt (m+1) k with h | h
    · have : (m:ℝ) + 1 ≤ k := by exact_mod_cast h
      nlinarith
    · have : (k:ℝ) ≤ m := by exact_mod_cast (by omega : k ≤ m)
      nlinarith
  have hu' : u = 1 - m * w := by linarith
  subst hu'
  set Y := (m:ℝ) * w ^ 2 + (1 - m * w) ^ 2 with hY
  have hw1 : 0 ≤ ((m:ℝ)+1) * w - 1 := by linarith
  have hY1 : 0 ≤ ((m:ℝ)+1) * Y - 1 := by
    have : ((m:ℝ)+1) * Y - 1 = m * (((m:ℝ)+1) * w - 1)^2 := by rw [hY]; ring
    rw [this]; positivity
  have hY2 : 0 ≤ 1 - (m:ℝ) * Y := by
    have : 1 - (m:ℝ) * Y = (1 - m * w) * (m * (m+1) * w - (m - 1)) := by rw [hY]; ring
    rw [this]
    apply mul_nonneg hu
    nlinarith
  have hkey : (m:ℝ) * (m+1) * (1 - (2*(k:ℝ)+1) * Y + (k:ℝ)*(k+1) * ((m:ℝ) * w^3 + (1 - m*w)^3))
      = k*(k+1) * (m * (m-1) * ((m+1)*w-1)^2 * (1 - m*w))
        + ((m+1)*Y - 1) * ((m+1) * ((m - k) * (m - k - 1)))
        + (1 - m*Y) * (m * ((m+1-k)*(m-k))) := by
    rw [hY]; ring
  have hk0 : (0:ℝ) ≤ k := by positivity
  have hpos : 0 ≤ k*(k+1) * (m * (m-1) * ((m+1)*w-1)^2 * (1 - m*w))
        + ((m+1)*Y - 1) * ((m+1) * ((m - k) * (m - k - 1)))
        + (1 - m*Y) * (m * ((m+1-k)*(m-k))) := by
    have h1 : (0:ℝ) ≤ (m:ℝ) - 1 := by linarith
    apply add_nonneg; apply add_nonneg
    · apply mul_nonneg (by positivity)
      apply mul_nonneg (mul_nonneg (mul_nonneg (by linarith) h1) (sq_nonneg _)) hu
    · apply mul_nonneg hY1 (mul_nonneg (by linarith) hmk)
    · apply mul_nonneg hY2 (mul_nonneg (by linarith) hmk2)
  rw [← hkey] at hpos
  have : (0:ℝ) < (m:ℝ) * (m+1) := by positivity
  exact (mul_nonneg_iff_of_pos_left this).mp hpos

def PCR_phi (k : ℕ) (t : ℝ) : ℝ := t - (2*(k:ℝ)+1)*t^2 + (k:ℝ)*(k+1)*t^3

theorem PCR_upd {d : ℕ} (f : ℝ → ℝ) (x : Fin d → ℝ) (i j : Fin d) (hij : i ≠ j) (a b : ℝ) :
    ∑ l, f (Function.update (Function.update x i a) j b l) + f (x i) + f (x j)
      = ∑ l, f (x l) + f a + f b := by
  have key : ∀ g : Fin d → ℝ, ∑ l, g l = g i + g j + ∑ l ∈ (Finset.univ.erase i).erase j, g l := by
    intro g
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨hij.symm, Finset.mem_univ j⟩)]
    ring
  rw [key (fun l => f (Function.update (Function.update x i a) j b l)), key (fun l => f (x l))]
  have : ∑ l ∈ (Finset.univ.erase i).erase j, f (Function.update (Function.update x i a) j b l)
      = ∑ l ∈ (Finset.univ.erase i).erase j, f (x l) := by
    apply Finset.sum_congr rfl
    intro l hl
    simp only [Finset.mem_erase] at hl
    rw [Function.update_of_ne hl.1, Function.update_of_ne hl.2.1]
  rw [this, Function.update_self, Function.update_of_ne hij, Function.update_self]
  ring

def PCR_S (d : ℕ) : Set (Fin d → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

theorem PCR_swap {d k : ℕ} (x : Fin d → ℝ)
    (hmin : ∀ y ∈ PCR_S d, ∑ l, PCR_phi k (x l) ≤ ∑ l, PCR_phi k (y l))
    (hx : x ∈ PCR_S d) (i j : Fin d) (hij : i ≠ j) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = x i + x j) :
    PCR_phi k (x i) + PCR_phi k (x j) ≤ PCR_phi k a + PCR_phi k b := by
  have hy : Function.update (Function.update x i a) j b ∈ PCR_S d := by
    refine ⟨fun l => ?_, ?_⟩
    · rw [Function.update_apply, Function.update_apply]
      split_ifs
      · exact hb
      · exact ha
      · exact hx.1 l
    · have := PCR_upd id x i j hij a b
      simp only [id] at this
      linarith [hx.2]
  have h1 := hmin _ hy
  have h2 := PCR_upd (PCR_phi k) x i j hij a b
  linarith

theorem PCR_S_compact (d : ℕ) : IsCompact (PCR_S d) := by
  have hsub : PCR_S d ⊆ Set.Icc 0 1 := by
    intro x hx
    refine ⟨fun i => hx.1 i, fun i => ?_⟩
    show x i ≤ 1
    rw [← hx.2]
    exact Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)
  apply (isCompact_Icc).of_isClosed_subset _ hsub
  have : PCR_S d = (⋂ i, {x : Fin d → ℝ | 0 ≤ x i}) ∩ {x | ∑ i, x i = 1} := by
    ext x; simp [PCR_S]
  rw [this]
  apply IsClosed.inter
  · exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  · exact isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const

theorem PCR_atmin {d k : ℕ} (hk : 1 ≤ k) (x : Fin d → ℝ)
    (hmin : ∀ y ∈ PCR_S d, ∑ l, PCR_phi k (x l) ≤ ∑ l, PCR_phi k (y l))
    (hx : x ∈ PCR_S d) : 0 ≤ ∑ l, PCR_phi k (x l) := by
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h; have := hx.2; simp at this
    · exact h
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨i0, hi0⟩ := Finite.exists_max x
  set w := x i0 with hwdef
  have hw : 0 < w := by
    by_contra hc
    push Not at hc
    have : ∑ i, x i ≤ 0 := Finset.sum_nonpos fun i _ => (hi0 i).trans hc
    linarith [hx.2]
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hkk : (0:ℝ) < k * (k+1) := by positivity
  -- M1, M2
  have M1 : ∀ i j, i ≠ j →
      0 ≤ x i * x j * (3*k*(k+1)*(x i + x j) - 2*(2*k+1)) := by
    intro i j hij
    have := PCR_swap x hmin hx i j hij (x i + x j) 0 (add_nonneg (hx.1 i) (hx.1 j)) le_rfl (by ring)
    have e : PCR_phi k (x i + x j) + PCR_phi k 0 - PCR_phi k (x i) - PCR_phi k (x j)
      = x i * x j * (3*k*(k+1)*(x i + x j) - 2*(2*k+1)) := by unfold PCR_phi; ring
    linarith
  have M2 : ∀ i j, i ≠ j →
      (3*k*(k+1)*(x i + x j) - 2*(2*k+1)) * (x i - x j)^2 ≤ 0 := by
    intro i j hij
    have hc : 0 ≤ (x i + x j)/2 := by linarith [hx.1 i, hx.1 j]
    have := PCR_swap x hmin hx i j hij ((x i + x j)/2) ((x i + x j)/2) hc hc (by ring)
    have e : 2 * PCR_phi k ((x i + x j)/2) - PCR_phi k (x i) - PCR_phi k (x j)
      = -((3*k*(k+1)*(x i + x j) - 2*(2*k+1)) * (x i - x j)^2) / 4 := by unfold PCR_phi; ring
    linarith
  have hclass : ∀ j, 0 < x j → x j ≠ w → 3*k*(k+1)*(x j + w) = 2*(2*k+1) := by
    intro j hj hjw
    have hji : j ≠ i0 := by rintro rfl; exact hjw rfl
    have hlt : x j < w := lt_of_le_of_ne (hi0 j) hjw
    have h1 := M1 j i0 hji
    have h2 := M2 j i0 hji
    rw [← hwdef] at h1 h2
    have hsq : 0 < (x j - w)^2 := by nlinarith
    have hG1 : 3*k*(k+1)*(x j + w) - 2*(2*k+1) ≤ 0 := by
      by_contra hc; push Not at hc; nlinarith
    have hG2 : 0 ≤ 3*k*(k+1)*(x j + w) - 2*(2*k+1) := by
      by_contra hc; push Not at hc
      have : 0 < x j * w := mul_pos hj hw
      nlinarith
    linarith
  have huniq : ∀ j1 j2, 0 < x j1 → x j1 ≠ w → 0 < x j2 → x j2 ≠ w → j1 = j2 := by
    intro j1 j2 h1 h1w h2 h2w
    by_contra hne
    have e1 := hclass j1 h1 h1w
    have e2 := hclass j2 h2 h2w
    have heq : x j1 = x j2 := by
      have : 3*k*(k+1)*(x j1 - x j2) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · nlinarith
      · linarith
    have hm := M1 j1 j2 hne
    rw [← heq] at hm
    have hlt : x j1 < w := lt_of_le_of_ne (hi0 j1) h1w
    have hG : 0 ≤ 3*k*(k+1)*(x j1 + x j1) - 2*(2*k+1) := by
      by_contra hc; push Not at hc
      have : 0 < x j1 * x j1 := mul_pos h1 h1
      nlinarith
    nlinarith
  -- decomposition
  set T := Finset.univ.filter (fun l => x l = w) with hT
  set m := T.card with hm
  have hsplit : ∀ f : ℝ → ℝ, ∑ l, f (x l) = m * f w +
      ∑ l ∈ Finset.univ.filter (fun l => ¬ x l = w), f (x l) := by
    intro f
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun l => x l = w)]
    congr 1
    rw [Finset.sum_congr rfl (fun l hl => by rw [(Finset.mem_filter.1 hl).2]), Finset.sum_const,
      nsmul_eq_mul]
  obtain ⟨u, hu0, huw, hu⟩ : ∃ u, 0 ≤ u ∧ u ≤ w ∧ ∀ f : ℝ → ℝ, f 0 = 0 →
      ∑ l ∈ Finset.univ.filter (fun l => ¬ x l = w), f (x l) = f u := by
    by_cases h : ∃ j, 0 < x j ∧ x j ≠ w
    · obtain ⟨j, hj, hjw⟩ := h
      refine ⟨x j, hj.le, hi0 j, fun f hf => ?_⟩
      apply Finset.sum_eq_single_of_mem j (by simp [hjw])
      intro l hl hlj
      have hl' : x l ≠ w := (Finset.mem_filter.1 hl).2
      have : x l = 0 := by
        rcases (hx.1 l).lt_or_eq with h | h
        · exact absurd (huniq l j h hl' hj hjw) hlj
        · exact h.symm
      rw [this, hf]
    · push Not at h
      refine ⟨0, le_rfl, hw.le, fun f hf => ?_⟩
      rw [hf]
      apply Finset.sum_eq_zero
      intro l hl
      have hl' : x l ≠ w := (Finset.mem_filter.1 hl).2
      have : x l = 0 := by
        rcases (hx.1 l).lt_or_eq with h' | h'
        · exact absurd (h l h') hl'
        · exact h'.symm
      rw [this, hf]
  have hm1 : 1 ≤ m := by
    rw [hm]
    exact Finset.card_pos.2 ⟨i0, by simp [hT, hwdef]⟩
  have hsum := hsplit id
  rw [hu id rfl] at hsum
  simp only [id] at hsum
  rw [hx.2] at hsum
  have hphi := hsplit (PCR_phi k)
  rw [hu (PCR_phi k) (by simp [PCR_phi])] at hphi
  rw [hphi]
  have := PCR_two m k hm1 w u hu0 huw hsum.symm
  have e : (m:ℝ) * PCR_phi k w + PCR_phi k u = ((m:ℝ) * w + u)
      - (2*(k:ℝ)+1) * ((m:ℝ) * w^2 + u^2) + (k:ℝ)*(k+1) * ((m:ℝ) * w^3 + u^3) := by
    unfold PCR_phi; ring
  rw [e, ← hsum]
  linarith

theorem PCR_simplex {d k : ℕ} (hk : 1 ≤ k) (x : Fin d → ℝ) (hx : x ∈ PCR_S d) :
    0 ≤ ∑ l, PCR_phi k (x l) := by
  have hcont : Continuous (fun y : Fin d → ℝ => ∑ l, PCR_phi k (y l)) := by
    unfold PCR_phi; fun_prop
  obtain ⟨z, hz, hzmin⟩ := (PCR_S_compact d).exists_isMinOn ⟨x, hx⟩ hcont.continuousOn
  have h0 := PCR_atmin hk z (fun y hy => hzmin hy) hz
  exact h0.trans (hzmin hx)

theorem PCR_key {d k : ℕ} (hk : 1 ≤ k) (x : Fin d → ℝ) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ (∑ i, x i)^3 - (2*(k:ℝ)+1) * ((∑ i, x i^2) * ∑ i, x i) + (k:ℝ)*(k+1) * ∑ i, x i^3 := by
  set s := ∑ i, x i with hs
  rcases (Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hx i)).lt_or_eq with hpos | hzero
  · rw [← hs] at hpos
    have hS : (fun i => x i / s) ∈ PCR_S d := by
      refine ⟨fun i => div_nonneg (hx i) hpos.le, ?_⟩
      rw [← Finset.sum_div, ← hs, div_self hpos.ne']
    have h0 := PCR_simplex hk _ hS
    have e : (∑ l, PCR_phi k (x l / s)) * s^3 =
        ∑ i, (s^2 * x i - (2*(k:ℝ)+1)*s*(x i^2) + (k:ℝ)*(k+1)*(x i^3)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      unfold PCR_phi
      field_simp
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, ← hs] at e
    have : 0 ≤ (∑ l, PCR_phi k (x l / s)) * s^3 := mul_nonneg h0 (by positivity)
    rw [e] at this
    nlinarith
  · have hz : ∀ i, x i = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hx i)).1 hzero.symm i (Finset.mem_univ i)
    simp [hs, hz]

def PCR_H : Set (Part 3 → ℝ) := {y | 0 ≤ y ⟨[3],by decide⟩ ∧
      0 ≤ y ⟨[2,1],by decide⟩ - y ⟨[3],by decide⟩ ∧
      ∀ k : ℕ, 1 ≤ k → 0 ≤ y ⟨[1,1,1],by decide⟩ -
        (2*(k:ℝ)+1)*y ⟨[2,1],by decide⟩ + (k:ℝ)*(k+1)*y ⟨[3],by decide⟩}

def PCR_G : Set (Part 3 → ℝ) := {y | ∃ d, 0 < d ∧ ∃ x : Fin d → ℝ,
    (∀ i, 0 ≤ x i) ∧ y = spectralMoments x}

theorem PCR_gen_H {y : Part 3 → ℝ} (hy : y ∈ PCR_G) : y ∈ PCR_H := by
  obtain ⟨d, _, x, hx, rfl⟩ := hy
  refine ⟨?_, ?_, fun k hk => ?_⟩
  · rw [PCR_smA]; exact Finset.sum_nonneg fun i _ => pow_nonneg (hx i) 3
  · rw [PCR_smA, PCR_smB, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_nonneg
    intro i _
    have : x i ≤ ∑ j, x j := Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)
    have e : x i ^ 2 * ∑ j, x j - x i ^ 3 = x i ^ 2 * (∑ j, x j - x i) := by ring
    rw [e]; exact mul_nonneg (sq_nonneg _) (by linarith)
  · rw [PCR_smA, PCR_smB, PCR_smC]
    exact PCR_key hk x hx

theorem PCR_consec (m k : ℕ) : 0 ≤ ((m:ℝ) - k) * ((m:ℝ) - k - 1) := by
  rcases le_or_gt m k with h | h
  · have : (m:ℝ) ≤ k := by exact_mod_cast h
    nlinarith
  · have : (k:ℝ) + 1 ≤ m := by exact_mod_cast h
    nlinarith

/-- choose the fan index -/
theorem PCR_index (a b c : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hk : ∀ k : ℕ, 1 ≤ k → 0 ≤ c - (2*(k:ℝ)+1)*b + (k:ℝ)*(k+1)*a) :
    ∃ m : ℕ, 1 ≤ m ∧ (m:ℝ) * a ≤ b ∧ b ≤ ((m:ℝ)+1) * a := by
  rcases ha.lt_or_eq with ha | ha
  · refine ⟨⌊b/a⌋₊, ?_, ?_, ?_⟩
    · apply Nat.le_floor
      rw [Nat.cast_one, le_div_iff₀ ha]; linarith
    · have := Nat.floor_le (div_nonneg (ha.le.trans hab) ha.le)
      rwa [le_div_iff₀ ha] at this
    · have := Nat.lt_floor_add_one (b/a)
      rw [div_lt_iff₀ ha] at this; linarith
  · subst ha
    have hb : b = 0 := by
      by_contra hb
      have hb' : 0 < b := lt_of_le_of_ne hab (Ne.symm hb)
      obtain ⟨n, hn⟩ := exists_nat_gt (c / b)
      rw [div_lt_iff₀ hb'] at hn
      have := hk (n+1) (by omega)
      push_cast at this
      nlinarith
    exact ⟨1, le_rfl, by simp [hb], by simp [hb]⟩


def PCR_A : Part 3 := ⟨[3], by decide⟩
def PCR_B : Part 3 := ⟨[2,1], by decide⟩
def PCR_C : Part 3 := ⟨[1,1,1], by decide⟩

theorem PCR_AB : PCR_A ≠ PCR_B := by
  intro h; have := congrArg Subtype.val h; simp [PCR_A, PCR_B] at this
theorem PCR_AC : PCR_A ≠ PCR_C := by
  intro h; have := congrArg Subtype.val h; simp [PCR_A, PCR_C] at this
theorem PCR_BC : PCR_B ≠ PCR_C := by
  intro h; have := congrArg Subtype.val h; simp [PCR_B, PCR_C] at this

theorem PCR_ext {f g : Coeff 3} (hA : f PCR_A = g PCR_A) (hB : f PCR_B = g PCR_B)
    (hC : f PCR_C = g PCR_C) : f = g := by
  ext p
  rcases PCR_parts p with rfl | rfl | rfl
  · exact hA
  · exact hB
  · exact hC

theorem PCR_pairing (f : Coeff 3) (y : Part 3 → ℝ) :
    pairing f y = f PCR_A * y PCR_A + f PCR_B * y PCR_B + f PCR_C * y PCR_C := by
  classical
  unfold pairing
  rw [Finsupp.sum_of_support_subset f (s := {PCR_A, PCR_B, PCR_C})]
  · rw [Finset.sum_insert (by simp [PCR_AB, PCR_AC]), Finset.sum_insert (by simp [PCR_BC]),
      Finset.sum_singleton]
    ring
  · intro p _
    rcases PCR_parts p with rfl | rfl | rfl
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  · intro i _; simp

theorem PCR_b3 : (b3 PCR_A = 1) ∧ (b3 PCR_B = 0) ∧ (b3 PCR_C = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · show Finsupp.single PCR_A (1:ℝ) PCR_A = 1
    exact Finsupp.single_eq_same
  · show Finsupp.single PCR_A (1:ℝ) PCR_B = 0
    simp [PCR_AB]
  · show Finsupp.single PCR_A (1:ℝ) PCR_C = 0
    simp [PCR_AC]

theorem PCR_b21 : (b21 PCR_A = 0) ∧ (b21 PCR_B = 1) ∧ (b21 PCR_C = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · show Finsupp.single PCR_B (1:ℝ) PCR_A = 0
    simp [PCR_AB.symm]
  · show Finsupp.single PCR_B (1:ℝ) PCR_B = 1
    exact Finsupp.single_eq_same
  · show Finsupp.single PCR_B (1:ℝ) PCR_C = 0
    simp [PCR_BC]

theorem PCR_b111 : (b111 PCR_A = 0) ∧ (b111 PCR_B = 0) ∧ (b111 PCR_C = 1) := by
  refine ⟨?_, ?_, ?_⟩
  · show Finsupp.single PCR_C (1:ℝ) PCR_A = 0
    simp [PCR_AC.symm]
  · show Finsupp.single PCR_C (1:ℝ) PCR_B = 0
    simp [PCR_BC.symm]
  · show Finsupp.single PCR_C (1:ℝ) PCR_C = 1
    exact Finsupp.single_eq_same

def PCR_mk (a b c : ℝ) : Coeff 3 := a • b3 + b • b21 + c • b111

theorem PCR_mk_apply (a b c : ℝ) : PCR_mk a b c PCR_A = a ∧ PCR_mk a b c PCR_B = b ∧
    PCR_mk a b c PCR_C = c := by
  obtain ⟨h1, h2, h3⟩ := PCR_b3
  obtain ⟨h4, h5, h6⟩ := PCR_b21
  obtain ⟨h7, h8, h9⟩ := PCR_b111
  simp only [PCR_mk, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_, ?_⟩ <;> simp [*]

theorem PCR_eta (f : Coeff 3) : f = PCR_mk (f PCR_A) (f PCR_B) (f PCR_C) := by
  obtain ⟨h1, h2, h3⟩ := PCR_mk_apply (f PCR_A) (f PCR_B) (f PCR_C)
  exact PCR_ext h1.symm h2.symm h3.symm

theorem PCR_mk_add (a b c a' b' c' : ℝ) :
    PCR_mk a b c + PCR_mk a' b' c' = PCR_mk (a + a') (b + b') (c + c') := by
  simp only [PCR_mk, add_smul]; abel

theorem PCR_mk_smul (t a b c : ℝ) : t • PCR_mk a b c = PCR_mk (t * a) (t * b) (t * c) := by
  simp only [PCR_mk, smul_add, smul_smul]

theorem PCR_mk_inj {a b c a' b' c' : ℝ} (h : PCR_mk a b c = PCR_mk a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  obtain ⟨h1, h2, h3⟩ := PCR_mk_apply a b c
  obtain ⟨h4, h5, h6⟩ := PCR_mk_apply a' b' c'
  rw [h] at h1 h2 h3
  exact ⟨h1.symm.trans h4, h2.symm.trans h5, h3.symm.trans h6⟩

theorem PCR_b3_mk : b3 = PCR_mk 1 0 0 := by
  rw [PCR_eta b3]; obtain ⟨h1, h2, h3⟩ := PCR_b3; rw [h1, h2, h3]

theorem PCR_b21b3_mk : b21 - b3 = PCR_mk (-1) 1 0 := by
  rw [PCR_eta (b21 - b3)]; obtain ⟨h1, h2, h3⟩ := PCR_b3; obtain ⟨h4, h5, h6⟩ := PCR_b21
  simp only [Finsupp.sub_apply, h1, h2, h3, h4, h5, h6]; norm_num

theorem PCR_cubic_mk (k : ℕ) :
    cubicRay k = PCR_mk ((k:ℝ) * (k+1)) (-(2*(k:ℝ)+1)) 1 := by
  rw [PCR_eta (cubicRay k)]
  obtain ⟨h1, h2, h3⟩ := PCR_b3; obtain ⟨h4, h5, h6⟩ := PCR_b21
  obtain ⟨h7, h8, h9⟩ := PCR_b111
  simp only [cubicRay, Finsupp.sub_apply, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    h1, h2, h3, h4, h5, h6, h7, h8, h9]
  congr 1 <;> ring

theorem PCR_lead (a b c : ℝ) (h : ∀ m : ℕ, 1 ≤ m → 0 ≤ a + b*m + c*(m:ℝ)^2) : 0 ≤ c := by
  by_contra hc
  push Not at hc
  obtain ⟨n, hn⟩ := exists_nat_gt ((|a| + |b|) / (-c))
  rw [div_lt_iff₀ (neg_pos.2 hc)] at hn
  have hm := h (n+1) (by omega)
  push_cast at hm
  have hM : (n:ℝ) < (n:ℝ) + 1 := by linarith
  have hM1 : (1:ℝ) ≤ (n:ℝ) + 1 := by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have h1 : |a| + |b| < ((n:ℝ)+1) * (-c) := by nlinarith
  have h2 : c * ((n:ℝ)+1)^2 < -((|a| + |b|) * ((n:ℝ)+1)) := by nlinarith
  have h3 : b * ((n:ℝ)+1) ≤ |b| * ((n:ℝ)+1) :=
    mul_le_mul_of_nonneg_right (le_abs_self b) (by linarith)
  have h4 : |a| ≤ |a| * ((n:ℝ)+1) := by nlinarith [abs_nonneg a]
  nlinarith [le_abs_self a]

theorem PCR_linb (a b : ℝ) (h : ∀ m : ℕ, 1 ≤ m → 0 ≤ a + b*m) : 0 ≤ b := by
  by_contra hc
  push Not at hc
  obtain ⟨n, hn⟩ := exists_nat_gt (|a| / (-b))
  rw [div_lt_iff₀ (neg_pos.2 hc)] at hn
  have hm := h (n+1) (by omega)
  push_cast at hm
  nlinarith [le_abs_self a]

theorem PCR_mem (f : Coeff 3) : f ∈ psdCone 3 ↔
    0 ≤ f PCR_C ∧ ∀ m : ℕ, 1 ≤ m → 0 ≤ f PCR_A + f PCR_B * m + f PCR_C * (m:ℝ)^2 := by
  constructor
  · intro hf
    have hq : ∀ m : ℕ, 1 ≤ m → 0 ≤ f PCR_A + f PCR_B * m + f PCR_C * (m:ℝ)^2 := by
      intro m hm
      have h := hf m hm (fun _ => 1) (fun _ => zero_le_one)
      rw [PCR_pairing, show spectralMoments (fun _ : Fin m => (1:ℝ)) PCR_A = _ from PCR_smA _,
        show spectralMoments (fun _ : Fin m => (1:ℝ)) PCR_B = _ from PCR_smB _,
        show spectralMoments (fun _ : Fin m => (1:ℝ)) PCR_C = _ from PCR_smC _] at h
      simp at h
      have hm' : (0:ℝ) < m := by exact_mod_cast hm
      have e : f PCR_A * m + f PCR_B * (m * m) + f PCR_C * m^3
          = m * (f PCR_A + f PCR_B * m + f PCR_C * (m:ℝ)^2) := by ring
      rw [e] at h
      exact (mul_nonneg_iff_of_pos_left hm').1 h
    exact ⟨PCR_lead _ _ _ hq, hq⟩
  · rintro ⟨hC, hq⟩ d hd x hx
    have hy := PCR_gen_H ⟨d, hd, x, hx, rfl⟩
    obtain ⟨ha, hba, hk⟩ := hy
    set y := spectralMoments (n := 3) x
    have ha' : 0 ≤ y PCR_A := ha
    have hba' : 0 ≤ y PCR_B - y PCR_A := hba
    have hk' : ∀ k : ℕ, 1 ≤ k → 0 ≤ y PCR_C - (2*(k:ℝ)+1) * y PCR_B + (k:ℝ)*(k+1) * y PCR_A :=
      hk
    obtain ⟨m, hm, h1, h2⟩ := PCR_index (y PCR_A) (y PCR_B) (y PCR_C) ha' (by linarith) hk'
    rw [PCR_pairing]
    have e : f PCR_A * y PCR_A + f PCR_B * y PCR_B + f PCR_C * y PCR_C
        = (((m:ℝ)+1) * y PCR_A - y PCR_B) * (f PCR_A + f PCR_B * m + f PCR_C * (m:ℝ)^2)
          + (y PCR_B - m * y PCR_A) *
            (f PCR_A + f PCR_B * ((m:ℝ)+1) + f PCR_C * ((m:ℝ)+1)^2)
          + (y PCR_C - (2*(m:ℝ)+1) * y PCR_B + (m:ℝ)*(m+1) * y PCR_A) * f PCR_C := by ring
    rw [e]
    have hq1 := hq (m+1) (by omega)
    push_cast at hq1
    apply add_nonneg; apply add_nonneg
    · exact mul_nonneg (by linarith) (hq m hm)
    · exact mul_nonneg (by linarith) hq1
    · exact mul_nonneg (hk' m hm) hC

theorem PCR_mk_mem (a b c : ℝ) : PCR_mk a b c ∈ psdCone 3 ↔
    0 ≤ c ∧ ∀ m : ℕ, 1 ≤ m → 0 ≤ a + b * m + c * (m:ℝ)^2 := by
  obtain ⟨h1, h2, h3⟩ := PCR_mk_apply a b c
  rw [PCR_mem, h1, h2, h3]

theorem PCR_mk_zero : PCR_mk 0 0 0 = 0 := by simp [PCR_mk]

theorem PCR_ray_smul {c : ℝ} (hc : 0 < c) (g : Coeff 3) : ray (c • g) = ray g := by
  ext w
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d * c, mul_nonneg hd hc.le, by rw [smul_smul]⟩
  · rintro ⟨d, hd, rfl⟩
    refine ⟨d / c, div_nonneg hd hc.le, ?_⟩
    rw [smul_smul, div_mul_cancel₀ d hc.ne']

theorem PCR_cubic_mem (k : ℕ) : cubicRay k ∈ psdCone 3 := by
  rw [PCR_cubic_mk, PCR_mk_mem]
  refine ⟨zero_le_one, fun m _ => ?_⟩
  have := PCR_consec m k
  nlinarith

theorem PCR_smul_mem {s : ℝ} (hs : 0 ≤ s) {f : Coeff 3} (hf : f ∈ psdCone 3) :
    s • f ∈ psdCone 3 := by
  rw [PCR_eta f, PCR_mk_smul, PCR_mk_mem]
  rw [PCR_mem] at hf
  refine ⟨mul_nonneg hs hf.1, fun m hm => ?_⟩
  have := mul_nonneg hs (hf.2 m hm)
  nlinarith

theorem PCR_extreme_crit (a b c : ℝ) (hne : ¬(a = 0 ∧ b = 0 ∧ c = 0))
    (hmem : PCR_mk a b c ∈ psdCone 3)
    (H : ∀ ua ub uc wa wb wc : ℝ, PCR_mk ua ub uc ∈ psdCone 3 → PCR_mk wa wb wc ∈ psdCone 3 →
      ua + wa = a → ub + wb = b → uc + wc = c →
      ∃ t, 0 ≤ t ∧ ua = t * a ∧ ub = t * b ∧ uc = t * c) :
    Extreme (psdCone 3) (PCR_mk a b c) := by
  refine ⟨fun h => hne (PCR_mk_inj (h.trans PCR_mk_zero.symm)), hmem, ?_⟩
  intro u hu w hw huw
  obtain ⟨ua, ub, uc, rfl⟩ : ∃ a b c, u = PCR_mk a b c := ⟨_, _, _, PCR_eta u⟩
  obtain ⟨wa, wb, wc, rfl⟩ : ∃ a b c, w = PCR_mk a b c := ⟨_, _, _, PCR_eta w⟩
  rw [PCR_mk_add] at huw
  obtain ⟨e1, e2, e3⟩ := PCR_mk_inj huw
  obtain ⟨t, ht, t1, t2, t3⟩ := H ua ub uc wa wb wc hu hw e1 e2 e3
  obtain ⟨s, hs, s1, s2, s3⟩ := H wa wb wc ua ub uc hw hu (by linarith) (by linarith)
    (by linarith)
  refine ⟨t, s, ht, hs, ?_, ?_⟩
  · rw [PCR_mk_smul, t1, t2, t3]
  · rw [PCR_mk_smul, s1, s2, s3]

theorem PCR_ext_b3 : Extreme (psdCone 3) b3 := by
  rw [PCR_b3_mk]
  apply PCR_extreme_crit
  · norm_num
  · rw [PCR_mk_mem]; exact ⟨le_rfl, fun m _ => by simp⟩
  · intro ua ub uc wa wb wc hu hw e1 e2 e3
    rw [PCR_mk_mem] at hu hw
    have huc : uc = 0 := by linarith [hu.1, hw.1]
    have hwc : wc = 0 := by linarith [hu.1, hw.1]
    have hub := PCR_linb ua ub (fun m hm => by have := hu.2 m hm; rw [huc] at this; linarith)
    have hwb := PCR_linb wa wb (fun m hm => by have := hw.2 m hm; rw [hwc] at this; linarith)
    have hua := hu.2 1 le_rfl
    refine ⟨ua, by simp at hua; linarith, by ring, by linarith, by linarith⟩

theorem PCR_ext_b21 : Extreme (psdCone 3) (b21 - b3) := by
  rw [PCR_b21b3_mk]
  apply PCR_extreme_crit
  · norm_num
  · rw [PCR_mk_mem]
    refine ⟨le_rfl, fun m hm => ?_⟩
    have : (1:ℝ) ≤ m := by exact_mod_cast hm
    linarith
  · intro ua ub uc wa wb wc hu hw e1 e2 e3
    rw [PCR_mk_mem] at hu hw
    have huc : uc = 0 := by linarith [hu.1, hw.1]
    have hwc : wc = 0 := by linarith [hu.1, hw.1]
    have hub := PCR_linb ua ub (fun m hm => by have := hu.2 m hm; rw [huc] at this; linarith)
    have hu1 := hu.2 1 le_rfl
    have hw1 := hw.2 1 le_rfl
    simp at hu1 hw1
    refine ⟨ub, hub, by linarith, by ring, by linarith⟩

theorem PCR_ext_cubic (k : ℕ) (hk : 1 ≤ k) : Extreme (psdCone 3) (cubicRay k) := by
  rw [PCR_cubic_mk]
  apply PCR_extreme_crit
  · norm_num
  · rw [← PCR_cubic_mk]; exact PCR_cubic_mem k
  · intro ua ub uc wa wb wc hu hw e1 e2 e3
    rw [PCR_mk_mem] at hu hw
    have hu1 := hu.2 k hk
    have hw1 := hw.2 k hk
    have hu2 := hu.2 (k+1) (by omega)
    have hw2 := hw.2 (k+1) (by omega)
    push_cast at hu2 hw2
    have s1 : (ua + wa) + (ub + wb) * k + (uc + wc) * (k:ℝ)^2 = 0 := by
      rw [e1, e2, e3]; ring
    have s2 : (ua + wa) + (ub + wb) * ((k:ℝ)+1) + (uc + wc) * ((k:ℝ)+1)^2 = 0 := by
      rw [e1, e2, e3]; ring
    have q1 : ua + ub * k + uc * (k:ℝ)^2 = 0 := by linarith
    have q2 : ua + ub * ((k:ℝ)+1) + uc * ((k:ℝ)+1)^2 = 0 := by linarith
    refine ⟨uc, hu.1, ?_, ?_, by ring⟩
    · linear_combination (1 + (k:ℝ)) * q1 - (k:ℝ) * q2
    · linear_combination q2 - q1

theorem PCR_class {v : Coeff 3} (hv : Extreme (psdCone 3) v) :
    ray v = ray b3 ∨ ray v = ray (b21 - b3) ∨ ∃ k : ℕ, 1 ≤ k ∧ ray v = ray (cubicRay k) := by
  obtain ⟨hne, hmem, hsplit⟩ := hv
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c, v = PCR_mk a b c := ⟨_, _, _, PCR_eta v⟩
  have hm := (PCR_mk_mem a b c).1 hmem
  obtain ⟨hc, hq⟩ := hm
  rcases hc.lt_or_eq with hc | hc
  · -- c > 0
    have hex : ∃ n : ℕ, 0 ≤ b + c * (2 * ((n:ℝ)+1) + 1) := by
      obtain ⟨n, hn⟩ := exists_nat_gt (|b| / c)
      rw [div_lt_iff₀ hc] at hn
      refine ⟨n, ?_⟩
      have : (0:ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith [neg_abs_le b]
    classical
    set j := Nat.find hex with hj
    have hP : 0 ≤ b + c * (2 * ((j:ℝ)+1) + 1) := Nat.find_spec hex
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · -- k = 1
      rw [h0] at hP
      norm_num at hP
      have hX : c • cubicRay 1 ∈ psdCone 3 := PCR_smul_mem hc.le (PCR_cubic_mem 1)
      have hY : PCR_mk (a - 2*c) (b + 3*c) 0 ∈ psdCone 3 := by
        rw [PCR_mk_mem]
        refine ⟨le_rfl, fun m hm => ?_⟩
        have h1 := hq 1 le_rfl
        have : (1:ℝ) ≤ m := by exact_mod_cast hm
        simp at h1
        nlinarith
      have hsum : c • cubicRay 1 + PCR_mk (a - 2*c) (b + 3*c) 0 = PCR_mk a b c := by
        rw [PCR_cubic_mk, PCR_mk_smul, PCR_mk_add]
        congr 1 <;> push_cast <;> ring
      obtain ⟨s, t, _, _, hs, _⟩ := hsplit _ hX _ hY hsum
      rw [PCR_cubic_mk, PCR_mk_smul, PCR_mk_smul] at hs
      obtain ⟨g1, g2, h3⟩ := PCR_mk_inj hs
      have hs1 : s = 1 := by
        have : (s - 1) * c = 0 := by linarith
        rcases mul_eq_zero.1 this with h | h
        · linarith
        · linarith
      right; right
      refine ⟨1, le_rfl, ?_⟩
      rw [hs1] at g1 g2
      have hv : PCR_mk a b c = c • cubicRay 1 := by
        rw [PCR_cubic_mk, PCR_mk_smul]
        push_cast at g1 g2
        congr 1 <;> push_cast <;> linarith
      rw [hv]; exact PCR_ray_smul hc _
    · -- k = j + 1, j ≥ 1
      have hmin : ¬ (0 ≤ b + c * (2 * (((j-1 : ℕ):ℝ)+1) + 1)) :=
        Nat.find_min hex (by omega)
      have hj1 : (((j-1 : ℕ):ℝ)) = (j:ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      rw [hj1] at hmin
      push Not at hmin
      set t := (b + (2*(j:ℝ)+3)*c)/2 with ht
      set s' := c - t with hs'
      have ht0 : 0 ≤ t := by rw [ht]; linarith
      have hs0 : 0 < s' := by rw [hs', ht]; linarith
      set q := a + b * ((j:ℝ)+1) + c * ((j:ℝ)+1)^2 with hqdef
      have hq0 : 0 ≤ q := by have := hq (j+1) (by omega); push_cast at this; linarith
      have hX : s' • cubicRay (j+1) ∈ psdCone 3 := PCR_smul_mem hs0.le (PCR_cubic_mem (j+1))
      have hY : PCR_mk (t * (j * (j+1)) + q) (-(t * (2*(j:ℝ)+1))) t ∈ psdCone 3 := by
        rw [PCR_mk_mem]
        refine ⟨ht0, fun m hm => ?_⟩
        have := mul_nonneg ht0 (PCR_consec m j)
        nlinarith
      have hsum : s' • cubicRay (j+1) + PCR_mk (t * (j * (j+1)) + q) (-(t * (2*(j:ℝ)+1))) t
          = PCR_mk a b c := by
        rw [PCR_cubic_mk, PCR_mk_smul, PCR_mk_add]
        congr 1
        · rw [hqdef, hs', ht]; push_cast; ring
        · rw [hs', ht]; push_cast; ring
        · rw [hs']; ring
      obtain ⟨s, _, _, _, hs, _⟩ := hsplit _ hX _ hY hsum
      rw [PCR_cubic_mk, PCR_mk_smul, PCR_mk_smul] at hs
      obtain ⟨g1, g2, h3⟩ := PCR_mk_inj hs
      have hsc : s' = s * c := by linarith
      have hspos : 0 < s := by
        by_contra h; push Not at h; nlinarith
      right; right
      refine ⟨j+1, by omega, ?_⟩
      have hv : PCR_mk a b c = (s⁻¹ * s') • cubicRay (j+1) := by
        rw [PCR_cubic_mk, PCR_mk_smul]
        congr 1
        · field_simp; linarith
        · field_simp; linarith
        · field_simp; linarith
      rw [hv]
      exact PCR_ray_smul (mul_pos (inv_pos.2 hspos) hs0) _
  · -- c = 0
    subst hc
    have hb : 0 ≤ b := PCR_linb a b (fun m hm => by have := hq m hm; linarith)
    have h1 := hq 1 le_rfl
    simp at h1
    have hX : PCR_mk (a + b) 0 0 ∈ psdCone 3 := by
      rw [PCR_mk_mem]; exact ⟨le_rfl, fun m _ => by simp; linarith⟩
    have hY : PCR_mk (-b) b 0 ∈ psdCone 3 := by
      rw [PCR_mk_mem]
      refine ⟨le_rfl, fun m hm => ?_⟩
      have : (1:ℝ) ≤ m := by exact_mod_cast hm
      nlinarith
    have hsum : PCR_mk (a + b) 0 0 + PCR_mk (-b) b 0 = PCR_mk a b 0 := by
      rw [PCR_mk_add]; congr 1 <;> ring
    obtain ⟨s, _, _, _, hs, _⟩ := hsplit _ hX _ hY hsum
    rw [PCR_mk_smul] at hs
    obtain ⟨e1, e2, _⟩ := PCR_mk_inj hs
    rcases hb.lt_or_eq with hb | hb
    · right; left
      have hs0 : s = 0 := by
        rcases mul_eq_zero.1 e2.symm with h | h
        · exact h
        · linarith
      rw [hs0] at e1
      have hab : a = -b := by linarith
      rw [hab, show PCR_mk (-b) b 0 = b • (b21 - b3) by
        rw [PCR_b21b3_mk, PCR_mk_smul]; congr 1 <;> ring]
      exact PCR_ray_smul hb _
    · left
      subst hb
      have ha : 0 < a := by
        rcases h1.lt_or_eq with h | h
        · simpa using h
        · exfalso; apply hne; rw [show a = 0 by linarith]; exact PCR_mk_zero
      rw [show PCR_mk a 0 0 = a • b3 by rw [PCR_b3_mk, PCR_mk_smul]; congr 1 <;> ring]
      exact PCR_ray_smul ha _

theorem PCR_rays : extremeRays (psdCone 3) =
      ({ray b3,ray (b21-b3)} ∪ {R | ∃ k : ℕ, 1 ≤ k ∧ R = ray (cubicRay k)}) := by
  ext R
  constructor
  · rintro ⟨v, hv, rfl⟩
    rcases PCR_class hv with h | h | ⟨k, hk, h⟩
    · left; left; exact h
    · left; right; exact h
    · right; exact ⟨k, hk, h⟩
  · rintro ((h | h) | ⟨k, hk, h⟩)
    · exact ⟨b3, PCR_ext_b3, h⟩
    · exact ⟨b21 - b3, PCR_ext_b21, h⟩
    · exact ⟨cubicRay k, PCR_ext_cubic k hk, h⟩

theorem PCR_np_aux {N : ℕ} (L : Fin N → Coeff 3 →ₗ[ℝ] ℝ)
    (hL : ∀ f, f ∈ psdCone 3 ↔ ∀ i, 0 ≤ L i f) (k1 k2 : ℕ) (hk1 : 1 ≤ k1) (hlt : k1 < k2)
    (hA : ∀ i, L i (cubicRay k1) = 0 → L i (cubicRay k2) = 0) : False := by
  set v := cubicRay k1
  set v' := cubicRay k2
  have hv := (hL v).1 (PCR_cubic_mem k1)
  have hev : ∀ᶠ t in nhds (0:ℝ), ∀ i, 0 ≤ L i v + t * (L i v - L i v') := by
    rw [Filter.eventually_all]
    intro i
    by_cases h0 : L i v = 0
    · have h1 := hA i h0
      exact Filter.Eventually.of_forall fun t => by rw [h0, h1]; simp
    · have hpos : 0 < L i v := lt_of_le_of_ne (hv i) (Ne.symm h0)
      have hc : Continuous fun t : ℝ => L i v + t * (L i v - L i v') := by fun_prop
      have := hc.continuousAt (x := 0) |>.eventually (lt_mem_nhds (by simpa using hpos))
      exact this.mono fun t ht => ht.le
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hz := hball (y := ε/2) (by rw [Real.dist_eq]; rw [abs_of_pos (by linarith)]; linarith)
  have hzmem : v + (ε/2) • (v - v') ∈ psdCone 3 := by
    rw [hL]
    intro i
    simpa [map_add, map_smul, map_sub] using hz i
  have hvv : v + (ε/2) • (v - v') = PCR_mk ((k1:ℝ)*(k1+1) + ε/2 * ((k1:ℝ)*(k1+1) - (k2:ℝ)*(k2+1)))
      (-(2*(k1:ℝ)+1) + ε/2 * (-(2*(k1:ℝ)+1) + (2*(k2:ℝ)+1))) 1 := by
    rw [show v = _ from PCR_cubic_mk k1, show v' = _ from PCR_cubic_mk k2, sub_eq_add_neg, ← neg_one_smul ℝ (PCR_mk _ _ _),
      PCR_mk_smul, PCR_mk_add, PCR_mk_smul, PCR_mk_add]
    congr 1 <;> ring
  rw [hvv, PCR_mk_mem] at hzmem
  have h := hzmem.2 k1 hk1
  have hk : (k1:ℝ) + 1 ≤ k2 := by exact_mod_cast hlt
  have hd : 0 < (k2:ℝ) - k1 := by linarith
  nlinarith [mul_pos (half_pos hε) (mul_pos hd (by linarith : (0:ℝ) < k2 - k1 + 1))]

theorem PCR_not_poly : ¬ IsPolyhedral (psdCone 3) := by
  rintro ⟨N, L, hL⟩
  have hL' : ∀ f, f ∈ psdCone 3 ↔ ∀ i, 0 ≤ L i f := by
    intro f; rw [hL]; rfl
  obtain ⟨x, y, hxy, hf⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ => {i : Fin N | L i (cubicRay (n+1)) = 0})
  have hiff : ∀ i, L i (cubicRay (x+1)) = 0 ↔ L i (cubicRay (y+1)) = 0 := by
    intro i
    have := congrArg (fun S : Set (Fin N) => i ∈ S) hf
    simpa using this
  rcases lt_or_gt_of_ne hxy with h | h
  · exact PCR_np_aux L hL' (x+1) (y+1) (by omega) (by omega) fun i => (hiff i).1
  · exact PCR_np_aux L hL' (y+1) (x+1) (by omega) (by omega) fun i => (hiff i).2

end QAlgorithms.Papers.Independent.Information100.P19

open QAlgorithms.Papers.Independent.Information100.P19 in
theorem solution  :
    extremeRays (psdCone 3) =
      ({ray b3,ray (b21-b3)} ∪ {R | ∃ k : ℕ, 1 ≤ k ∧ R = ray (cubicRay k)}) ∧
    ¬ IsPolyhedral (psdCone 3) :=
  ⟨PCR_rays, PCR_not_poly⟩

