-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P19.psd_cubic_moments
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T13:32:39.922379+00:00
-- url     : https://prove2.me/submissions/6aa866bc-03d2-4f9e-85c9-5f75648aac1e

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section
open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder
open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

theorem PCM_parts (p : Part 3) :
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

theorem PCM_smA {d : ℕ} (x : Fin d → ℝ) :
    spectralMoments x (⟨[3], by decide⟩ : Part 3) = ∑ i, x i ^ 3 := by
  simp [spectralMoments]

theorem PCM_smB {d : ℕ} (x : Fin d → ℝ) :
    spectralMoments x (⟨[2,1], by decide⟩ : Part 3) = (∑ i, x i ^ 2) * ∑ i, x i := by
  simp [spectralMoments]

theorem PCM_smC {d : ℕ} (x : Fin d → ℝ) :
    spectralMoments x (⟨[1,1,1], by decide⟩ : Part 3) = (∑ i, x i) ^ 3 := by
  simp [spectralMoments]; ring

/-- two-level bound -/
theorem PCM_two (m k : ℕ) (hm : 1 ≤ m) (w u : ℝ) (hu : 0 ≤ u) (huw : u ≤ w)
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

def PCM_phi (k : ℕ) (t : ℝ) : ℝ := t - (2*(k:ℝ)+1)*t^2 + (k:ℝ)*(k+1)*t^3

theorem PCM_upd {d : ℕ} (f : ℝ → ℝ) (x : Fin d → ℝ) (i j : Fin d) (hij : i ≠ j) (a b : ℝ) :
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

def PCM_S (d : ℕ) : Set (Fin d → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

theorem PCM_swap {d k : ℕ} (x : Fin d → ℝ)
    (hmin : ∀ y ∈ PCM_S d, ∑ l, PCM_phi k (x l) ≤ ∑ l, PCM_phi k (y l))
    (hx : x ∈ PCM_S d) (i j : Fin d) (hij : i ≠ j) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = x i + x j) :
    PCM_phi k (x i) + PCM_phi k (x j) ≤ PCM_phi k a + PCM_phi k b := by
  have hy : Function.update (Function.update x i a) j b ∈ PCM_S d := by
    refine ⟨fun l => ?_, ?_⟩
    · rw [Function.update_apply, Function.update_apply]
      split_ifs
      · exact hb
      · exact ha
      · exact hx.1 l
    · have := PCM_upd id x i j hij a b
      simp only [id] at this
      linarith [hx.2]
  have h1 := hmin _ hy
  have h2 := PCM_upd (PCM_phi k) x i j hij a b
  linarith

theorem PCM_S_compact (d : ℕ) : IsCompact (PCM_S d) := by
  have hsub : PCM_S d ⊆ Set.Icc 0 1 := by
    intro x hx
    refine ⟨fun i => hx.1 i, fun i => ?_⟩
    show x i ≤ 1
    rw [← hx.2]
    exact Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)
  apply (isCompact_Icc).of_isClosed_subset _ hsub
  have : PCM_S d = (⋂ i, {x : Fin d → ℝ | 0 ≤ x i}) ∩ {x | ∑ i, x i = 1} := by
    ext x; simp [PCM_S]
  rw [this]
  apply IsClosed.inter
  · exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  · exact isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const

theorem PCM_atmin {d k : ℕ} (hk : 1 ≤ k) (x : Fin d → ℝ)
    (hmin : ∀ y ∈ PCM_S d, ∑ l, PCM_phi k (x l) ≤ ∑ l, PCM_phi k (y l))
    (hx : x ∈ PCM_S d) : 0 ≤ ∑ l, PCM_phi k (x l) := by
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
    have := PCM_swap x hmin hx i j hij (x i + x j) 0 (add_nonneg (hx.1 i) (hx.1 j)) le_rfl (by ring)
    have e : PCM_phi k (x i + x j) + PCM_phi k 0 - PCM_phi k (x i) - PCM_phi k (x j)
      = x i * x j * (3*k*(k+1)*(x i + x j) - 2*(2*k+1)) := by unfold PCM_phi; ring
    linarith
  have M2 : ∀ i j, i ≠ j →
      (3*k*(k+1)*(x i + x j) - 2*(2*k+1)) * (x i - x j)^2 ≤ 0 := by
    intro i j hij
    have hc : 0 ≤ (x i + x j)/2 := by linarith [hx.1 i, hx.1 j]
    have := PCM_swap x hmin hx i j hij ((x i + x j)/2) ((x i + x j)/2) hc hc (by ring)
    have e : 2 * PCM_phi k ((x i + x j)/2) - PCM_phi k (x i) - PCM_phi k (x j)
      = -((3*k*(k+1)*(x i + x j) - 2*(2*k+1)) * (x i - x j)^2) / 4 := by unfold PCM_phi; ring
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
  have hphi := hsplit (PCM_phi k)
  rw [hu (PCM_phi k) (by simp [PCM_phi])] at hphi
  rw [hphi]
  have := PCM_two m k hm1 w u hu0 huw hsum.symm
  have e : (m:ℝ) * PCM_phi k w + PCM_phi k u = ((m:ℝ) * w + u)
      - (2*(k:ℝ)+1) * ((m:ℝ) * w^2 + u^2) + (k:ℝ)*(k+1) * ((m:ℝ) * w^3 + u^3) := by
    unfold PCM_phi; ring
  rw [e, ← hsum]
  linarith

theorem PCM_simplex {d k : ℕ} (hk : 1 ≤ k) (x : Fin d → ℝ) (hx : x ∈ PCM_S d) :
    0 ≤ ∑ l, PCM_phi k (x l) := by
  have hcont : Continuous (fun y : Fin d → ℝ => ∑ l, PCM_phi k (y l)) := by
    unfold PCM_phi; fun_prop
  obtain ⟨z, hz, hzmin⟩ := (PCM_S_compact d).exists_isMinOn ⟨x, hx⟩ hcont.continuousOn
  have h0 := PCM_atmin hk z (fun y hy => hzmin hy) hz
  exact h0.trans (hzmin hx)

theorem PCM_key {d k : ℕ} (hk : 1 ≤ k) (x : Fin d → ℝ) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ (∑ i, x i)^3 - (2*(k:ℝ)+1) * ((∑ i, x i^2) * ∑ i, x i) + (k:ℝ)*(k+1) * ∑ i, x i^3 := by
  set s := ∑ i, x i with hs
  rcases (Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hx i)).lt_or_eq with hpos | hzero
  · rw [← hs] at hpos
    have hS : (fun i => x i / s) ∈ PCM_S d := by
      refine ⟨fun i => div_nonneg (hx i) hpos.le, ?_⟩
      rw [← Finset.sum_div, ← hs, div_self hpos.ne']
    have h0 := PCM_simplex hk _ hS
    have e : (∑ l, PCM_phi k (x l / s)) * s^3 =
        ∑ i, (s^2 * x i - (2*(k:ℝ)+1)*s*(x i^2) + (k:ℝ)*(k+1)*(x i^3)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      unfold PCM_phi
      field_simp
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, ← hs] at e
    have : 0 ≤ (∑ l, PCM_phi k (x l / s)) * s^3 := mul_nonneg h0 (by positivity)
    rw [e] at this
    nlinarith
  · have hz : ∀ i, x i = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hx i)).1 hzero.symm i (Finset.mem_univ i)
    simp [hs, hz]

def PCM_H : Set (Part 3 → ℝ) := {y | 0 ≤ y ⟨[3],by decide⟩ ∧
      0 ≤ y ⟨[2,1],by decide⟩ - y ⟨[3],by decide⟩ ∧
      ∀ k : ℕ, 1 ≤ k → 0 ≤ y ⟨[1,1,1],by decide⟩ -
        (2*(k:ℝ)+1)*y ⟨[2,1],by decide⟩ + (k:ℝ)*(k+1)*y ⟨[3],by decide⟩}

def PCM_G : Set (Part 3 → ℝ) := {y | ∃ d, 0 < d ∧ ∃ x : Fin d → ℝ,
    (∀ i, 0 ≤ x i) ∧ y = spectralMoments x}

theorem PCM_gen_H {y : Part 3 → ℝ} (hy : y ∈ PCM_G) : y ∈ PCM_H := by
  obtain ⟨d, _, x, hx, rfl⟩ := hy
  refine ⟨?_, ?_, fun k hk => ?_⟩
  · rw [PCM_smA]; exact Finset.sum_nonneg fun i _ => pow_nonneg (hx i) 3
  · rw [PCM_smA, PCM_smB, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_nonneg
    intro i _
    have : x i ≤ ∑ j, x j := Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)
    have e : x i ^ 2 * ∑ j, x j - x i ^ 3 = x i ^ 2 * (∑ j, x j - x i) := by ring
    rw [e]; exact mul_nonneg (sq_nonneg _) (by linarith)
  · rw [PCM_smA, PCM_smB, PCM_smC]
    exact PCM_key hk x hx

theorem PCM_H_closed : IsClosed PCM_H := by
  have : PCM_H = {y : Part 3 → ℝ | 0 ≤ y ⟨[3],by decide⟩} ∩
      {y | 0 ≤ y ⟨[2,1],by decide⟩ - y ⟨[3],by decide⟩} ∩
      ⋂ k : ℕ, ⋂ (_ : 1 ≤ k), {y | 0 ≤ y ⟨[1,1,1],by decide⟩ -
        (2*(k:ℝ)+1)*y ⟨[2,1],by decide⟩ + (k:ℝ)*(k+1)*y ⟨[3],by decide⟩} := by
    ext y; simp [PCM_H, and_assoc]
  rw [this]
  refine IsClosed.inter (IsClosed.inter ?_ ?_)
    (isClosed_iInter fun k => isClosed_iInter fun _ => ?_) <;>
    exact isClosed_le continuous_const (by fun_prop)

theorem PCM_cone_H : finiteCone PCM_G ⊆ PCM_H := by
  rintro v ⟨N, c, u, hcu, rfl⟩
  have ev : ∀ p : Part 3, (∑ i, c i • u i) p = ∑ i, c i * u i p := by
    intro p; simp [Finset.sum_apply]
  have hu : ∀ i, u i ∈ PCM_H := fun i => PCM_gen_H (hcu i).2
  refine ⟨?_, ?_, fun k hk => ?_⟩
  · rw [ev ⟨[3],by decide⟩]; exact Finset.sum_nonneg fun i _ => mul_nonneg (hcu i).1 (hu i).1
  · rw [ev ⟨[3],by decide⟩, ev ⟨[2,1],by decide⟩, ← Finset.sum_sub_distrib]
    apply Finset.sum_nonneg; intro i _
    rw [← mul_sub]; exact mul_nonneg (hcu i).1 (hu i).2.1
  · rw [ev ⟨[3],by decide⟩, ev ⟨[2,1],by decide⟩, ev ⟨[1,1,1],by decide⟩, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_nonneg; intro i _
    have e : c i * u i ⟨[1,1,1],by decide⟩ - (2*(k:ℝ)+1) * (c i * u i ⟨[2,1],by decide⟩)
        + (k:ℝ)*(k+1) * (c i * u i ⟨[3],by decide⟩) = c i * (u i ⟨[1,1,1],by decide⟩ -
        (2*(k:ℝ)+1)*u i ⟨[2,1],by decide⟩ + (k:ℝ)*(k+1)*u i ⟨[3],by decide⟩) := by ring
    rw [e]; exact mul_nonneg (hcu i).1 ((hu i).2.2 k hk)

theorem PCM_consec (m k : ℕ) : 0 ≤ ((m:ℝ) - k) * ((m:ℝ) - k - 1) := by
  rcases le_or_gt m k with h | h
  · have : (m:ℝ) ≤ k := by exact_mod_cast h
    nlinarith
  · have : (k:ℝ) + 1 ≤ m := by exact_mod_cast h
    nlinarith

/-- choose the fan index -/
theorem PCM_index (a b c : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
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

def PCM_one (n : ℕ) : Part 3 → ℝ := spectralMoments (fun _ : Fin n => (1:ℝ))

theorem PCM_oneA (n : ℕ) : PCM_one n ⟨[3],by decide⟩ = n := by simp [PCM_one, PCM_smA]
theorem PCM_oneB (n : ℕ) : PCM_one n ⟨[2,1],by decide⟩ = (n:ℝ)^2 := by
  simp [PCM_one, PCM_smB]; ring
theorem PCM_oneC (n : ℕ) : PCM_one n ⟨[1,1,1],by decide⟩ = (n:ℝ)^3 := by
  simp [PCM_one, PCM_smC]

theorem PCM_one_G (n : ℕ) (hn : 1 ≤ n) : PCM_one n ∈ PCM_G :=
  ⟨n, hn, fun _ => 1, fun _ => zero_le_one, rfl⟩

theorem PCM_zA (α β γ : ℝ) (m m' n : ℕ) :
    (α • PCM_one m + β • PCM_one m' + γ • PCM_one n) ⟨[3],by decide⟩ = α * m + β * m' + γ * n := by
  change α * PCM_one m ⟨[3],by decide⟩ + β * PCM_one m' ⟨[3],by decide⟩
    + γ * PCM_one n ⟨[3],by decide⟩ = _
  rw [PCM_oneA, PCM_oneA, PCM_oneA]

theorem PCM_zB (α β γ : ℝ) (m m' n : ℕ) :
    (α • PCM_one m + β • PCM_one m' + γ • PCM_one n) ⟨[2,1],by decide⟩
      = α * (m:ℝ)^2 + β * (m':ℝ)^2 + γ * (n:ℝ)^2 := by
  change α * PCM_one m ⟨[2,1],by decide⟩ + β * PCM_one m' ⟨[2,1],by decide⟩
    + γ * PCM_one n ⟨[2,1],by decide⟩ = _
  rw [PCM_oneB, PCM_oneB, PCM_oneB]

theorem PCM_zC (α β γ : ℝ) (m m' n : ℕ) :
    (α • PCM_one m + β • PCM_one m' + γ • PCM_one n) ⟨[1,1,1],by decide⟩
      = α * (m:ℝ)^3 + β * (m':ℝ)^3 + γ * (n:ℝ)^3 := by
  change α * PCM_one m ⟨[1,1,1],by decide⟩ + β * PCM_one m' ⟨[1,1,1],by decide⟩
    + γ * PCM_one n ⟨[1,1,1],by decide⟩ = _
  rw [PCM_oneC, PCM_oneC, PCM_oneC]

theorem PCM_H_cone : PCM_H ⊆ closure (finiteCone PCM_G) := by
  intro y hy
  obtain ⟨ha, hba, hk⟩ := hy
  set a := y ⟨[3],by decide⟩ with hadef
  set b := y ⟨[2,1],by decide⟩ with hbdef
  set c := y ⟨[1,1,1],by decide⟩ with hcdef
  obtain ⟨m, hm, h1, h2⟩ := PCM_index a b c ha (by linarith) hk
  have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
  set α := (((m:ℝ)+1)*a - b)/m with hα
  set β := (b - m*a)/((m:ℝ)+1) with hβ
  set δ := c - (2*(m:ℝ)+1)*b + (m:ℝ)*(m+1)*a with hδ
  have hα0 : 0 ≤ α := div_nonneg (by linarith) (by linarith)
  have hβ0 : 0 ≤ β := div_nonneg (by linarith) (by linarith)
  have hδ0 : 0 ≤ δ := hk m hm
  let z : ℕ → Part 3 → ℝ := fun n =>
    α • PCM_one m + β • PCM_one (m+1) + (δ * (1/((n:ℝ)+1))^3) • PCM_one (n+1)
  have hz : ∀ n, z n ∈ finiteCone PCM_G := by
    intro n
    refine ⟨3, ![α, β, δ * (1/((n:ℝ)+1))^3], ![PCM_one m, PCM_one (m+1), PCM_one (n+1)],
      ?_, ?_⟩
    · intro i
      fin_cases i
      · exact ⟨hα0, PCM_one_G m hm⟩
      · exact ⟨hβ0, PCM_one_G (m+1) (by omega)⟩
      · exact ⟨mul_nonneg hδ0 (by positivity), PCM_one_G (n+1) (by omega)⟩
    · simp [z, Fin.sum_univ_three]
  have ht : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto z atTop (nhds y) := by
    rw [tendsto_pi_nhds]
    intro p
    rcases PCM_parts p with rfl | rfl | rfl
    · have e : ∀ n : ℕ, z n ⟨[3],by decide⟩ = a + δ * (1/((n:ℝ)+1))^2 := by
        intro n
        simp only [z]; rw [PCM_zA]
        rw [hα, hβ]; push_cast; field_simp; ring
      simp_rw [e]
      have := (ht.pow 2).const_mul δ |>.const_add a
      simpa using this
    · have e : ∀ n : ℕ, z n ⟨[2,1],by decide⟩ = b + δ * (1/((n:ℝ)+1)) := by
        intro n
        simp only [z]; rw [PCM_zB]
        rw [hα, hβ]; push_cast; field_simp; ring
      simp_rw [e]
      have := (ht.const_mul δ).const_add b
      simpa using this
    · have e : ∀ n : ℕ, z n ⟨[1,1,1],by decide⟩ = c := by
        intro n
        simp only [z]; rw [PCM_zC]
        rw [hα, hβ, hδ]; push_cast; field_simp; ring
      simp_rw [e]
      exact tendsto_const_nhds
  exact mem_closure_of_tendsto hlim (Eventually.of_forall hz)

theorem PCM_cone : psdMom 3 = PCM_H := by
  apply Set.Subset.antisymm
  · exact closure_minimal PCM_cone_H PCM_H_closed
  · exact PCM_H_cone

def PCM_K : Set (Fin 2 → ℝ) := ({0} ∪ {v | ∃ m : ℕ, 1 ≤ m ∧
        v = ![1/(m:ℝ),1/(m:ℝ)^2]})

def PCM_H3 : Set (Fin 2 → ℝ) := {v | 0 ≤ v 1 ∧ v 1 ≤ v 0 ∧
    ∀ k : ℕ, 1 ≤ k → 0 ≤ 1 - (2*(k:ℝ)+1) * v 0 + (k:ℝ)*(k+1) * v 1}

theorem PCM_H3_closed : IsClosed PCM_H3 := by
  have : PCM_H3 = {v : Fin 2 → ℝ | 0 ≤ v 1} ∩ {v | v 1 ≤ v 0} ∩
      ⋂ k : ℕ, ⋂ (_ : 1 ≤ k), {v | 0 ≤ 1 - (2*(k:ℝ)+1) * v 0 + (k:ℝ)*(k+1) * v 1} := by
    ext v; simp [PCM_H3, and_assoc]
  rw [this]
  refine IsClosed.inter (IsClosed.inter ?_ ?_)
    (isClosed_iInter fun k => isClosed_iInter fun _ => ?_)
  · exact isClosed_le continuous_const (by fun_prop)
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · exact isClosed_le continuous_const (by fun_prop)

theorem PCM_H3_convex : Convex ℝ PCM_H3 := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  simp only [PCM_H3, Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine ⟨by positivity, by nlinarith [mul_le_mul_of_nonneg_left hx2 ha,
    mul_le_mul_of_nonneg_left hy2 hb], fun k hk => ?_⟩
  have h1 := mul_nonneg ha (hx3 k hk)
  have h2 := mul_nonneg hb (hy3 k hk)
  have e : 1 - (2*(k:ℝ)+1) * (a * x 0 + b * y 0) + (k:ℝ)*(k+1) * (a * x 1 + b * y 1)
    = a * (1 - (2*(k:ℝ)+1) * x 0 + (k:ℝ)*(k+1) * x 1)
      + b * (1 - (2*(k:ℝ)+1) * y 0 + (k:ℝ)*(k+1) * y 1) + (1 - a - b) := by ring
  rw [e]; linarith

theorem PCM_K_H3 : PCM_K ⊆ PCM_H3 := by
  rintro v (hv | ⟨m, hm, rfl⟩)
  · rw [Set.mem_singleton_iff] at hv
    subst hv
    refine ⟨le_rfl, le_rfl, fun k _ => ?_⟩
    simp
  · have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
    refine ⟨?_, ?_, fun k hk => ?_⟩
    · simp
    · simp
      rw [inv_le_inv₀ (by positivity) (by positivity)]
      nlinarith
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      have e : 1 - (2*(k:ℝ)+1) * (1/(m:ℝ)) + (k:ℝ)*(k+1) * (1/(m:ℝ)^2)
          = (((m:ℝ) - k) * ((m:ℝ) - k - 1)) / (m:ℝ)^2 := by
        field_simp; ring
      rw [e]
      exact div_nonneg (PCM_consec m k) (by positivity)

theorem PCM_slice : {v : Fin 2 → ℝ | ∃ y ∈ PCM_H, y ⟨[1,1,1],by decide⟩ = 1 ∧
      v = ![y ⟨[2,1],by decide⟩,y ⟨[3],by decide⟩]} = closure (convexHull ℝ PCM_K) := by
  apply Set.Subset.antisymm
  · rintro v ⟨y, ⟨ha, hba, hk⟩, hc, rfl⟩
    apply subset_closure
    set a := y ⟨[3],by decide⟩ with hadef
    set b := y ⟨[2,1],by decide⟩ with hbdef
    rw [hc] at hk
    obtain ⟨m, hm, h1, h2⟩ := PCM_index a b 1 ha (by linarith) hk
    have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
    have hmem : ∀ n : ℕ, 1 ≤ n → ![1/(n:ℝ),1/(n:ℝ)^2] ∈ convexHull ℝ PCM_K :=
      fun n hn => subset_convexHull ℝ _ (Or.inr ⟨n, hn, rfl⟩)
    have h0 : (0 : Fin 2 → ℝ) ∈ convexHull ℝ PCM_K :=
      subset_convexHull ℝ _ (Or.inl rfl)
    have hsum := (convex_convexHull ℝ PCM_K).sum_mem (t := Finset.univ)
      (w := ![(m:ℝ)^2 * (((m:ℝ)+1)*a - b), ((m:ℝ)+1)^2 * (b - m*a),
        1 - (2*(m:ℝ)+1)*b + (m:ℝ)*(m+1)*a])
      (z := ![![1/(m:ℝ),1/(m:ℝ)^2], ![1/((m+1:ℕ):ℝ),1/((m+1:ℕ):ℝ)^2], 0])
      (fun i _ => by
        fin_cases i
        · exact mul_nonneg (by positivity) (by linarith)
        · exact mul_nonneg (by positivity) (by linarith)
        · exact hk m hm)
      (by simp [Fin.sum_univ_three]; ring)
      (fun i _ => by
        fin_cases i
        · exact hmem m hm
        · exact hmem (m+1) (by omega)
        · exact h0)
    convert hsum using 1
    ext i
    fin_cases i
    · simp [Fin.sum_univ_three]; field_simp; ring
    · simp [Fin.sum_univ_three]; field_simp; ring
  · apply closure_minimal _ PCM_H3_closed |>.trans
    · rintro v ⟨hv1, hv2, hv3⟩
      refine ⟨fun p => if p.val = [3] then v 1 else if p.val = [2,1] then v 0 else 1,
        ⟨?_, ?_, ?_⟩, ?_, ?_⟩
      · simpa using hv1
      · simpa using hv2
      · intro k hk; simpa using hv3 k hk
      · simp
      · ext i; fin_cases i <;> simp
    · exact convexHull_min PCM_K_H3 PCM_H3_convex

end QAlgorithms.Papers.Independent.Information100.P19

open QAlgorithms.Papers.Independent.Information100.P19 in
theorem solution  :
    psdMom 3 = {y | 0 ≤ y ⟨[3],by decide⟩ ∧
      0 ≤ y ⟨[2,1],by decide⟩ - y ⟨[3],by decide⟩ ∧
      ∀ k : ℕ, 1 ≤ k → 0 ≤ y ⟨[1,1,1],by decide⟩ -
        (2*(k:ℝ)+1)*y ⟨[2,1],by decide⟩ + (k:ℝ)*(k+1)*y ⟨[3],by decide⟩} ∧
    {v : Fin 2 → ℝ | ∃ y ∈ psdMom 3, y ⟨[1,1,1],by decide⟩ = 1 ∧
      v = ![y ⟨[2,1],by decide⟩,y ⟨[3],by decide⟩]} =
      closure (convexHull ℝ ({0} ∪ {v | ∃ m : ℕ, 1 ≤ m ∧
        v = ![1/(m:ℝ),1/(m:ℝ)^2]})) := by
  refine ⟨PCM_cone, ?_⟩
  rw [PCM_cone]
  exact PCM_slice

