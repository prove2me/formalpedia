-- Prove2me | solution 1 for RandomLeadGBS.Diffusion.eq_36
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T10:37:46.322332+00:00
-- url     : https://prove2.me/submissions/e724dbb8-75cc-4135-a320-fac60cd8cc9c

import Mathlib
import Definitions.Def_RandomLeadGBS_Diffusion_Model
import Theorems.Thm_RandomLeadGBS_Diffusion_lemma_4
import Theorems.Thm_RandomLeadGBS_Diffusion_eq_31
import Theorems.Thm_RandomLeadGBS_Diffusion_corollary_6
import Theorems.Thm_RandomLeadGBS_Diffusion_lemma_8

open Filter Topology
open RandomLeadGBS.Diffusion

namespace GBSEq36

/-! ### Support of a stationary distribution -/

lemma orderStep_ge (P : Params) (r : ℝ) (y : ℤ) (z : ℕ) :
    ⌈truncTarget P r y⌉ ≤ ((orderStep P r y z : ℕ) : ℤ) := by
  simp only [orderStep]
  rw [Int.ceil_sub_natCast]
  have h := Int.self_le_toNat (⌈truncTarget P r y⌉ - (z : ℤ))
  push_cast
  omega

/-- A stationary distribution vanishes on states with `Z < ⌈T(Y)⌉` (they are never entered). -/
lemma support (P : Params) (r : ℝ) (hr : 0 < r) (hβ : 0 < P.β) (p : State → ℝ)
    (hp : IsStationary P r p) (s : State) (hs : ((s.2 : ℕ) : ℤ) < ⌈truncTarget P r s.1⌉) :
    p s = 0 := by
  have hb := hp.2.2.2.2 s
  have h0 : ∀ s0 : State, p s0 * rate P r s0 s = 0 := by
    intro s0
    have : rate P r s0 s = 0 := by
      unfold rate
      rw [if_neg, if_neg]
      · simp
      · rintro ⟨-, h⟩
        have := orderStep_ge P r (s0.1 + 1) (s0.2 - 1)
        rw [h] at hs
        simp only [afterItem] at hs
        omega
      · intro h
        have := orderStep_ge P r (s0.1 - 1) s0.2
        rw [h] at hs
        simp only [afterCustomer] at hs
        omega
    rw [this, mul_zero]
  simp only [h0, tsum_zero] at hb
  have hpos : 0 < exitRate P r s := by
    unfold exitRate; positivity
  rcases mul_eq_zero.mp hb.symm with h | h
  · exact h
  · linarith

/-! ### Tail-sum formula on `ℤ`-valued observables -/

lemma tail {ι : Type*} (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : Summable w) (y : ι → ℤ) :
    ∑' i, ENNReal.ofReal (w i * ((y i).toNat : ℝ)) =
      ∑' k : ℕ, ENNReal.ofReal (∑' i, if (k : ℤ) < y i then w i else 0) := by
  have h1 : ∀ i, ENNReal.ofReal (w i * ((y i).toNat : ℝ)) =
      ∑' k : ℕ, if (k : ℤ) < y i then ENNReal.ofReal (w i) else 0 := by
    intro i
    rw [tsum_eq_sum (s := Finset.range (y i).toNat)]
    · rw [Finset.sum_congr rfl (fun k hk => if_pos (Int.lt_toNat.mp (Finset.mem_range.mp hk)))]
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul (hw i),
        ENNReal.ofReal_natCast, mul_comm]
    · intro k hk
      rw [if_neg]
      intro h
      exact hk (Finset.mem_range.mpr (Int.lt_toNat.mpr h))
  rw [tsum_congr h1, ENNReal.tsum_comm]
  congr 1; funext k
  rw [ENNReal.ofReal_tsum_of_nonneg (fun i => by split_ifs; exact hw i; exact le_rfl)
    (Summable.of_nonneg_of_le (fun i => by split_ifs; exact hw i; exact le_rfl)
      (fun i => by split_ifs; exact le_rfl; exact hw i) hs)]
  congr 1; funext i
  split_ifs <;> simp

lemma summable_of_ofReal {ι : Type*} (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    (h : ∑' i, ENNReal.ofReal (f i) ≠ ⊤) : Summable f := by
  have := ENNReal.summable_toReal h
  simpa [ENNReal.toReal_ofReal (hf _)] using this

lemma tsum_le_of_ofReal {ι κ : Type*} (f : ι → ℝ) (g : κ → ℝ) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hsg : Summable g) (h : ∑' i, ENNReal.ofReal (f i) ≤ ∑' i, ENNReal.ofReal (g i)) :
    Summable f ∧ ∑' i, f i ≤ ∑' i, g i := by
  have hsf : Summable f := summable_of_ofReal f hf
    (ne_top_of_le_ne_top (by rw [← ENNReal.ofReal_tsum_of_nonneg hg hsg]; exact ENNReal.ofReal_ne_top) h)
  rw [← ENNReal.ofReal_tsum_of_nonneg hf hsf, ← ENNReal.ofReal_tsum_of_nonneg hg hsg] at h
  exact ⟨hsf, (ENNReal.ofReal_le_ofReal_iff (tsum_nonneg hg)).mp h⟩

lemma ind_summable {ι : Type*} (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : Summable w)
    (c : ι → Prop) [DecidablePred c] : Summable (fun i => if c i then w i else 0) :=
  Summable.of_nonneg_of_le (fun i => by split_ifs; exact hw i; exact le_rfl)
    (fun i => by split_ifs; exact le_rfl; exact hw i) hs

/-- Upper tails: `Ŷ ≤st Y` gives `E Ŷ⁺ ≤ E Y⁺`. -/
lemma pos_cmp (p : State → ℝ) (q : ℤ → ℝ) (hpn : ∀ s, 0 ≤ p s) (hps : Summable p)
    (hqn : ∀ j, 0 ≤ q j) (hqs : Summable q)
    (h8 : ∀ x : ℝ, ∑' j : ℤ, (if x < (j : ℝ) then q j else 0) ≤
      ∑' s : State, (if x < (s.1 : ℝ) then p s else 0))
    (hsp : Summable (fun s : State => p s * ((s.1.toNat : ℕ) : ℝ))) :
    Summable (fun j : ℤ => q j * ((j.toNat : ℕ) : ℝ)) ∧
      ∑' j : ℤ, q j * ((j.toNat : ℕ) : ℝ) ≤ ∑' s : State, p s * ((s.1.toNat : ℕ) : ℝ) := by
  apply tsum_le_of_ofReal _ _ (fun j => mul_nonneg (hqn j) (Nat.cast_nonneg _))
    (fun s => mul_nonneg (hpn s) (Nat.cast_nonneg _)) hsp
  rw [tail q hqn hqs (fun j => j), tail p hpn hps (fun s => s.1)]
  refine ENNReal.tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal ?_
  have := h8 (k : ℝ)
  have e1 : ∀ j : ℤ, ((k : ℝ) < (j : ℝ)) = ((k : ℤ) < j) := fun j => by
    apply propext; constructor <;> intro h <;> exact_mod_cast h
  simp only [e1] at this
  exact this

/-- Lower tails: `Ŷ ≤st Y` gives `E Y⁻ ≤ E Ŷ⁻`. -/
lemma neg_cmp (p : State → ℝ) (q : ℤ → ℝ) (hpn : ∀ s, 0 ≤ p s) (hps : Summable p)
    (hp1 : ∑' s, p s = 1)
    (hqn : ∀ j, 0 ≤ q j) (hqs : Summable q) (hq1 : ∑' j, q j = 1)
    (h8 : ∀ x : ℝ, ∑' j : ℤ, (if x < (j : ℝ) then q j else 0) ≤
      ∑' s : State, (if x < (s.1 : ℝ) then p s else 0))
    (hsq : Summable (fun j : ℤ => q j * (((-j).toNat : ℕ) : ℝ))) :
    Summable (fun s : State => p s * (((-s.1).toNat : ℕ) : ℝ)) ∧
      ∑' s : State, p s * (((-s.1).toNat : ℕ) : ℝ) ≤ ∑' j : ℤ, q j * (((-j).toNat : ℕ) : ℝ) := by
  apply tsum_le_of_ofReal _ _ (fun s => mul_nonneg (hpn s) (Nat.cast_nonneg _))
    (fun j => mul_nonneg (hqn j) (Nat.cast_nonneg _)) hsq
  rw [tail p hpn hps (fun s => -s.1), tail q hqn hqs (fun j => -j)]
  refine ENNReal.tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal ?_
  have := h8 (-(k : ℝ) - 1)
  -- complement form
  have cp : ∀ s : State, (if (k : ℤ) < -s.1 then p s else 0) =
      p s - (if -(k : ℝ) - 1 < (s.1 : ℝ) then p s else 0) := by
    intro s
    by_cases h : (k : ℤ) < -s.1
    · have : ¬ (-(k : ℝ) - 1 < (s.1 : ℝ)) := by
        intro h'
        have : -(k : ℤ) - 1 < s.1 := by exact_mod_cast h'
        omega
      rw [if_pos h, if_neg this]; ring
    · have : (-(k : ℝ) - 1 < (s.1 : ℝ)) := by
        have : -(k : ℤ) - 1 < s.1 := by omega
        exact_mod_cast this
      rw [if_neg h, if_pos this]; ring
  have cq : ∀ j : ℤ, (if (k : ℤ) < -j then q j else 0) =
      q j - (if -(k : ℝ) - 1 < (j : ℝ) then q j else 0) := by
    intro j
    by_cases h : (k : ℤ) < -j
    · have : ¬ (-(k : ℝ) - 1 < (j : ℝ)) := by
        intro h'
        have : -(k : ℤ) - 1 < j := by exact_mod_cast h'
        omega
      rw [if_pos h, if_neg this]; ring
    · have : (-(k : ℝ) - 1 < (j : ℝ)) := by
        have : -(k : ℤ) - 1 < j := by omega
        exact_mod_cast this
      rw [if_neg h, if_pos this]; ring
  rw [tsum_congr cp, tsum_congr cq, Summable.tsum_sub hps (ind_summable p hpn hps _),
    Summable.tsum_sub hqs (ind_summable q hqn hqs _), hp1, hq1]
  linarith

/-! ### Pointwise facts about the truncated target -/

lemma T_nonneg (P : Params) (r : ℝ) (y : ℤ) : 0 ≤ truncTarget P r y := le_max_right _ _

lemma T_le (P : Params) (r : ℝ) (hM : 0 ≤ Xstar P r + P.f r) (y : ℤ) :
    truncTarget P r y ≤ Xstar P r + P.f r :=
  max_le (min_le_right _ _) hM

lemma target_eq (P : Params) (hx : ∀ r, P.xs r = 0) (r : ℝ) (y : ℤ) :
    target P r y = Xstar P r - (P.γ : ℝ) * y := by
  simp [target, hx r]

lemma up_bound (P : Params) (hx : ∀ r, P.xs r = 0) (r : ℝ) (y : ℤ) :
    (P.γ : ℝ) * y ≤ Xstar P r - truncTarget P r y + max ((P.γ : ℝ) * y - Xstar P r) 0 := by
  have ht := target_eq P hx r y
  unfold truncTarget
  rw [ht]
  rcases le_total 0 (Xstar P r - (P.γ : ℝ) * y) with h | h
  · have : max (min (Xstar P r - (P.γ : ℝ) * y) (Xstar P r + P.f r)) 0 ≤
        Xstar P r - (P.γ : ℝ) * y :=
      max_le (min_le_left _ _) h
    have := le_max_right ((P.γ : ℝ) * y - Xstar P r) 0
    linarith
  · have : max (min (Xstar P r - (P.γ : ℝ) * y) (Xstar P r + P.f r)) 0 = 0 :=
      max_eq_right (le_trans (min_le_left _ _) h)
    rw [this]
    have := le_max_left ((P.γ : ℝ) * y - Xstar P r) 0
    linarith

lemma low_bound (P : Params) (hx : ∀ r, P.xs r = 0) (r : ℝ) (hM : 0 ≤ Xstar P r + P.f r)
    (y : ℤ) :
    Xstar P r - truncTarget P r y - max (-P.f r - (P.γ : ℝ) * y) 0 ≤ (P.γ : ℝ) * y := by
  have ht := target_eq P hx r y
  unfold truncTarget
  rw [ht]
  rcases le_total (Xstar P r - (P.γ : ℝ) * y) (Xstar P r + P.f r) with h | h
  · rw [min_eq_left h]
    have := le_max_left (Xstar P r - (P.γ : ℝ) * y) 0
    have := le_max_right (-P.f r - (P.γ : ℝ) * y) 0
    linarith
  · rw [min_eq_right h, max_eq_left hM]
    have := le_max_left (-P.f r - (P.γ : ℝ) * y) 0
    linarith

lemma gapDt_lower (P : Params) (hx : ∀ r, P.xs r = 0) (r : ℝ) (s : State) :
    (P.γ : ℝ) * s.1 - Xstar P r - 1 ≤ gapDt P r s := by
  unfold gapDt
  have h1 := Int.ceil_lt_add_one (min (truncTarget P r s.1) (target P r s.1))
  have h2 := min_le_right (truncTarget P r s.1) (target P r s.1)
  simp only [target_eq P hx r s.1] at h1 h2 ⊢
  have : (0 : ℝ) ≤ s.2 := Nat.cast_nonneg _
  linarith

lemma gapDt_nonneg (P : Params) (r : ℝ) (s : State)
    (hs : ⌈truncTarget P r s.1⌉ ≤ ((s.2 : ℕ) : ℤ)) : 0 ≤ gapDt P r s := by
  unfold gapDt
  have h1 : ⌈min (truncTarget P r s.1) (target P r s.1)⌉ ≤ ⌈truncTarget P r s.1⌉ :=
    Int.ceil_mono (min_le_left _ _)
  have : ⌈min (truncTarget P r s.1) (target P r s.1)⌉ ≤ ((s.2 : ℕ) : ℤ) := le_trans h1 hs
  have : ((⌈min (truncTarget P r s.1) (target P r s.1)⌉ : ℤ) : ℝ) ≤ ((((s.2 : ℕ) : ℤ)) : ℝ) := by
    exact_mod_cast this
  push_cast at this
  linarith

lemma int_split (y : ℤ) : (y : ℝ) = ((y.toNat : ℕ) : ℝ) - (((-y).toNat : ℕ) : ℝ) := by
  have := Int.toNat_sub_toNat_neg y
  have h : ((((y.toNat : ℕ) : ℤ) - (((-y).toNat : ℕ) : ℤ) : ℤ) : ℝ) = (y : ℝ) := by
    rw [this]
  push_cast at h
  linarith

lemma toNat_le_max (y : ℤ) : ((y.toNat : ℕ) : ℝ) = max (y : ℝ) 0 := by
  rcases le_total 0 y with h | h
  · rw [max_eq_left (by exact_mod_cast h)]
    have : ((y.toNat : ℕ) : ℤ) = y := Int.toNat_of_nonneg h
    exact_mod_cast this
  · rw [max_eq_right (by exact_mod_cast h)]
    simp [Int.toNat_eq_zero.mpr h]

lemma toNat_neg_eq (y : ℤ) : (((-y).toNat : ℕ) : ℝ) = max (-(y : ℝ)) 0 := by
  rw [toNat_le_max]; push_cast; rfl

end GBSEq36

open GBSEq36

theorem solution (P : Params) (hP : P.Standing) (hx : ∀ r, P.xs r = 0)
    (p : ℝ → State → ℝ) (hp : ∀ᶠ r in atTop, IsStationary P r (p r))
    (q : ℝ → ℤ → ℝ) (hq : ∀ᶠ r in atTop, IsArtStationary P r (q r)) :
    (∀ᶠ r in atTop, Summable (fun s : State => p r s * (s.1 : ℝ)) ∧
      Summable (fun j : ℤ => q r j * (j : ℝ))) ∧
    Tendsto (fun r => ∑' s : State, p r s * ((s.1 : ℝ) / Real.sqrt r) -
      ∑' j : ℤ, q r j * ((j : ℝ) / Real.sqrt r)) atTop (𝓝 0) := by
  have hP' := hP
  obtain ⟨hβ, hγ, hfpos, -, hfsqrt⟩ := hP'
  have hγr : (1 : ℝ) ≤ P.γ := by exact_mod_cast hγ
  obtain ⟨C4, hC4, r4, h4⟩ := lemma_4 P hP hx
  obtain ⟨C31, hC31, r31, h31⟩ := eq_31 P hP hx
  have h6 := corollary_6 P hP hx
  obtain ⟨c1, hc1, r6, h6'⟩ := h6 1 one_pos
  have hpos : ∀ᶠ r : ℝ in atTop, 0 < r := eventually_gt_atTop 0
  /- The core estimate at a fixed large `r`. -/
  have key : ∀ r : ℝ, 0 < r → r ≥ r4 → r ≥ r31 → r ≥ r6 →
      IsStationary P r (p r) → IsArtStationary P r (q r) →
      Summable (fun s : State => p r s * (s.1 : ℝ)) ∧ Summable (fun j : ℤ => q r j * (j : ℝ)) ∧
      0 ≤ ∑' s : State, p r s * (s.1 : ℝ) - ∑' j : ℤ, q r j * (j : ℝ) ∧
      (P.γ : ℝ) * (∑' s : State, p r s * (s.1 : ℝ) - ∑' j : ℤ, q r j * (j : ℝ)) ≤
        C31 + C4 + 2 + ∑' j : ℤ, q r j * max (-P.f r - (P.γ : ℝ) * j) 0 ∧
      Summable (fun j : ℤ => q r j * max (-P.f r - (P.γ : ℝ) * j) 0) := by
    intro r hr hr4 hr31 hr6 hpr hqr
    set pr := p r with hpr_def
    set qr := q r with hqr_def
    have hXs : 0 < Xstar P r := by unfold Xstar; positivity
    have hM : 0 ≤ Xstar P r + P.f r := by linarith [hfpos r]
    have hpr' := hpr
    have hqr' := hqr
    obtain ⟨hpn, hps, hp1, -, -⟩ := hpr'
    obtain ⟨hqn, hqs, hq1, -, -⟩ := hqr'
    obtain ⟨hsD, hsDt, -, hDtC⟩ := h4 r hr4 pr hpr
    obtain ⟨hsTq, hsTp, h31r⟩ := h31 r hr31 pr qr hpr hqr
    obtain ⟨hs6, -⟩ := h6' r hr6 qr hqr
    have hsqrt : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
    -- (1) E Y⁺ < ∞ from the gap D̃
    have hsYp : Summable (fun s : State => pr s * ((s.1.toNat : ℕ) : ℝ)) := by
      refine Summable.of_nonneg_of_le (fun s => mul_nonneg (hpn s) (Nat.cast_nonneg _))
        (fun s => ?_) (hsDt.add (hps.mul_right (Xstar P r + 1)))
      by_cases hz : ((s.2 : ℕ) : ℤ) < ⌈truncTarget P r s.1⌉
      · rw [support P r hr hβ pr hpr s hz]; simp
      · push Not at hz
        have h0 := gapDt_nonneg P r s hz
        have h1 := gapDt_lower P hx r s
        rw [← mul_add]
        apply mul_le_mul_of_nonneg_left _ (hpn s)
        rw [toNat_le_max]
        apply max_le
        · have : (s.1 : ℝ) ≤ (P.γ : ℝ) * s.1 ∨ (s.1 : ℝ) < 0 := by
            rcases le_or_gt 0 (s.1 : ℝ) with h | h
            · left; nlinarith
            · right; exact h
          rcases this with h | h <;> linarith
        · linarith
    -- (2) E Ŷ⁻ < ∞ from Corollary 6
    have hsQn : Summable (fun j : ℤ => qr j * (((-j).toNat : ℕ) : ℝ)) := by
      have hb : Summable (fun j : ℤ =>
          Real.sqrt r * (qr j * max (-c1 - (j : ℝ) / Real.sqrt r) 0) + Real.sqrt r * c1 * qr j) :=
        (hs6.mul_left _).add (hqs.mul_left _)
      refine Summable.of_nonneg_of_le (fun j => mul_nonneg (hqn j) (Nat.cast_nonneg _))
        (fun j => ?_) hb
      rw [toNat_neg_eq]
      have h1 : max (-(j : ℝ)) 0 ≤ Real.sqrt r * max (-c1 - (j : ℝ) / Real.sqrt r) 0 +
          Real.sqrt r * c1 := by
        apply max_le
        · have : -c1 - (j : ℝ) / Real.sqrt r ≤ max (-c1 - (j : ℝ) / Real.sqrt r) 0 :=
            le_max_left _ _
          have e : Real.sqrt r * (-c1 - (j : ℝ) / Real.sqrt r) = -(Real.sqrt r * c1) - j := by
            field_simp
          nlinarith
        · have := le_max_right (-c1 - (j : ℝ) / Real.sqrt r) 0
          positivity
      have := mul_le_mul_of_nonneg_left h1 (hqn j)
      nlinarith
    -- (3) tail comparisons from Lemma 8
    obtain ⟨h8a, -⟩ := lemma_8 P hP hx r hr pr hpr qr hqr
    obtain ⟨hsQp, hQpY⟩ := pos_cmp pr qr hpn hps hqn hqs h8a hsYp
    obtain ⟨hsYn, hYnQ⟩ := neg_cmp pr qr hpn hps hp1 hqn hqs hq1 h8a hsQn
    have eY : (fun s : State => pr s * (s.1 : ℝ)) =
        fun s => pr s * ((s.1.toNat : ℕ) : ℝ) - pr s * (((-s.1).toNat : ℕ) : ℝ) := by
      funext s; rw [int_split s.1]; ring
    have eQ : (fun j : ℤ => qr j * (j : ℝ)) =
        fun j => qr j * ((j.toNat : ℕ) : ℝ) - qr j * (((-j).toNat : ℕ) : ℝ) := by
      funext j; rw [int_split j]; ring
    have hsY : Summable (fun s : State => pr s * (s.1 : ℝ)) := by rw [eY]; exact hsYp.sub hsYn
    have hsQ : Summable (fun j : ℤ => qr j * (j : ℝ)) := by rw [eQ]; exact hsQp.sub hsQn
    have hlow : 0 ≤ ∑' s : State, pr s * (s.1 : ℝ) - ∑' j : ℤ, qr j * (j : ℝ) := by
      rw [eY, eQ, Summable.tsum_sub hsYp hsYn, Summable.tsum_sub hsQp hsQn]
      linarith
    -- (4) the error term of the artificial chain is summable
    have hsE : Summable (fun j : ℤ => qr j * max (-P.f r - (P.γ : ℝ) * j) 0) := by
      refine Summable.of_nonneg_of_le
        (fun j => mul_nonneg (hqn j) (le_max_right _ _)) (fun j => ?_) (hsQn.mul_left (P.γ : ℝ))
      rw [toNat_neg_eq]
      have : max (-P.f r - (P.γ : ℝ) * j) 0 ≤ (P.γ : ℝ) * max (-(j : ℝ)) 0 := by
        apply max_le
        · have := le_max_left (-(j : ℝ)) 0
          have := hfpos r
          nlinarith
        · have := le_max_right (-(j : ℝ)) 0
          positivity
      have := mul_le_mul_of_nonneg_left this (hqn j)
      linarith
    -- (5) upper bound for the GBS chain: γ E Y ≤ X∗ − E T + E D̃ + 1
    have hsT : Summable (fun s : State => pr s * truncTarget P r s.1) :=
      Summable.of_nonneg_of_le (fun s => mul_nonneg (hpn s) (T_nonneg P r _))
        (fun s => mul_le_mul_of_nonneg_left (T_le P r hM _) (hpn s))
        (hps.mul_right (Xstar P r + P.f r))
    have hsTh : Summable (fun j : ℤ => qr j * truncTarget P r j) :=
      Summable.of_nonneg_of_le (fun j => mul_nonneg (hqn j) (T_nonneg P r _))
        (fun j => mul_le_mul_of_nonneg_left (T_le P r hM _) (hqn j))
        (hqs.mul_right (Xstar P r + P.f r))
    have hup : (P.γ : ℝ) * ∑' s : State, pr s * (s.1 : ℝ) ≤
        Xstar P r - ∑' s : State, pr s * truncTarget P r s.1 + ∑' s, pr s * gapDt P r s + 1 := by
      have hpt : ∀ s : State, (P.γ : ℝ) * (pr s * (s.1 : ℝ)) ≤
          Xstar P r * pr s - pr s * truncTarget P r s.1 + pr s * gapDt P r s + pr s := by
        intro s
        by_cases hz : ((s.2 : ℕ) : ℤ) < ⌈truncTarget P r s.1⌉
        · rw [support P r hr hβ pr hpr s hz]; simp
        · push Not at hz
          have h0 := gapDt_nonneg P r s hz
          have h1 := gapDt_lower P hx r s
          have h2 := up_bound P hx r s.1
          have h3 : max ((P.γ : ℝ) * s.1 - Xstar P r) 0 ≤ gapDt P r s + 1 :=
            max_le (by linarith) (by linarith)
          have := mul_le_mul_of_nonneg_left (le_trans h2 (by linarith :
            Xstar P r - truncTarget P r s.1 + max ((P.γ : ℝ) * s.1 - Xstar P r) 0 ≤
              Xstar P r - truncTarget P r s.1 + (gapDt P r s + 1))) (hpn s)
          nlinarith
      have := Summable.tsum_le_tsum hpt (hsY.mul_left _)
        ((((hps.mul_left (Xstar P r)).sub hsT).add hsDt).add hps)
      rw [tsum_mul_left, Summable.tsum_add (((hps.mul_left (Xstar P r)).sub hsT).add hsDt) hps,
        Summable.tsum_add ((hps.mul_left (Xstar P r)).sub hsT) hsDt,
        Summable.tsum_sub (hps.mul_left (Xstar P r)) hsT, tsum_mul_left, hp1] at this
      linarith
    -- (6) lower bound for the artificial chain
    have hlo : Xstar P r - ∑' j : ℤ, qr j * truncTarget P r j -
        ∑' j : ℤ, qr j * max (-P.f r - (P.γ : ℝ) * j) 0 ≤
        (P.γ : ℝ) * ∑' j : ℤ, qr j * (j : ℝ) := by
      have hpt : ∀ j : ℤ, Xstar P r * qr j - qr j * truncTarget P r j -
          qr j * max (-P.f r - (P.γ : ℝ) * j) 0 ≤ (P.γ : ℝ) * (qr j * (j : ℝ)) := by
        intro j
        have := mul_le_mul_of_nonneg_left (low_bound P hx r hM j) (hqn j)
        nlinarith
      have := Summable.tsum_le_tsum hpt (((hqs.mul_left (Xstar P r)).sub hsTh).sub hsE)
        (hsQ.mul_left _)
      rw [tsum_mul_left, Summable.tsum_sub ((hqs.mul_left (Xstar P r)).sub hsTh) hsE,
        Summable.tsum_sub (hqs.mul_left (Xstar P r)) hsTh, tsum_mul_left, hq1] at this
      linarith
    -- (7) T versus ⌈T⌉
    have hTq : ∑' j : ℤ, qr j * truncTarget P r j ≤
        ∑' j : ℤ, qr j * ((⌈truncTarget P r j⌉ : ℤ) : ℝ) :=
      Summable.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left (Int.le_ceil _) (hqn j))
        hsTh hsTq
    have hTp : ∑' s : State, pr s * ((⌈truncTarget P r s.1⌉ : ℤ) : ℝ) - 1 ≤
        ∑' s : State, pr s * truncTarget P r s.1 := by
      have := Summable.tsum_le_tsum
        (fun s : State => (by
          have h := Int.ceil_lt_add_one (truncTarget P r s.1)
          have := mul_le_mul_of_nonneg_left h.le (hpn s)
          linarith : pr s * ((⌈truncTarget P r s.1⌉ : ℤ) : ℝ) ≤
            pr s * truncTarget P r s.1 + pr s))
        hsTp (hsT.add hps)
      rw [Summable.tsum_add hsT hps, hp1] at this
      linarith
    refine ⟨hsY, hsQ, hlow, ?_, hsE⟩
    rw [mul_sub]
    linarith
  refine ⟨?_, ?_⟩
  · filter_upwards [hpos, hp, hq, eventually_ge_atTop r4, eventually_ge_atTop r31,
      eventually_ge_atTop r6] with r hr hpr hqr h4r h31r h6r
    obtain ⟨a, b, -⟩ := key r hr h4r h31r h6r hpr hqr
    exact ⟨a, b⟩
  · -- the scaled difference tends to zero
    rw [tendsto_order]
    constructor
    · intro a ha
      filter_upwards [hpos, hp, hq, eventually_ge_atTop r4, eventually_ge_atTop r31,
        eventually_ge_atTop r6] with r hr hpr hqr h4r h31r h6r
      obtain ⟨hsY, hsQ, hlow, -⟩ := key r hr h4r h31r h6r hpr hqr
      have hsqrt : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
      have e : ∑' s : State, p r s * ((s.1 : ℝ) / Real.sqrt r) -
          ∑' j : ℤ, q r j * ((j : ℝ) / Real.sqrt r) =
          (∑' s : State, p r s * (s.1 : ℝ) - ∑' j : ℤ, q r j * (j : ℝ)) / Real.sqrt r := by
        simp only [mul_div_assoc']
        rw [tsum_div_const, tsum_div_const, sub_div]
      rw [e]
      have := div_nonneg hlow hsqrt.le
      linarith
    · intro a ha
      -- choose ε = a/3 in Corollary 6
      obtain ⟨c, hc, r6', h6c⟩ := h6 (a / 3) (by linarith)
      have hγpos : (0 : ℝ) < P.γ := by linarith
      have hf_big : ∀ᶠ r in atTop, c * (P.γ : ℝ) ≤ P.f r / Real.sqrt r :=
        hfsqrt.eventually (eventually_ge_atTop _)
      have hC : Tendsto (fun r => (C31 + C4 + 2) / ((P.γ : ℝ) * Real.sqrt r)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.const_mul_atTop hγpos)
      have hC' : ∀ᶠ r in atTop, (C31 + C4 + 2) / ((P.γ : ℝ) * Real.sqrt r) < a / 3 :=
        hC.eventually (gt_mem_nhds (by linarith))
      filter_upwards [hpos, hp, hq, eventually_ge_atTop r4, eventually_ge_atTop r31,
        eventually_ge_atTop r6, eventually_ge_atTop r6', hf_big, hC'] with
        r hr hpr hqr h4r h31r h6r h6r' hfr hCr
      obtain ⟨hsY, hsQ, hlow, hupb, hsE⟩ := key r hr h4r h31r h6r hpr hqr
      obtain ⟨hs6, h6le⟩ := h6c r h6r' (q r) hqr
      have hsqrt : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
      have hqn := hqr.1
      -- the error term is at most γ √r · a/3
      have hE : ∑' j : ℤ, q r j * max (-P.f r - (P.γ : ℝ) * j) 0 ≤
          (P.γ : ℝ) * Real.sqrt r * (a / 3) := by
        have hfr' : c * (P.γ : ℝ) * Real.sqrt r ≤ P.f r := by
          rw [le_div_iff₀ hsqrt] at hfr; linarith
        have hpt : ∀ j : ℤ, q r j * max (-P.f r - (P.γ : ℝ) * j) 0 ≤
            (P.γ : ℝ) * Real.sqrt r * (q r j * max (-c - (j : ℝ) / Real.sqrt r) 0) := by
          intro j
          have : max (-P.f r - (P.γ : ℝ) * j) 0 ≤
              (P.γ : ℝ) * Real.sqrt r * max (-c - (j : ℝ) / Real.sqrt r) 0 := by
            apply max_le
            · have h1 := le_max_left (-c - (j : ℝ) / Real.sqrt r) 0
              have e : (P.γ : ℝ) * Real.sqrt r * (-c - (j : ℝ) / Real.sqrt r) =
                  -(c * (P.γ : ℝ) * Real.sqrt r) - (P.γ : ℝ) * j := by
                field_simp
              have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (P.γ : ℝ) * Real.sqrt r)
              linarith
            · have := le_max_right (-c - (j : ℝ) / Real.sqrt r) 0
              positivity
          have := mul_le_mul_of_nonneg_left this (hqn j)
          linarith
        have := Summable.tsum_le_tsum hpt hsE (hs6.mul_left _)
        rw [tsum_mul_left] at this
        have h3 := mul_le_mul_of_nonneg_left h6le (by positivity : (0 : ℝ) ≤ (P.γ : ℝ) * Real.sqrt r)
        linarith
      have e : ∑' s : State, p r s * ((s.1 : ℝ) / Real.sqrt r) -
          ∑' j : ℤ, q r j * ((j : ℝ) / Real.sqrt r) =
          (∑' s : State, p r s * (s.1 : ℝ) - ∑' j : ℤ, q r j * (j : ℝ)) / Real.sqrt r := by
        simp only [mul_div_assoc']
        rw [tsum_div_const, tsum_div_const, sub_div]
      rw [e, div_lt_iff₀ hsqrt]
      set Δ := ∑' s : State, p r s * (s.1 : ℝ) - ∑' j : ℤ, q r j * (j : ℝ)
      have hCr' : C31 + C4 + 2 < a / 3 * ((P.γ : ℝ) * Real.sqrt r) := by
        rw [div_lt_iff₀ (by positivity)] at hCr; linarith
      have : (P.γ : ℝ) * Δ < (P.γ : ℝ) * (a * Real.sqrt r) := by nlinarith
      exact lt_of_mul_lt_mul_left this hγpos.le
