-- Prove2me | solution 1 for RobustDP.Discounted.lemma2_policy_evaluation
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:15:01.205719+00:00
-- url     : https://prove2.me/submissions/b6f26ea9-3e61-45da-aa8e-5104e6dc3511

import Mathlib
import Definitions.Def_RobustDP_Discounted_Model
import Definitions.Def_RobustDP_Discounted_Value
import Definitions.Def_RobustDP_Discounted_Bellman

set_option autoImplicit false
open RobustDP.Discounted

namespace MMA

section expect

variable {X : Type*}

lemma summable_toReal (p : PMF X) : Summable fun x => (p x).toReal :=
  ENNReal.summable_toReal p.tsum_coe_ne_top

lemma tsum_toReal (p : PMF X) : ∑' x, (p x).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun a => p.apply_ne_top a), p.tsum_coe]; simp

lemma summable_expect (p : PMF X) (f : X → ℝ) (C : ℝ) (hf : ∀ x, |f x| ≤ C) :
    Summable fun x => (p x).toReal * f x := by
  refine Summable.of_norm_bounded ((summable_toReal p).mul_right C) (fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  exact mul_le_mul_of_nonneg_left (hf x) ENNReal.toReal_nonneg

lemma expect_const (p : PMF X) (c : ℝ) :
    RobustDP.FiniteHorizon.expect p (fun _ => c) = c := by
  unfold RobustDP.FiniteHorizon.expect
  rw [tsum_mul_right, tsum_toReal, one_mul]

lemma expect_le_add (p : PMF X) (f g : X → ℝ) (C D : ℝ) (hf : ∀ x, |f x| ≤ C)
    (hg : ∀ x, |g x| ≤ D) (c : ℝ) (h : ∀ x, f x ≤ g x + c) :
    RobustDP.FiniteHorizon.expect p f ≤ RobustDP.FiniteHorizon.expect p g + c := by
  unfold RobustDP.FiniteHorizon.expect
  have h1 := summable_expect p f C hf
  have h2 := summable_expect p g D hg
  have h3 : Summable fun x => (p x).toReal * c := (summable_toReal p).mul_right c
  calc ∑' x, (p x).toReal * f x ≤ ∑' x, ((p x).toReal * g x + (p x).toReal * c) := by
        refine h1.tsum_le_tsum (fun x => ?_) (h2.add h3)
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left (h x) ENNReal.toReal_nonneg
    _ = _ := by rw [h2.tsum_add h3, tsum_mul_right, tsum_toReal, one_mul]

lemma abs_expect_le (p : PMF X) (f : X → ℝ) (C : ℝ) (hf : ∀ x, |f x| ≤ C) :
    |RobustDP.FiniteHorizon.expect p f| ≤ C := by
  obtain ⟨x0, _⟩ := p.support_nonempty
  have h0 : (0:ℝ) ≤ C := le_trans (abs_nonneg _) (hf x0)
  rw [abs_le]
  constructor
  · have := expect_le_add p (fun _ => -C) f C C (fun _ => by rw [abs_neg]; exact (abs_of_nonneg h0).le) hf 0
      (fun x => by have := (abs_le.mp (hf x)).1; linarith)
    rw [expect_const] at this; linarith
  · have := expect_le_add p f (fun _ => C) C C hf (fun _ => (abs_of_nonneg h0).le) 0
      (fun x => by have := (abs_le.mp (hf x)).2; linarith)
    rw [expect_const] at this; linarith

end expect

section Qlemmas

variable {S A : Type*} [Countable S] [Countable A]

lemma Q_abs_le (M : Model S A) (R : ℝ) (hR : ∀ s, ∀ a ∈ M.Aset s, ∀ s', |M.r s a s'| ≤ R)
    (U : S → ℝ) (C : ℝ) (hU : ∀ s, |U s| ≤ C) (s : S) (a : A) (ha : a ∈ M.Aset s) :
    |Q M U s a| ≤ R + M.lam * C := by
  have hb : ∀ s', |M.r s a s' + M.lam * U s'| ≤ R + M.lam * C := by
    intro s'
    calc |M.r s a s' + M.lam * U s'| ≤ |M.r s a s'| + |M.lam * U s'| := abs_add_le _ _
      _ ≤ R + M.lam * C := by
        rw [abs_mul, abs_of_pos M.lam_pos]
        exact add_le_add (hR s a ha s') (mul_le_mul_of_nonneg_left (hU s') M.lam_pos.le)
  haveI : Nonempty (M.P s a) := (M.P_nonempty s a ha).to_subtype
  have hall : ∀ p : M.P s a, |RobustDP.FiniteHorizon.expect p.1 (fun s' => M.r s a s' + M.lam * U s')|
      ≤ R + M.lam * C := fun p => abs_expect_le p.1 _ _ hb
  have hbdd : BddBelow (Set.range fun p : M.P s a =>
      RobustDP.FiniteHorizon.expect p.1 (fun s' => M.r s a s' + M.lam * U s')) :=
    ⟨-(R + M.lam * C), by rintro _ ⟨p, rfl⟩; exact (abs_le.mp (hall p)).1⟩
  rw [abs_le]
  constructor
  · exact le_ciInf (fun p => (abs_le.mp (hall p)).1)
  · obtain ⟨p⟩ := ‹Nonempty (M.P s a)›
    exact (ciInf_le hbdd p).trans (abs_le.mp (hall p)).2

lemma Q_le_Q_add (M : Model S A) (R : ℝ) (hR : ∀ s, ∀ a ∈ M.Aset s, ∀ s', |M.r s a s'| ≤ R)
    (U W : S → ℝ) (C : ℝ) (hU : ∀ s, |U s| ≤ C) (hW : ∀ s, |W s| ≤ C) (c : ℝ)
    (h : ∀ s, U s ≤ W s + c) (s : S) (a : A) (ha : a ∈ M.Aset s) :
    Q M U s a ≤ Q M W s a + M.lam * c := by
  have hb : ∀ (V : S → ℝ), (∀ s, |V s| ≤ C) → ∀ s', |M.r s a s' + M.lam * V s'| ≤ R + M.lam * C := by
    intro V hV s'
    calc |M.r s a s' + M.lam * V s'| ≤ |M.r s a s'| + |M.lam * V s'| := abs_add_le _ _
      _ ≤ R + M.lam * C := by
        rw [abs_mul, abs_of_pos M.lam_pos]
        exact add_le_add (hR s a ha s') (mul_le_mul_of_nonneg_left (hV s') M.lam_pos.le)
  haveI : Nonempty (M.P s a) := (M.P_nonempty s a ha).to_subtype
  have hbddU : BddBelow (Set.range fun p : M.P s a =>
      RobustDP.FiniteHorizon.expect p.1 (fun s' => M.r s a s' + M.lam * U s')) :=
    ⟨-(R + M.lam * C), by rintro _ ⟨p, rfl⟩; exact (abs_le.mp (abs_expect_le p.1 _ _ (hb U hU))).1⟩
  have : Q M U s a - M.lam * c ≤ Q M W s a := by
    refine le_ciInf (fun p => ?_)
    have h1 : RobustDP.FiniteHorizon.expect p.1 (fun s' => M.r s a s' + M.lam * U s') ≤
        RobustDP.FiniteHorizon.expect p.1 (fun s' => M.r s a s' + M.lam * W s') + M.lam * c := by
      refine expect_le_add p.1 _ _ _ _ (hb U hU) (hb W hW) _ (fun s' => ?_)
      have := mul_le_mul_of_nonneg_left (h s') M.lam_pos.le
      rw [mul_add] at this
      linarith
    have h2 : Q M U s a ≤ RobustDP.FiniteHorizon.expect p.1 (fun s' => M.r s a s' + M.lam * U s') :=
      ciInf_le hbddU p
    linarith
  linarith

end Qlemmas

section exp2

variable {X Y : Type*}

lemma summable_expect' (p : PMF X) (f : X → ℝ) (C : ℝ) (hf : ∀ x ∈ p.support, |f x| ≤ C) :
    Summable fun x => (p x).toReal * f x := by
  refine Summable.of_norm_bounded ((summable_toReal p).mul_right C) (fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  by_cases hx : x ∈ p.support
  · exact mul_le_mul_of_nonneg_left (hf x hx) ENNReal.toReal_nonneg
  · rw [PMF.mem_support_iff, not_not] at hx; simp [hx]

lemma expect_le_add' (p : PMF X) (f g : X → ℝ) (C D : ℝ) (hf : ∀ x ∈ p.support, |f x| ≤ C)
    (hg : ∀ x ∈ p.support, |g x| ≤ D) (c : ℝ) (h : ∀ x ∈ p.support, f x ≤ g x + c) :
    RobustDP.FiniteHorizon.expect p f ≤ RobustDP.FiniteHorizon.expect p g + c := by
  unfold RobustDP.FiniteHorizon.expect
  have h1 := summable_expect' p f C hf
  have h2 := summable_expect' p g D hg
  have h3 : Summable fun x => (p x).toReal * c := (summable_toReal p).mul_right c
  calc ∑' x, (p x).toReal * f x ≤ ∑' x, ((p x).toReal * g x + (p x).toReal * c) := by
        refine h1.tsum_le_tsum (fun x => ?_) (h2.add h3)
        rw [← mul_add]
        by_cases hx : x ∈ p.support
        · exact mul_le_mul_of_nonneg_left (h x hx) ENNReal.toReal_nonneg
        · rw [PMF.mem_support_iff, not_not] at hx; simp [hx]
    _ = _ := by rw [h2.tsum_add h3, tsum_mul_right, tsum_toReal, one_mul]

lemma abs_expect_le' (p : PMF X) (f : X → ℝ) (C : ℝ) (hf : ∀ x ∈ p.support, |f x| ≤ C) :
    |RobustDP.FiniteHorizon.expect p f| ≤ C := by
  obtain ⟨x0, hx0⟩ := p.support_nonempty
  have h0 : (0:ℝ) ≤ C := le_trans (abs_nonneg _) (hf x0 hx0)
  rw [abs_le]
  constructor
  · have := expect_le_add' p (fun _ => -C) f C C
      (fun _ _ => by rw [abs_neg]; exact (abs_of_nonneg h0).le) hf 0
      (fun x hx => by have := (abs_le.mp (hf x hx)).1; linarith)
    rw [expect_const] at this; linarith
  · have := expect_le_add' p f (fun _ => C) C C hf (fun _ _ => (abs_of_nonneg h0).le) 0
      (fun x hx => by have := (abs_le.mp (hf x hx)).2; linarith)
    rw [expect_const] at this; linarith

lemma expect_congr' (p : PMF X) (f g : X → ℝ) (h : ∀ x ∈ p.support, f x = g x) :
    RobustDP.FiniteHorizon.expect p f = RobustDP.FiniteHorizon.expect p g := by
  unfold RobustDP.FiniteHorizon.expect
  refine tsum_congr (fun x => ?_)
  by_cases hx : x ∈ p.support
  · rw [h x hx]
  · rw [PMF.mem_support_iff, not_not] at hx; simp [hx]

lemma expect_add' (p : PMF X) (f g : X → ℝ) (C D : ℝ) (hf : ∀ x ∈ p.support, |f x| ≤ C)
    (hg : ∀ x ∈ p.support, |g x| ≤ D) :
    RobustDP.FiniteHorizon.expect p (fun x => f x + g x) =
      RobustDP.FiniteHorizon.expect p f + RobustDP.FiniteHorizon.expect p g := by
  unfold RobustDP.FiniteHorizon.expect
  rw [← (summable_expect' p f C hf).tsum_add (summable_expect' p g D hg)]
  exact tsum_congr (fun x => mul_add _ _ _)

lemma expect_mul_left' (p : PMF X) (c : ℝ) (f : X → ℝ) :
    RobustDP.FiniteHorizon.expect p (fun x => c * f x) = c * RobustDP.FiniteHorizon.expect p f := by
  unfold RobustDP.FiniteHorizon.expect
  rw [← tsum_mul_left]
  exact tsum_congr (fun x => by ring)

lemma expect_pure (a : X) (g : X → ℝ) :
    RobustDP.FiniteHorizon.expect (PMF.pure a) g = g a := by
  unfold RobustDP.FiniteHorizon.expect
  rw [tsum_eq_single a]
  · simp
  · intro b hb; simp [PMF.pure_apply, hb]

lemma expect_bind (p : PMF X) (f : X → PMF Y) (g : Y → ℝ) (C : ℝ)
    (hg : ∀ x ∈ p.support, ∀ y ∈ (f x).support, |g y| ≤ C) :
    RobustDP.FiniteHorizon.expect (p.bind f) g =
      RobustDP.FiniteHorizon.expect p (fun x => RobustDP.FiniteHorizon.expect (f x) g) := by
  classical
  have key : ∀ y, ((p.bind f) y).toReal = ∑' x, (p x).toReal * (f x y).toReal := by
    intro y
    rw [PMF.bind_apply, ENNReal.tsum_toReal_eq]
    · exact tsum_congr (fun x => ENNReal.toReal_mul)
    · intro x; exact ENNReal.mul_ne_top (p.apply_ne_top x) (PMF.apply_ne_top _ _)
  unfold RobustDP.FiniteHorizon.expect
  -- the double family
  set F : X → Y → ℝ := fun x y => (p x).toReal * (f x y).toReal * g y with hF
  have hsum_a : Summable (fun z : X × Y => (p z.1).toReal * (f z.1 z.2).toReal) := by
    have : Summable (fun z : X × Y => (p z.1 * f z.1 z.2).toReal) := by
      refine ENNReal.summable_toReal ?_
      rw [ENNReal.tsum_prod (f := fun a b => p a * (f a) b)]
      have : ∀ x, ∑' y, p x * f x y = p x := by
        intro x; rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
      simp only [this, p.tsum_coe]; exact ENNReal.one_ne_top
    simpa [ENNReal.toReal_mul] using this
  have hsum : Summable (Function.uncurry F) := by
    refine Summable.of_norm_bounded (hsum_a.mul_right C) (fun z => ?_)
    obtain ⟨x, y⟩ := z
    simp only [Function.uncurry_apply_pair, hF]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg,
      abs_of_nonneg ENNReal.toReal_nonneg]
    by_cases hx : x ∈ p.support
    · by_cases hy : y ∈ (f x).support
      · have := hg x hx y hy
        calc (p x).toReal * (f x y).toReal * |g y| ≤ (p x).toReal * (f x y).toReal * C :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ = _ := rfl
      · rw [PMF.mem_support_iff, not_not] at hy; simp [hy]
    · rw [PMF.mem_support_iff, not_not] at hx; simp [hx]
  calc ∑' y, ((p.bind f) y).toReal * g y
      = ∑' y, ∑' x, F x y := by
        refine tsum_congr (fun y => ?_)
        rw [key, ← tsum_mul_right]
    _ = ∑' x, ∑' y, F x y := hsum.tsum_comm
    _ = _ := by
        refine tsum_congr (fun x => ?_)
        rw [← tsum_mul_left]
        exact tsum_congr (fun y => by simp only [hF]; ring)

lemma expect_map (p : PMF X) (k : X → Y) (g : Y → ℝ) (C : ℝ)
    (hg : ∀ x ∈ p.support, |g (k x)| ≤ C) :
    RobustDP.FiniteHorizon.expect (p.map k) g =
      RobustDP.FiniteHorizon.expect p (fun x => g (k x)) := by
  show RobustDP.FiniteHorizon.expect (p.bind (PMF.pure ∘ k)) g = _
  rw [expect_bind p _ g C]
  · exact expect_congr' _ _ _ (fun x _ => by simp [expect_pure])
  · intro x hx y hy
    simp only [Function.comp, PMF.support_pure, Set.mem_singleton_iff] at hy
    rw [hy]; exact hg x hx

end exp2

section path

variable {S A : Type*} [Countable S] [Countable A]

lemma lastReward_extend (M : Model S A) {n : ℕ} (h : History S A n) (a : A) (s' : S) :
    lastReward M (h.extend a s') = M.r h.cur a s' := by
  simp [lastReward, History.extend, Fin.snoc_last, History.cur]

lemma cur_extend {n : ℕ} (h : History S A n) (a : A) (s' : S) : (h.extend a s').cur = s' := rfl

lemma mem_support_pathLaw_succ (d : (n : ℕ) → History S A n → PMF A)
    (σ : (n : ℕ) → History S A n → A → PMF S) (s : S) (n : ℕ) (h : History S A (n + 1)) :
    h ∈ (pathLaw d σ s (n + 1)).support ↔
      ∃ h' ∈ (pathLaw d σ s n).support, ∃ a ∈ (d n h').support, ∃ s' ∈ (σ n h' a).support,
        h'.extend a s' = h := by
  simp only [pathLaw, PMF.mem_support_bind_iff, PMF.mem_support_map_iff]

/-- one step of the path law -/
lemma expect_pathLaw_succ (d : (n : ℕ) → History S A n → PMF A)
    (σ : (n : ℕ) → History S A n → A → PMF S) (s : S) (n : ℕ) (G : History S A (n + 1) → ℝ)
    (C : ℝ)
    (hG : ∀ h ∈ (pathLaw d σ s n).support, ∀ a ∈ (d n h).support, ∀ s' ∈ (σ n h a).support,
      |G (h.extend a s')| ≤ C) :
    RobustDP.FiniteHorizon.expect (pathLaw d σ s (n + 1)) G =
      RobustDP.FiniteHorizon.expect (pathLaw d σ s n) (fun h =>
        RobustDP.FiniteHorizon.expect (d n h) (fun a =>
          RobustDP.FiniteHorizon.expect (σ n h a) (fun s' => G (h.extend a s')))) := by
  have e : pathLaw d σ s (n + 1) = (pathLaw d σ s n).bind fun h =>
      (d n h).bind fun a => (σ n h a).map fun s' => h.extend a s' := rfl
  rw [e, expect_bind _ _ G C]
  · refine expect_congr' _ _ _ (fun h hh => ?_)
    rw [expect_bind _ _ G C]
    · refine expect_congr' _ _ _ (fun a ha => ?_)
      exact expect_map _ _ G C (fun s' hs' => hG h hh a ha s' hs')
    · intro a ha y hy
      rw [PMF.mem_support_map_iff] at hy
      obtain ⟨s', hs', rfl⟩ := hy
      exact hG h hh a ha s' hs'
  · intro h hh y hy
    rw [PMF.mem_support_bind_iff] at hy
    obtain ⟨a, ha, hy⟩ := hy
    rw [PMF.mem_support_map_iff] at hy
    obtain ⟨s', hs', rfl⟩ := hy
    exact hG h hh a ha s' hs'

end path

section core

variable {S A : Type*} [Countable S] [Countable A]

lemma rw_bound (M : Model S A) (R : ℝ) (hR : ∀ s, ∀ a ∈ M.Aset s, ∀ s', |M.r s a s'| ≤ R)
    (W : S → ℝ) (C : ℝ) (hW : ∀ s, |W s| ≤ C) (s : S) (a : A) (ha : a ∈ M.Aset s) (s' : S) :
    |M.r s a s' + M.lam * W s'| ≤ R + M.lam * C := by
  calc |M.r s a s' + M.lam * W s'| ≤ |M.r s a s'| + |M.lam * W s'| := abs_add_le _ _
    _ ≤ R + M.lam * C := by
      rw [abs_mul, abs_of_pos M.lam_pos]
      exact add_le_add (hR s a ha s') (mul_le_mul_of_nonneg_left (hW s') M.lam_pos.le)

lemma Q_le_expect (M : Model S A) (R : ℝ) (hR : ∀ s, ∀ a ∈ M.Aset s, ∀ s', |M.r s a s'| ≤ R)
    (W : S → ℝ) (C : ℝ) (hW : ∀ s, |W s| ≤ C) (s : S) (a : A) (ha : a ∈ M.Aset s)
    (p : PMF S) (hp : p ∈ M.P s a) :
    Q M W s a ≤ RobustDP.FiniteHorizon.expect p (fun s' => M.r s a s' + M.lam * W s') := by
  have hbdd : BddBelow (Set.range fun q : M.P s a =>
      RobustDP.FiniteHorizon.expect q.1 (fun s' => M.r s a s' + M.lam * W s')) :=
    ⟨-(R + M.lam * C), by
      rintro _ ⟨q, rfl⟩
      exact (abs_le.mp (abs_expect_le' q.1 _ _ (fun s' _ => rw_bound M R hR W C hW s a ha s'))).1⟩
  exact ciInf_le hbdd (⟨p, hp⟩ : M.P s a)

lemma exists_near (M : Model S A) (R : ℝ) (hR : ∀ s, ∀ a ∈ M.Aset s, ∀ s', |M.r s a s'| ≤ R)
    (W : S → ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : StaticAdversary M, ∀ s, ∀ a ∈ M.Aset s,
      RobustDP.FiniteHorizon.expect (p.1 s a) (fun s' => M.r s a s' + M.lam * W s') ≤
        Q M W s a + ε := by
  classical
  have : ∀ (s : S) (a : A), ∃ q : PMF S, a ∈ M.Aset s → q ∈ M.P s a ∧
      RobustDP.FiniteHorizon.expect q (fun s' => M.r s a s' + M.lam * W s') ≤ Q M W s a + ε := by
    intro s a
    by_cases ha : a ∈ M.Aset s
    · haveI : Nonempty (M.P s a) := (M.P_nonempty s a ha).to_subtype
      have hlt : Q M W s a < Q M W s a + ε := lt_add_of_pos_right _ hε
      obtain ⟨q, hq⟩ := exists_lt_of_ciInf_lt hlt
      exact ⟨q.1, fun _ => ⟨q.2, hq.le⟩⟩
    · exact ⟨PMF.pure s, fun h => absurd h ha⟩
  choose q hq using this
  exact ⟨⟨q, fun s a ha => (hq s a ha).1⟩, fun s a ha => (hq s a ha).2⟩

variable (M : Model S A) (d : (n : ℕ) → History S A n → PMF A)
  (σ : (n : ℕ) → History S A n → A → PMF S) (s : S)

noncomputable def eT (n : ℕ) : ℝ :=
  RobustDP.FiniteHorizon.expect (pathLaw d σ s (n + 1)) (lastReward M)

noncomputable def wT (W : S → ℝ) (n : ℕ) : ℝ :=
  RobustDP.FiniteHorizon.expect (pathLaw d σ s n) (fun h => W h.cur)

noncomputable def Psi (W : S → ℝ) (n : ℕ) (h : History S A n) : ℝ :=
  RobustDP.FiniteHorizon.expect (d n h) (fun a =>
    RobustDP.FiniteHorizon.expect (σ n h a) (fun s' => M.r h.cur a s' + M.lam * W s'))

variable {M d σ s}

section bounds
variable (R : ℝ) (hR : ∀ s, ∀ a ∈ M.Aset s, ∀ s', |M.r s a s'| ≤ R)
  (hd : ∀ n h, ∀ a ∈ (d n h).support, a ∈ M.Aset h.cur)
include hR hd

lemma lastReward_bound (n : ℕ) :
    ∀ h ∈ (pathLaw d σ s (n + 1)).support, |lastReward M h| ≤ R := by
  intro h hh
  rw [mem_support_pathLaw_succ] at hh
  obtain ⟨h', _, a, ha, s', _, rfl⟩ := hh
  rw [lastReward_extend]
  exact hR _ a (hd n h' a ha) s'

lemma eT_abs (n : ℕ) : |eT M d σ s n| ≤ R :=
  abs_expect_le' _ _ R (lastReward_bound R hR hd n)

lemma Psi_abs (W : S → ℝ) (C : ℝ) (hW : ∀ s, |W s| ≤ C) (n : ℕ) (h : History S A n) :
    |Psi M d σ W n h| ≤ R + M.lam * C :=
  abs_expect_le' _ _ _ (fun a ha => abs_expect_le' _ _ _
    (fun s' _ => rw_bound M R hR W C hW h.cur a (hd n h a ha) s'))

lemma one_step (W : S → ℝ) (C : ℝ) (hW : ∀ s, |W s| ≤ C) (n : ℕ) :
    eT M d σ s n + M.lam * wT d σ s W (n + 1) =
      RobustDP.FiniteHorizon.expect (pathLaw d σ s n) (Psi M d σ W n) := by
  have hlam : ∀ h ∈ (pathLaw d σ s (n + 1)).support, |M.lam * W h.cur| ≤ M.lam * C := by
    intro h _
    rw [abs_mul, abs_of_pos M.lam_pos]
    exact mul_le_mul_of_nonneg_left (hW _) M.lam_pos.le
  calc eT M d σ s n + M.lam * wT d σ s W (n + 1)
      = RobustDP.FiniteHorizon.expect (pathLaw d σ s (n + 1))
          (fun h => lastReward M h + M.lam * W h.cur) := by
        rw [expect_add' _ _ _ R (M.lam * C) (lastReward_bound R hR hd n) hlam,
          expect_mul_left']
        rfl
    _ = _ := by
        rw [expect_pathLaw_succ d σ s n _ (R + M.lam * C)]
        · refine expect_congr' _ _ _ (fun h _ => ?_)
          unfold Psi
          refine expect_congr' _ _ _ (fun a _ => ?_)
          refine expect_congr' _ _ _ (fun s' _ => ?_)
          rw [lastReward_extend]
          rfl
        · intro h _ a ha s' _
          rw [lastReward_extend]
          exact rw_bound M R hR W C hW h.cur a (hd n h a ha) s'

end bounds


end core

section tele

variable {S A : Type*} [Countable S] [Countable A] {M : Model S A}
  {d : (n : ℕ) → History S A n → PMF A}
  {σ : (n : ℕ) → History S A n → A → PMF S} {s : S}

noncomputable def Phi (M : Model S A) (d : (n : ℕ) → History S A n → PMF A)
    (σ : (n : ℕ) → History S A n → A → PMF S) (s : S) (W : S → ℝ) (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.range n, M.lam ^ t * eT M d σ s t + M.lam ^ n * wT d σ s W n

lemma Phi_zero (W : S → ℝ) : Phi M d σ s W 0 = W s := by
  unfold Phi wT
  have : pathLaw d σ s 0 = PMF.pure (History.init s) := rfl
  rw [this, expect_pure]
  simp [History.init, History.cur]

lemma Phi_succ (W : S → ℝ) (n : ℕ) :
    Phi M d σ s W (n + 1) - Phi M d σ s W n =
      M.lam ^ n * (eT M d σ s n + M.lam * wT d σ s W (n + 1) - wT d σ s W n) := by
  unfold Phi
  rw [Finset.sum_range_succ]
  ring

lemma tendsto_Phi (R : ℝ) (hR : ∀ s, ∀ a ∈ M.Aset s, ∀ s', |M.r s a s'| ≤ R)
    (hd : ∀ n h, ∀ a ∈ (d n h).support, a ∈ M.Aset h.cur)
    (W : S → ℝ) (C : ℝ) (hW : ∀ s, |W s| ≤ C) :
    Filter.Tendsto (Phi M d σ s W) Filter.atTop (nhds (discountedReward M d σ s)) := by
  have hsum : Summable fun t => M.lam ^ t * eT M d σ s t := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one M.lam_pos.le M.lam_lt_one).mul_right R) (fun t => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos M.lam_pos t)]
    exact mul_le_mul_of_nonneg_left (eT_abs (σ := σ) (s := s) R hR hd t) (pow_pos M.lam_pos t).le
  have h1 := hsum.hasSum.tendsto_sum_nat
  have h2 : Filter.Tendsto (fun n : ℕ => M.lam ^ n * wT d σ s W n) Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm (a := fun n : ℕ => M.lam ^ n * C) (fun n => ?_) ?_
    · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos M.lam_pos n)]
      exact mul_le_mul_of_nonneg_left
        (abs_expect_le' _ _ C (fun h _ => hW _)) (pow_pos M.lam_pos n).le
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one M.lam_pos.le M.lam_lt_one).mul_const C
  have := h1.add h2
  rw [add_zero] at this
  exact this

lemma discounted_abs_le (R : ℝ) (hR : ∀ s, ∀ a ∈ M.Aset s, ∀ s', |M.r s a s'| ≤ R)
    (hd : ∀ n h, ∀ a ∈ (d n h).support, a ∈ M.Aset h.cur) :
    |discountedReward M d σ s| ≤ R / (1 - M.lam) := by
  have hg : Summable fun t : ℕ => M.lam ^ t * R :=
    (summable_geometric_of_lt_one M.lam_pos.le M.lam_lt_one).mul_right R
  have hsum : Summable fun t => M.lam ^ t * eT M d σ s t := by
    refine Summable.of_norm_bounded hg (fun t => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos M.lam_pos t)]
    exact mul_le_mul_of_nonneg_left (eT_abs (σ := σ) (s := s) R hR hd t) (pow_pos M.lam_pos t).le
  have hgs : ∑' t : ℕ, M.lam ^ t * R = R / (1 - M.lam) := by
    rw [tsum_mul_right, tsum_geometric_of_lt_one M.lam_pos.le M.lam_lt_one]; ring
  have hgs' : Summable fun t : ℕ => M.lam ^ t * (-R) := hg.neg.congr (fun t => by ring)
  have hgn : ∑' t : ℕ, M.lam ^ t * (-R) = -(R / (1 - M.lam)) := by
    rw [tsum_mul_right, tsum_geometric_of_lt_one M.lam_pos.le M.lam_lt_one]; ring
  unfold discountedReward
  rw [abs_le]
  constructor
  · rw [← hgn]
    refine hgs'.tsum_le_tsum (fun t => ?_) hsum
    have := (abs_le.mp (eT_abs (σ := σ) (s := s) R hR hd t)).1
    exact mul_le_mul_of_nonneg_left this (pow_pos M.lam_pos t).le
  · rw [← hgs]
    refine hsum.tsum_le_tsum (fun t => ?_) hg
    have := (abs_le.mp (eT_abs (σ := σ) (s := s) R hR hd t)).2
    exact mul_le_mul_of_nonneg_left this (pow_pos M.lam_pos t).le

/-- lower bound -/
lemma lower_bound (R : ℝ) (hR : ∀ s, ∀ a ∈ M.Aset s, ∀ s', |M.r s a s'| ≤ R)
    (hd : ∀ n h, ∀ a ∈ (d n h).support, a ∈ M.Aset h.cur)
    (hσ : ∀ n h a, a ∈ M.Aset h.cur → σ n h a ∈ M.P h.cur a)
    (W : S → ℝ) (C : ℝ) (hW : ∀ s, |W s| ≤ C)
    (HL : ∀ n (h : History S A n), W h.cur ≤
      RobustDP.FiniteHorizon.expect (d n h) (fun a => Q M W h.cur a)) :
    W s ≤ discountedReward M d σ s := by
  have hstep : ∀ n, wT d σ s W n ≤ eT M d σ s n + M.lam * wT d σ s W (n + 1) := by
    intro n
    rw [one_step R hR hd W C hW n]
    unfold wT
    have := expect_le_add' (pathLaw d σ s n) (fun h => W h.cur) (Psi M d σ W n) C (R + M.lam * C)
      (fun h _ => hW _) (fun h _ => Psi_abs R hR hd W C hW n h) 0 (fun h _ => ?_)
    · simpa using this
    · rw [add_zero]
      refine (HL n h).trans ?_
      have := expect_le_add' (d n h) (fun a => Q M W h.cur a) (fun a =>
        RobustDP.FiniteHorizon.expect (σ n h a) (fun s' => M.r h.cur a s' + M.lam * W s'))
        (R + M.lam * C) (R + M.lam * C)
        (fun a ha => Q_abs_le M R hR W C hW h.cur a (hd n h a ha))
        (fun a ha => abs_expect_le' _ _ _ (fun s' _ => rw_bound M R hR W C hW h.cur a (hd n h a ha) s'))
        0 (fun a ha => by
          rw [add_zero]
          exact Q_le_expect M R hR W C hW h.cur a (hd n h a ha) _ (hσ n h a (hd n h a ha)))
      simpa [Psi] using this
  have hmono : Monotone (Phi M d σ s W) := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    have := Phi_succ (M := M) (d := d) (σ := σ) (s := s) W n
    have h2 := hstep n
    have h3 : 0 ≤ M.lam ^ n * (eT M d σ s n + M.lam * wT d σ s W (n + 1) - wT d σ s W n) :=
      mul_nonneg (pow_pos M.lam_pos n).le (by linarith)
    linarith
  refine ge_of_tendsto' (tendsto_Phi (σ := σ) (s := s) R hR hd W C hW) (fun n => ?_)
  rw [← Phi_zero (M := M) (d := d) (σ := σ) (s := s) W]
  exact hmono (Nat.zero_le n)

/-- upper bound -/
lemma upper_bound (R : ℝ) (hR : ∀ s, ∀ a ∈ M.Aset s, ∀ s', |M.r s a s'| ≤ R)
    (hd : ∀ n h, ∀ a ∈ (d n h).support, a ∈ M.Aset h.cur)
    (W : S → ℝ) (C : ℝ) (hW : ∀ s, |W s| ≤ C) (ε : ℝ) (hε : 0 ≤ ε)
    (hσ' : ∀ n (h : History S A n) a, a ∈ M.Aset h.cur →
      RobustDP.FiniteHorizon.expect (σ n h a) (fun s' => M.r h.cur a s' + M.lam * W s') ≤
        Q M W h.cur a + ε)
    (HU : ∀ n (h : History S A n),
      RobustDP.FiniteHorizon.expect (d n h) (fun a => Q M W h.cur a) ≤ W h.cur) :
    discountedReward M d σ s ≤ W s + ε / (1 - M.lam) := by
  have hstep : ∀ n, eT M d σ s n + M.lam * wT d σ s W (n + 1) ≤ wT d σ s W n + ε := by
    intro n
    rw [one_step R hR hd W C hW n]
    unfold wT
    refine expect_le_add' (pathLaw d σ s n) (Psi M d σ W n) (fun h => W h.cur) (R + M.lam * C) C
      (fun h _ => Psi_abs R hR hd W C hW n h) (fun h _ => hW _) ε (fun h _ => ?_)
    have := expect_le_add' (d n h) (fun a =>
        RobustDP.FiniteHorizon.expect (σ n h a) (fun s' => M.r h.cur a s' + M.lam * W s'))
        (fun a => Q M W h.cur a) (R + M.lam * C) (R + M.lam * C)
        (fun a ha => abs_expect_le' _ _ _ (fun s' _ => rw_bound M R hR W C hW h.cur a (hd n h a ha) s'))
        (fun a ha => Q_abs_le M R hR W C hW h.cur a (hd n h a ha))
        ε (fun a ha => hσ' n h a (hd n h a ha))
    have h2 := HU n h
    unfold Psi
    linarith
  have hbound : ∀ n, Phi M d σ s W n ≤ W s + ε * ∑ t ∈ Finset.range n, M.lam ^ t := by
    intro n
    induction n with
    | zero => simp [Phi_zero]
    | succ n ih =>
      have := Phi_succ (M := M) (d := d) (σ := σ) (s := s) W n
      have h2 := hstep n
      have h3 : M.lam ^ n * (eT M d σ s n + M.lam * wT d σ s W (n + 1) - wT d σ s W n) ≤
          M.lam ^ n * ε := mul_le_mul_of_nonneg_left (by linarith) (pow_pos M.lam_pos n).le
      rw [Finset.sum_range_succ]
      nlinarith
  have hgeo : ∑ t ∈ Finset.range 0, M.lam ^ t ≤ 0 := by simp
  refine le_of_tendsto' (tendsto_Phi (σ := σ) (s := s) R hR hd W C hW) (fun n => ?_)
  refine (hbound n).trans ?_
  have hs : ∑ t ∈ Finset.range n, M.lam ^ t ≤ 1 / (1 - M.lam) := by
    refine (Summable.sum_le_tsum _ (fun _ _ => (pow_pos M.lam_pos _).le)
      (summable_geometric_of_lt_one M.lam_pos.le M.lam_lt_one)).trans ?_
    rw [tsum_geometric_of_lt_one M.lam_pos.le M.lam_lt_one, one_div]
  calc W s + ε * ∑ t ∈ Finset.range n, M.lam ^ t ≤ W s + ε * (1 / (1 - M.lam)) := by
        have := mul_le_mul_of_nonneg_left hs hε
        linarith
    _ = W s + ε / (1 - M.lam) := by rw [mul_one_div]

end tele

section banach

variable {S : Type*} [Countable S]

lemma exists_fixed (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1) (Γ : (S → ℝ) → (S → ℝ))
    (hb : ∀ U, IsBounded U → IsBounded (Γ U))
    (hc : ∀ U W, IsBounded U → IsBounded W → ∀ c, 0 ≤ c → (∀ s, |U s - W s| ≤ c) →
      ∀ s, |Γ U s - Γ W s| ≤ lam * c) :
    ∃ U, IsBounded U ∧ Γ U = U := by
  have hbd : ∀ f : lp (fun _ : S => ℝ) ⊤, IsBounded (⇑f) := by
    intro f
    obtain ⟨C, hC⟩ := memℓp_infty_iff.mp f.2
    exact ⟨C, fun s => by simpa using hC ⟨s, rfl⟩⟩
  have hmem : ∀ U : S → ℝ, IsBounded U → Memℓp U ⊤ := by
    rintro U ⟨C, hC⟩
    exact memℓp_infty ⟨C, by rintro _ ⟨s, rfl⟩; simpa using hC s⟩
  let G : lp (fun _ : S => ℝ) ⊤ → lp (fun _ : S => ℝ) ⊤ :=
    fun f => ⟨Γ f, hmem _ (hb _ (hbd f))⟩
  have hG : ContractingWith ⟨lam, h0.le⟩ G := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul (fun f g => ?_)⟩
    · show (⟨lam, h0.le⟩ : NNReal) < 1
      exact_mod_cast h1
    · rw [dist_eq_norm, dist_eq_norm]
      refine lp.norm_le_of_forall_le (mul_nonneg h0.le (norm_nonneg _)) (fun s => ?_)
      have := hc f g (hbd f) (hbd g) ‖f - g‖ (norm_nonneg _)
        (fun s => by simpa using lp.norm_apply_le_norm (by simp) (f - g) s) s
      have e : ‖(G f - G g) s‖ = |Γ f s - Γ g s| := by
        rw [lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs]
      rw [e]
      exact this
  refine ⟨⇑(ContractingWith.fixedPoint G hG), hbd _, ?_⟩
  have := ContractingWith.fixedPoint_isFixedPt hG
  exact congrArg (fun f : lp (fun _ : S => ℝ) ⊤ => (f : S → ℝ)) this

lemma fixed_unique (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1) (Γ : (S → ℝ) → (S → ℝ))
    (hc : ∀ U W, IsBounded U → IsBounded W → ∀ c, 0 ≤ c → (∀ s, |U s - W s| ≤ c) →
      ∀ s, |Γ U s - Γ W s| ≤ lam * c)
    (U W : S → ℝ) (hU : IsBounded U) (hW : IsBounded W) (hUf : Γ U = U) (hWf : Γ W = W) :
    U = W := by
  obtain ⟨CU, hCU⟩ := hU
  obtain ⟨CW, hCW⟩ := hW
  have hbdd : BddAbove (Set.range fun s => |U s - W s|) :=
    ⟨CU + CW, by
      rintro _ ⟨s, rfl⟩
      calc |U s - W s| ≤ |U s| + |W s| := abs_sub _ _
        _ ≤ CU + CW := add_le_add (hCU s) (hCW s)⟩
  set c := ⨆ s, |U s - W s| with hc0
  have hc1 : 0 ≤ c := Real.iSup_nonneg (fun s => abs_nonneg _)
  have hle : ∀ s, |U s - W s| ≤ c := fun s => le_ciSup hbdd s
  have h2 : c ≤ lam * c := by
    refine Real.iSup_le (fun s => ?_) (mul_nonneg h0.le hc1)
    have := hc U W ⟨CU, hCU⟩ ⟨CW, hCW⟩ c hc1 hle s
    rwa [hUf, hWf] at this
  have h3 : c ≤ 0 := by nlinarith
  funext s
  have := hle s
  have h4 : |U s - W s| ≤ 0 := this.trans h3
  have := abs_nonneg (U s - W s)
  have : |U s - W s| = 0 := le_antisymm h4 this
  linarith [abs_eq_zero.mp this]

end banach

section Vlemmas

variable {S A : Type*} [Countable S] [Countable A] (M : Model S A)

noncomputable def toAdv (p : StaticAdversary M) : Adversary M :=
  ⟨fun _ h a => p.1 h.cur a, fun _ h a ha => p.2 h.cur a ha⟩

lemma nonempty_static : Nonempty (StaticAdversary M) := by
  obtain ⟨R, hR⟩ := M.bounded
  obtain ⟨p, _⟩ := exists_near M R hR (fun _ => 0) 1 one_pos
  exact ⟨p⟩

variable {M}

lemma V_bddBelow (R : ℝ) (hR : ∀ s, ∀ a ∈ M.Aset s, ∀ s', |M.r s a s'| ≤ R) (π : Policy M) (s : S) :
    BddBelow (Set.range fun σ : Adversary M => discountedReward M π.1 σ.1 s) :=
  ⟨-(R / (1 - M.lam)), by
    rintro _ ⟨σ, rfl⟩
    exact (abs_le.mp (discounted_abs_le R hR π.2)).1⟩

lemma V_ge (R : ℝ) (hR : ∀ s, ∀ a ∈ M.Aset s, ∀ s', |M.r s a s'| ≤ R) (π : Policy M)
    (W : S → ℝ) (C : ℝ) (hW : ∀ s, |W s| ≤ C)
    (HL : ∀ n (h : History S A n), W h.cur ≤
      RobustDP.FiniteHorizon.expect (π.1 n h) (fun a => Q M W h.cur a)) (s : S) :
    W s ≤ V M π s := by
  haveI : Nonempty (Adversary M) := ⟨toAdv M (nonempty_static M).some⟩
  exact le_ciInf (fun σ => lower_bound R hR π.2 σ.2 W C hW HL)

lemma V_le (R : ℝ) (hR : ∀ s, ∀ a ∈ M.Aset s, ∀ s', |M.r s a s'| ≤ R) (π : Policy M)
    (W : S → ℝ) (C : ℝ) (hW : ∀ s, |W s| ≤ C)
    (HU : ∀ n (h : History S A n),
      RobustDP.FiniteHorizon.expect (π.1 n h) (fun a => Q M W h.cur a) ≤ W h.cur) (s : S) :
    V M π s ≤ W s := by
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  have hε' : 0 < ε * (1 - M.lam) := mul_pos hε (sub_pos.2 M.lam_lt_one)
  obtain ⟨p, hp⟩ := exists_near M R hR W _ hε'
  have := upper_bound (σ := fun _ h a => p.1 h.cur a) (s := s) R hR π.2 W C hW _ hε'.le
    (fun n h a ha => hp h.cur a ha) HU
  rw [mul_div_cancel_right₀ _ (sub_pos.2 M.lam_lt_one).ne'] at this
  exact (ciInf_le (V_bddBelow R hR π s) (toAdv M p)).trans this

lemma Vstatic_le (R : ℝ) (hR : ∀ s, ∀ a ∈ M.Aset s, ∀ s', |M.r s a s'| ≤ R) (π : Policy M)
    (W : S → ℝ) (C : ℝ) (hW : ∀ s, |W s| ≤ C)
    (HU : ∀ n (h : History S A n),
      RobustDP.FiniteHorizon.expect (π.1 n h) (fun a => Q M W h.cur a) ≤ W h.cur) (s : S) :
    Vstatic M π s ≤ W s := by
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  have hε' : 0 < ε * (1 - M.lam) := mul_pos hε (sub_pos.2 M.lam_lt_one)
  obtain ⟨p, hp⟩ := exists_near M R hR W _ hε'
  have := upper_bound (σ := fun _ h a => p.1 h.cur a) (s := s) R hR π.2 W C hW _ hε'.le
    (fun n h a ha => hp h.cur a ha) HU
  rw [mul_div_cancel_right₀ _ (sub_pos.2 M.lam_lt_one).ne'] at this
  have hbdd : BddBelow (Set.range fun p : StaticAdversary M =>
      discountedReward M π.1 (fun _ h a => p.1 h.cur a) s) :=
    ⟨-(R / (1 - M.lam)), by
      rintro _ ⟨q, rfl⟩
      exact (abs_le.mp (discounted_abs_le R hR π.2)).1⟩
  exact (ciInf_le hbdd p).trans this

lemma V_le_Vstatic (R : ℝ) (hR : ∀ s, ∀ a ∈ M.Aset s, ∀ s', |M.r s a s'| ≤ R) (π : Policy M)
    (s : S) : V M π s ≤ Vstatic M π s := by
  haveI : Nonempty (StaticAdversary M) := nonempty_static M
  exact le_ciInf (fun p => ciInf_le (V_bddBelow R hR π s) (toAdv M p))

lemma V_abs_le (R : ℝ) (hR : ∀ s, ∀ a ∈ M.Aset s, ∀ s', |M.r s a s'| ≤ R) (π : Policy M)
    (s : S) : |V M π s| ≤ R / (1 - M.lam) := by
  haveI : Nonempty (Adversary M) := ⟨toAdv M (nonempty_static M).some⟩
  rw [abs_le]
  constructor
  · exact le_ciInf (fun σ => (abs_le.mp (discounted_abs_le R hR π.2)).1)
  · obtain ⟨σ⟩ := ‹Nonempty (Adversary M)›
    exact (ciInf_le (V_bddBelow R hR π s) σ).trans (abs_le.mp (discounted_abs_le R hR π.2)).2

lemma Q_lip (R : ℝ) (hR : ∀ s, ∀ a ∈ M.Aset s, ∀ s', |M.r s a s'| ≤ R)
    (U W : S → ℝ) (hU : IsBounded U) (hW : IsBounded W) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ s, |U s - W s| ≤ c) (s : S) (a : A) (ha : a ∈ M.Aset s) :
    |Q M U s a - Q M W s a| ≤ M.lam * c := by
  obtain ⟨CU, hCU⟩ := hU
  obtain ⟨CW, hCW⟩ := hW
  have h1 := Q_le_Q_add M R hR U W (max CU CW)
    (fun s => (hCU s).trans (le_max_left _ _)) (fun s => (hCW s).trans (le_max_right _ _)) c
    (fun s => by have := (abs_le.mp (h s)).2; linarith) s a ha
  have h2 := Q_le_Q_add M R hR W U (max CU CW)
    (fun s => (hCW s).trans (le_max_right _ _)) (fun s => (hCU s).trans (le_max_left _ _)) c
    (fun s => by have := (abs_le.mp (h s)).1; linarith) s a ha
  rw [abs_le]; constructor <;> linarith

lemma stationary_apply (d : DecisionRule M) (n : ℕ) (h : History S A n) :
    (stationary M d).1 n h = PMF.pure (d.1 h.cur) := rfl

lemma stationary_fixed (R : ℝ) (hR : ∀ s, ∀ a ∈ M.Aset s, ∀ s', |M.r s a s'| ≤ R)
    (d : DecisionRule M) (U : S → ℝ) (hU : IsBounded U) (hf : ∀ s, U s = Q M U s (d.1 s)) (s : S) :
    V M (stationary M d) s = U s := by
  obtain ⟨C, hC⟩ := hU
  have HE : ∀ n (h : History S A n), RobustDP.FiniteHorizon.expect ((stationary M d).1 n h)
      (fun a => Q M U h.cur a) = U h.cur := by
    intro n h
    rw [stationary_apply, expect_pure]
    exact (hf _).symm
  apply le_antisymm
  · exact V_le R hR _ U C hC (fun n h => (HE n h).le) s
  · exact V_ge R hR _ U C hC (fun n h => (HE n h).ge) s

end Vlemmas

lemma exists_stat_fixed {S A : Type*} [Countable S] [Countable A] (M : Model S A) (R : ℝ)
    (hR : ∀ s, ∀ a ∈ M.Aset s, ∀ s', |M.r s a s'| ≤ R) (d : DecisionRule M) :
    ∃ U : S → ℝ, IsBounded U ∧ ∀ s, U s = Q M U s (d.1 s) := by
  obtain ⟨U, hU, hfix⟩ := exists_fixed M.lam M.lam_pos M.lam_lt_one (fun U s => Q M U s (d.1 s))
    (fun U ⟨C, hC⟩ => ⟨R + M.lam * C, fun s => Q_abs_le M R hR U C hC s _ (d.2 s)⟩)
    (fun U W hU hW c hc h s => Q_lip R hR U W hU hW c hc h s _ (d.2 s))
  exact ⟨U, hU, fun s => (congrFun hfix s).symm⟩

lemma feas_le {S A : Type*} [Countable S] [Countable A] (M : Model S A) (R : ℝ)
    (hR : ∀ s, ∀ a ∈ M.Aset s, ∀ s', |M.r s a s'| ≤ R) (d : DecisionRule M) (U : S → ℝ)
    (hU : IsBounded U)
    (hfe : ∀ s, ∀ p ∈ M.P s (d.1 s),
      U s ≤ RobustDP.FiniteHorizon.expect p (fun s' => M.r s (d.1 s) s' + M.lam * U s')) (s : S) :
    U s ≤ V M (stationary M d) s := by
  obtain ⟨C, hC⟩ := hU
  refine V_ge R hR _ U C hC (fun n h => ?_) s
  rw [stationary_apply, expect_pure]
  haveI : Nonempty (M.P h.cur (d.1 h.cur)) := (M.P_nonempty _ _ (d.2 _)).to_subtype
  exact le_ciInf (fun p => hfe _ _ p.2)

end MMA

theorem solution {S A : Type*} [Countable S] [Countable A] (M : Model S A)
    (d : DecisionRule M) (α : S → ℝ) (hα : ∀ s, 0 < α s) (hαs : Summable α) :
    let feasible : (S → ℝ) → Prop := fun U =>
      IsBounded U ∧ ∀ s, ∀ p ∈ M.P s (d.1 s),
        U s ≤ RobustDP.FiniteHorizon.expect p (fun s' => M.r s (d.1 s) s' + M.lam * U s')
    feasible (V M (stationary M d)) ∧
      (∀ U, feasible U → ∑' s, α s * U s ≤ ∑' s, α s * V M (stationary M d) s) ∧
      ∀ U, feasible U → ∑' s, α s * U s = ∑' s, α s * V M (stationary M d) s →
        U = V M (stationary M d) := by
  intro feasible
  obtain ⟨R, hR⟩ := M.bounded
  obtain ⟨U0, hU0, hf0⟩ := MMA.exists_stat_fixed M R hR d
  have hV : V M (stationary M d) = U0 :=
    funext (fun s => MMA.stationary_fixed R hR d U0 hU0 hf0 s)
  have hsumm : ∀ U : S → ℝ, IsBounded U → Summable fun s => α s * U s := by
    rintro U ⟨C, hC⟩
    refine Summable.of_norm_bounded (hαs.mul_right C) (fun s => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hα s)]
    exact mul_le_mul_of_nonneg_left (hC s) (hα s).le
  have hle : ∀ U, feasible U → ∀ s, U s ≤ V M (stationary M d) s :=
    fun U hU => MMA.feas_le M R hR d U hU.1 hU.2
  refine ⟨⟨hV ▸ hU0, ?_⟩, ?_, ?_⟩
  · intro s p hp
    rw [hV]
    obtain ⟨C, hC⟩ := hU0
    exact (hf0 s).le.trans (MMA.Q_le_expect M R hR U0 C hC s _ (d.2 s) p hp)
  · intro U hU
    refine (hsumm U hU.1).tsum_le_tsum (fun s => ?_) (hsumm _ (hV ▸ hU0))
    exact mul_le_mul_of_nonneg_left (hle U hU s) (hα s).le
  · intro U hU heq
    have h1 := hsumm U hU.1
    have h2 := hsumm _ (hV ▸ hU0 : IsBounded (V M (stationary M d)))
    have h3 : HasSum (fun s => α s * V M (stationary M d) s - α s * U s) 0 := by
      have := h2.hasSum.sub h1.hasSum
      rwa [heq, sub_self] at this
    rw [hasSum_zero_iff_of_nonneg] at h3
    · funext s
      have := congrFun h3 s
      simp only [Pi.zero_apply] at this
      have h4 : α s * (V M (stationary M d) s - U s) = 0 := by rw [mul_sub]; exact this
      rcases mul_eq_zero.mp h4 with h | h
      · exact absurd h (hα s).ne'
      · linarith
    · intro s
      have := mul_le_mul_of_nonneg_left (hle U hU s) (hα s).le
      linarith
