-- Prove2me | solution 1 for StableDispatch.Markov.exit_sum_finite
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T12:13:36.564733+00:00
-- url     : https://prove2.me/submissions/73db69ce-2b77-4269-a737-65b7b0922934

import Mathlib
import Definitions.Def_MatrixAnalytic_Tree_Process
import Definitions.Def_StableDispatch_Markov_Setting

open scoped ENNReal
open MatrixAnalytic.Tree

set_option linter.unusedSectionVars false

namespace SDFoster

noncomputable section

variable {V : Type*} [Countable V] [DecidableEq V]

lemma pathWeightE_cons (P : V → V → ℝ) {t : ℕ} (y : V) (ω : Fin (t + 1) → V) :
    pathWeightE P (Fin.cons y ω : Fin (t + 2) → V)
      = ENNReal.ofReal (P y (ω 0)) * pathWeightE P ω := by
  unfold pathWeightE
  rw [Fin.prod_univ_succ]
  congr 1

open Classical in
/-- mass of the trajectories of length `t` after the start `y` which avoid `T` at times `1..t`. -/
def mass (P : V → V → ℝ) (T : Set V) (y : V) (t : ℕ) : ℝ≥0∞ :=
  ∑' ω : Fin t → V, if ∀ s, ω s ∉ T then pathWeightE P (Fin.cons y ω : Fin (t + 1) → V) else 0

lemma mass_zero (P : V → V → ℝ) (T : Set V) (y : V) : mass P T y 0 = 1 := by
  unfold mass
  simp [pathWeightE]

open Classical in
/-- `W` cut off on the taboo set `T`. -/
def cut (T : Set V) (W : V → ℝ≥0∞) (w : V) : ℝ≥0∞ := if w ∈ T then 0 else W w

lemma cut_le (T : Set V) (W : V → ℝ≥0∞) (w : V) : cut T W w ≤ W w := by
  unfold cut; split_ifs <;> simp

lemma cut_mem {T : Set V} {w : V} (W : V → ℝ≥0∞) (h : w ∈ T) : cut T W w = 0 := by
  unfold cut; simp [h]

lemma cut_not_mem {T : Set V} {w : V} (W : V → ℝ≥0∞) (h : w ∉ T) : cut T W w = W w := by
  unfold cut; simp [h]

lemma mass_succ (P : V → V → ℝ) (T : Set V) (y : V) (t : ℕ) :
    mass P T y (t + 1) = ∑' w, ENNReal.ofReal (P y w) * cut T (fun w => mass P T w t) w := by
  unfold mass
  rw [← (Fin.consEquiv (fun _ : Fin (t + 1) => V)).tsum_eq]
  rw [ENNReal.tsum_prod']
  refine tsum_congr (fun w => ?_)
  by_cases hw : w ∈ T
  · rw [cut_mem _ hw, mul_zero]
    simp [Fin.consEquiv, Fin.forall_fin_succ, hw]
  · rw [cut_not_mem _ hw, ← ENNReal.tsum_mul_left]
    refine tsum_congr (fun ω => ?_)
    have hc : (∀ s : Fin (t + 1), (Fin.cons w ω : Fin (t + 1) → V) s ∉ T) ↔ ∀ s, ω s ∉ T := by
      rw [Fin.forall_fin_succ]; simp [hw]
    split_ifs with h1 h2 h2
    · exact pathWeightE_cons P y (Fin.cons w ω)
    · exact absurd (hc.1 h1) h2
    · exact absurd (hc.2 h2) h1
    · simp

/-- `W` is a supersolution of the expected-number-of-jumps equation for the taboo set `T`. -/
def Super (P : V → V → ℝ) (T : Set V) (W : V → ℝ≥0∞) : Prop :=
  ∀ y, 1 + ∑' w, ENNReal.ofReal (P y w) * cut T W w ≤ W y

lemma partial_le (P : V → V → ℝ) (T : Set V) (W : V → ℝ≥0∞) (hS : Super P T W) :
    ∀ N y, ∑ t ∈ Finset.range N, mass P T y t ≤ W y
  | 0, y => by simp
  | N + 1, y => by
    rw [Finset.sum_range_succ']
    simp only [mass_succ, mass_zero]
    rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    calc ∑' w, ∑ t ∈ Finset.range N, ENNReal.ofReal (P y w) * cut T (fun w => mass P T w t) w
          + 1 ≤ ∑' w, ENNReal.ofReal (P y w) * cut T W w + 1 := by
          gcongr with w
          rw [← Finset.mul_sum]
          gcongr
          by_cases hw : w ∈ T
          · simp [cut_mem _ hw]
          · simp only [cut_not_mem _ hw]
            exact partial_le P T W hS N w
      _ ≤ W y := by rw [add_comm]; exact hS y

lemma tsum_mass_le (P : V → V → ℝ) (T : Set V) (W : V → ℝ≥0∞) (hS : Super P T W) (y : V) :
    ∑' t, mass P T y t ≤ W y := by
  rw [ENNReal.tsum_eq_iSup_nat]
  exact iSup_le (fun N => partial_le P T W hS N y)

open Classical in
def aF (u : V) (T' : Set V) (φ : V → ℝ≥0∞) (w : V) : ℝ≥0∞ :=
  if w = u then 1 else if w ∈ T' then 0 else φ w

open Classical in
def bF (u : V) (T' : Set V) (ψ : V → ℝ≥0∞) (w : V) : ℝ≥0∞ :=
  if w = u then 0 else if w ∈ T' then 1 else ψ w

def phi (P : V → V → ℝ) (u : V) (T' : Set V) : ℕ → V → ℝ≥0∞
  | 0 => fun _ => 1
  | k + 1 => fun y => ∑' w, ENNReal.ofReal (P y w) * aF u T' (phi P u T' k) w

def psi (P : V → V → ℝ) (u : V) (T' : Set V) : ℕ → V → ℝ≥0∞
  | 0 => fun _ => 0
  | k + 1 => fun y => ∑' w, ENNReal.ofReal (P y w) * bF u T' (psi P u T' k) w

lemma phi_add_psi (P : V → V → ℝ) (hP : ∀ y, ∑' w, ENNReal.ofReal (P y w) = 1)
    (u : V) (T' : Set V) : ∀ k y, phi P u T' k y + psi P u T' k y = 1
  | 0, y => by simp [phi, psi]
  | k + 1, y => by
    simp only [phi, psi]
    rw [← ENNReal.tsum_add]
    rw [← hP y]
    refine tsum_congr (fun w => ?_)
    rw [← mul_add]
    have : aF u T' (phi P u T' k) w + bF u T' (psi P u T' k) w = 1 := by
      unfold aF bF
      split_ifs
      · simp
      · simp
      · exact phi_add_psi P hP u T' k w
    rw [this, mul_one]

lemma phi_le_one (P : V → V → ℝ) (hP : ∀ y, ∑' w, ENNReal.ofReal (P y w) = 1)
    (u : V) (T' : Set V) (k : ℕ) (y : V) : phi P u T' k y ≤ 1 := by
  rw [← phi_add_psi P hP u T' k y]
  exact le_self_add

lemma phi_succ_le (P : V → V → ℝ) (hP : ∀ y, ∑' w, ENNReal.ofReal (P y w) = 1)
    (u : V) (T' : Set V) : ∀ k y, phi P u T' (k + 1) y ≤ phi P u T' k y
  | 0, y => by
    show ∑' w, ENNReal.ofReal (P y w) * aF u T' (fun _ => 1) w ≤ 1
    calc ∑' w, ENNReal.ofReal (P y w) * aF u T' (fun _ => 1) w ≤ ∑' w, ENNReal.ofReal (P y w) := by
          gcongr with w
          exact mul_le_of_le_one_right (by positivity) (by unfold aF; split_ifs <;> simp)
      _ = 1 := hP y
  | k + 1, y => by
    show ∑' w, ENNReal.ofReal (P y w) * aF u T' (phi P u T' (k + 1)) w
      ≤ ∑' w, ENNReal.ofReal (P y w) * aF u T' (phi P u T' k) w
    gcongr with w
    unfold aF
    split_ifs
    · exact le_rfl
    · exact le_rfl
    · exact phi_succ_le P hP u T' k w

lemma exists_psi_ne_zero (P : V → V → ℝ)
    (hirr : ∀ x y, Relation.ReflTransGen (fun a b => 0 < P a b) x y)
    (T' : Set V) (u z : V) (hu : u ∉ T') (hz : z ∈ T') : ∃ N, psi P u T' N u ≠ 0 := by
  by_contra hcon
  push Not at hcon
  let C : Set V := {y | y ∉ T' ∧ ∀ k, psi P u T' k y = 0}
  have huC : u ∈ C := ⟨hu, hcon⟩
  have hclos : ∀ y w, y ∈ C → 0 < P y w → w ∈ C := by
    intro y w hy hyw
    have hpos : ENNReal.ofReal (P y w) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hyw
    by_cases hwu : w = u
    · rw [hwu]; exact huC
    by_cases hwT : w ∈ T'
    · exfalso
      have h1 : ENNReal.ofReal (P y w) * bF u T' (psi P u T' 0) w ≤ psi P u T' 1 y :=
        ENNReal.le_tsum (f := fun w => ENNReal.ofReal (P y w) * bF u T' (psi P u T' 0) w) w
      rw [hy.2 1] at h1
      simp [bF, hwu, hwT] at h1
      exact hpos (ENNReal.ofReal_eq_zero.2 h1)
    · refine ⟨hwT, fun k => ?_⟩
      have h1 : ENNReal.ofReal (P y w) * bF u T' (psi P u T' k) w ≤ psi P u T' (k + 1) y :=
        ENNReal.le_tsum (f := fun w => ENNReal.ofReal (P y w) * bF u T' (psi P u T' k) w) w
      rw [hy.2 (k + 1)] at h1
      simp only [bF, hwu, hwT, if_false, nonpos_iff_eq_zero, mul_eq_zero] at h1
      rcases h1 with h1 | h1
      · exact absurd h1 hpos
      · exact h1
  have hreach : ∀ y, Relation.ReflTransGen (fun a b => 0 < P a b) u y → y ∈ C := by
    intro y hy
    induction hy with
    | refl => exact huC
    | tail _ hab ih => exact hclos _ _ ih hab
  exact (hreach z (hirr u z)).1 hz

open Classical in
lemma removal (P : V → V → ℝ) (hP : ∀ y, ∑' w, ENNReal.ofReal (P y w) = 1)
    (hirr : ∀ x y, Relation.ReflTransGen (fun a b => 0 < P a b) x y)
    (T' : Set V) (u z : V) (hu : u ∉ T') (hz : z ∈ T') (W : V → ℝ≥0∞) (hW : ∀ y, W y ≠ ⊤)
    (hS : Super P (insert u T') W) : ∃ W' : V → ℝ≥0∞, (∀ y, W' y ≠ ⊤) ∧ Super P T' W' := by
  obtain ⟨N, hN⟩ := exists_psi_ne_zero P hirr T' u z hu hz
  set φ := phi P u T' N with hφ
  have hφ1 : ∀ y, φ y ≤ 1 := fun y => phi_le_one P hP u T' N y
  have hφu : φ u < 1 := by
    have h := phi_add_psi P hP u T' N u
    have hne : φ u ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hφ1 u)
    calc φ u < φ u + psi P u T' N u := ENNReal.lt_add_right hne hN
      _ = 1 := h
  have hd0 : 1 - φ u ≠ 0 := (tsub_pos_iff_lt.2 hφu).ne'
  have hdt : 1 - φ u ≠ ⊤ := ENNReal.sub_ne_top ENNReal.one_ne_top
  set K := W u / (1 - φ u) with hK
  have hKt : K ≠ ⊤ := ENNReal.div_ne_top (hW u) hd0
  have hKu : W u + K * φ u ≤ K := by
    have h1 : K * (1 - φ u) = W u := ENNReal.div_mul_cancel hd0 hdt
    refine le_of_eq ?_
    calc W u + K * φ u = K * (1 - φ u) + K * φ u := by rw [h1]
      _ = K * (1 - φ u + φ u) := by rw [mul_add]
      _ = K := by rw [tsub_add_cancel_of_le (hφ1 u), mul_one]
  refine ⟨fun y => W y + K * φ y, fun y => ?_, fun y => ?_⟩
  · exact ENNReal.add_ne_top.2 ⟨hW y, ENNReal.mul_ne_top hKt
      (ne_top_of_le_ne_top ENNReal.one_ne_top (hφ1 y))⟩
  · have hpt : ∀ w, ENNReal.ofReal (P y w) * cut T' (fun y => W y + K * φ y) w
        ≤ ENNReal.ofReal (P y w) * cut (insert u T') W w
          + K * (ENNReal.ofReal (P y w) * aF u T' φ w) := by
      intro w
      rw [mul_left_comm, ← mul_add]
      gcongr
      by_cases hwu : w = u
      · subst hwu
        rw [cut_not_mem _ hu, cut_mem _ (Set.mem_insert _ _)]
        simp [aF]
        exact hKu
      · by_cases hwT : w ∈ T'
        · rw [cut_mem _ hwT]; exact zero_le
        · have : w ∉ insert u T' := by simp [hwu, hwT]
          rw [cut_not_mem _ hwT, cut_not_mem _ this]
          simp [hwu, hwT, aF]
    calc 1 + ∑' w, ENNReal.ofReal (P y w) * cut T' (fun y => W y + K * φ y) w
        ≤ 1 + ∑' w, (ENNReal.ofReal (P y w) * cut (insert u T') W w
          + K * (ENNReal.ofReal (P y w) * aF u T' φ w)) := by
          gcongr with w; exact hpt w
      _ = (1 + ∑' w, ENNReal.ofReal (P y w) * cut (insert u T') W w)
          + K * phi P u T' (N + 1) y := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, add_assoc]
          rfl
      _ ≤ W y + K * φ y := by
          gcongr
          · exact hS y
          · exact phi_succ_le P hP u T' N y

open Classical in
theorem foster_mass (P : V → V → ℝ) (hP : ∀ y, ∑' w, ENNReal.ofReal (P y w) = 1)
    (hirr : ∀ x y, Relation.ReflTransGen (fun a b => 0 < P a b) x y)
    (F : Set V) (hF : F.Finite) (W : V → ℝ≥0∞) (hW : ∀ y, W y ≠ ⊤)
    (hdrift : ∀ y, y ∉ F → 1 + ∑' w, ENNReal.ofReal (P y w) * W w ≤ W y)
    (hfin : ∀ y, y ∈ F → ∑' w, ENNReal.ofReal (P y w) * W w ≠ ⊤) (z : V) :
    ∑' t, mass P {z} z t ≠ ⊤ := by
  have key : ∀ A : Finset V, ∀ W : V → ℝ≥0∞, (∀ y, W y ≠ ⊤) → Super P (↑A ∪ {z}) W →
      ∃ W' : V → ℝ≥0∞, (∀ y, W' y ≠ ⊤) ∧ Super P {z} W' := by
    intro A
    induction A using Finset.induction_on with
    | empty => intro W hW hS; exact ⟨W, hW, by simpa using hS⟩
    | insert a A haA ih =>
      intro W hW hS
      by_cases haz : a = z
      · subst haz
        apply ih W hW
        have : (↑(insert a A) : Set V) ∪ {a} = ↑A ∪ {a} := by
          ext x; simp
        rw [← this]; exact hS
      · have hu : a ∉ (↑A ∪ {z} : Set V) := by simp [haA, haz]
        have hz : z ∈ (↑A ∪ {z} : Set V) := by simp
        have : insert a (↑A ∪ {z} : Set V) = ↑(insert a A) ∪ {z} := by
          ext x; simp; tauto
        obtain ⟨W', hW', hS'⟩ := removal P hP hirr (↑A ∪ {z}) a z hu hz W hW (by rw [this]; exact hS)
        exact ih W' hW' hS'
  let W0 : V → ℝ≥0∞ := fun y => if y ∈ F then 1 + ∑' w, ENNReal.ofReal (P y w) * W w else W y
  have hW0 : ∀ y, W0 y ≠ ⊤ := by
    intro y
    by_cases hy : y ∈ F
    · simp only [W0, hy, if_true]; exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hfin y hy⟩
    · simp only [W0, hy, if_false]; exact hW y
  have hS0 : Super P (↑hF.toFinset ∪ {z}) W0 := by
    intro y
    have hle : 1 + ∑' w, ENNReal.ofReal (P y w) * cut (↑hF.toFinset ∪ {z}) W0 w
        ≤ 1 + ∑' w, ENNReal.ofReal (P y w) * W w := by
      gcongr with w
      by_cases hw : w ∈ (↑hF.toFinset ∪ {z} : Set V)
      · rw [cut_mem _ hw]; exact zero_le
      · have hwF : w ∉ F := by
          intro h; exact hw (by simp [h])
        rw [cut_not_mem _ hw]
        simp [W0, hwF]
    by_cases hy : y ∈ F
    · simp only [W0, hy, if_true]; exact hle
    · refine hle.trans ?_
      simp only [W0, hy, if_false]
      exact hdrift y hy
  obtain ⟨W', hW', hS'⟩ := key hF.toFinset W0 hW0 hS0
  exact ne_top_of_le_ne_top (hW' z) (tsum_mass_le P {z} W' hS' z)

lemma tsum_start (x : V) (t : ℕ) (C : (Fin (t + 1) → V) → Prop) [DecidablePred C]
    (D : (Fin (t + 1) → V) → Prop) [DecidablePred D]
    (hCD : ∀ ω, C ω ↔ (ω 0 = x ∧ D ω))
    (g : (Fin (t + 1) → V) → ℝ≥0∞) :
    (∑' ω : Fin (t + 1) → V, if C ω then g ω else 0)
      = ∑' ω' : Fin t → V, if D (Fin.cons x ω') then g (Fin.cons x ω') else 0 := by
  rw [← (Fin.consEquiv (fun _ : Fin (t + 1) => V)).tsum_eq, ENNReal.tsum_prod']
  have key : ∀ a : V, (∑' ω' : Fin t → V, if C ((Fin.consEquiv fun _ => V) (a, ω'))
      then g ((Fin.consEquiv fun _ => V) (a, ω')) else 0)
      = if a = x then ∑' ω' : Fin t → V, (if D (Fin.cons x ω') then g (Fin.cons x ω') else 0)
        else 0 := by
    intro a
    by_cases ha : a = x
    · subst ha
      rw [if_pos rfl]
      refine tsum_congr (fun ω' => ?_)
      have h := hCD ((Fin.consEquiv fun _ => V) (a, ω'))
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd (h.1 h1).2 h2
      · exact absurd (h.2 ⟨rfl, h2⟩) h1
      · rfl
    · rw [if_neg ha]
      refine ENNReal.tsum_eq_zero.2 (fun ω' => ?_)
      rw [if_neg]
      intro h1
      exact ha ((hCD _).1 h1).1
  rw [tsum_congr key, tsum_ite_eq]

open Classical in
lemma returnTail_eq (Q : V → V → ℝ) (x : V) (t : ℕ) :
    returnTail Q x t = mass (jumpP Q) {x} x t := by
  unfold returnTail mass
  rw [tsum_start x t _ (fun ω => ∀ s : Fin (t + 1), s ≠ 0 → ω s ≠ x) (fun _ => Iff.rfl)]
  refine tsum_congr (fun ω' => ?_)
  have hc : (∀ s : Fin (t + 1), s ≠ 0 → (Fin.cons x ω' : Fin (t + 1) → V) s ≠ x)
      ↔ ∀ s, ω' s ∉ ({x} : Set V) := by
    rw [Fin.forall_fin_succ]; simp
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (hc.1 h1) h2
  · exact absurd (hc.2 h2) h1
  · rfl

open Classical in
lemma sum_expVisits (Q : V → V → ℝ) (x : V) :
    ∑' y, expVisitsAvoid (jumpP Q) {x} x y = ∑' t, returnTail Q x t := by
  unfold expVisitsAvoid returnTail
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun t => ?_)
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun ω => ?_)
  by_cases h : ω 0 = x ∧ ∀ s : Fin (t + 1), s ≠ 0 → ω s ≠ x
  · rw [if_pos h]
    refine Eq.trans (tsum_congr (fun y => ?_))
      (tsum_ite_eq (ω (Fin.last t)) (fun _ => pathWeightE (jumpP Q) ω))
    · by_cases hy : y = ω (Fin.last t)
      · rw [if_pos hy, if_pos]
        exact ⟨h.1, hy.symm, fun s hs => by simpa using h.2 s hs⟩
      · rw [if_neg hy, if_neg]
        rintro ⟨_, h2, _⟩
        exact hy h2.symm
  · rw [if_neg h]
    refine ENNReal.tsum_eq_zero.2 (fun y => ?_)
    rw [if_neg]
    rintro ⟨h1, _, h3⟩
    exact h ⟨h1, fun s hs => by simpa using h3 s hs⟩

/-- **Foster's criterion** for the continuous-time process with generator `Q`, in terms of its
jump chain: holding rates bounded below, a stochastic irreducible jump chain, and a nonnegative
function whose jump-chain drift is at most `-1` outside a finite set. -/
theorem foster_ct (Q : V → V → ℝ) (qmin : ℝ) (hqmin : 0 < qmin)
    (hq : ∀ x, qmin ≤ holdRate Q x)
    (hP : ∀ y, ∑' w, ENNReal.ofReal (jumpP Q y w) = 1)
    (hirr : ∀ x y, Relation.ReflTransGen (fun a b => 0 < jumpP Q a b) x y)
    (F : Set V) (hF : F.Finite) (W : V → ℝ≥0∞) (hW : ∀ y, W y ≠ ⊤)
    (hdrift : ∀ y, y ∉ F → 1 + ∑' w, ENNReal.ofReal (jumpP Q y w) * W w ≤ W y)
    (hfin : ∀ y, y ∈ F → ∑' w, ENNReal.ofReal (jumpP Q y w) * W w ≠ ⊤) :
    IsPositiveRecurrentProcess Q := by
  intro x
  have hm := foster_mass (jumpP Q) hP hirr F hF W hW hdrift hfin x
  have hR : ∑' t, returnTail Q x t ≠ ⊤ := by
    rw [tsum_congr (returnTail_eq Q x)]; exact hm
  refine ⟨ENNReal.tendsto_atTop_zero_of_tsum_ne_top hR, ?_⟩
  calc expReturnTime Q x
      ≤ ∑' y, expVisitsAvoid (jumpP Q) {x} x y * ENNReal.ofReal qmin⁻¹ := by
        unfold expReturnTime sojournAvoid
        gcongr with y
        exact hq y
    _ = (∑' t, returnTail Q x t) * ENNReal.ofReal qmin⁻¹ := by
        rw [ENNReal.tsum_mul_right, sum_expVisits]
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hR) ENNReal.ofReal_lt_top

end

end SDFoster


open scoped ENNReal
open MatrixAnalytic.Tree StableDispatch.Markov

set_option linter.unusedSectionVars false

namespace SDChain

noncomputable section

variable {n : ℕ}

/-- arrival target -/
def arr (x : State n) : State n := (Function.update x.1 x.2 (x.1 x.2 + 1), x.2)
/-- departure target at server `j` -/
def dep (x : State n) (j : Fin n) : State n := (Function.update x.1 j (x.1 j - 1), x.2)
/-- switch target -/
def sw (x : State n) (j : Fin n) : State n := (x.1, j)

/-- the off-diagonal rates out of `x` -/
def offRate (lam α : ℝ) (μ : Fin n → ℝ) (x y : State n) : ℝ :=
  (if y = arr x then lam * n else 0)
    + ∑ j, (if 1 ≤ x.1 j ∧ y = dep x j then μ j else 0)
    + ∑ j, (if x.1 j < x.1 x.2 ∧ y = sw x j then α else 0)

/-- the total exit rate -/
def hold (lam α : ℝ) (μ : Fin n → ℝ) (x : State n) : ℝ :=
  lam * n + ∑ j, (if 1 ≤ x.1 j then μ j else 0) + ∑ j, (if x.1 j < x.1 x.2 then α else 0)

/-- the rate-weighted sum `Σ_y offRate x y f y`, written out. -/
def Dr (lam α : ℝ) (μ : Fin n → ℝ) (x : State n) (f : State n → ℝ) : ℝ :=
  lam * n * f (arr x) + ∑ j, (if 1 ≤ x.1 j then μ j * f (dep x j) else 0)
    + ∑ j, (if x.1 j < x.1 x.2 then α * f (sw x j) else 0)

lemma arr_ne (x : State n) : arr x ≠ x := by
  intro h
  have := congrArg (fun z : State n => z.1 x.2) h
  simp [arr] at this

lemma dep_ne (x : State n) (j : Fin n) (hj : 1 ≤ x.1 j) : dep x j ≠ x := by
  intro h
  have := congrArg (fun z : State n => z.1 j) h
  simp [dep] at this
  omega

lemma sw_ne (x : State n) (j : Fin n) (hj : x.1 j < x.1 x.2) : sw x j ≠ x := by
  intro h
  have := congrArg (fun z : State n => z.2) h
  simp [sw] at this
  rw [this] at hj
  exact lt_irrefl _ hj

lemma offRate_self (lam α : ℝ) (μ : Fin n → ℝ) (x : State n) : offRate lam α μ x x = 0 := by
  unfold offRate
  rw [if_neg (arr_ne x).symm]
  rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
  · simp
  · intro j _
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact sw_ne x j h1 h2.symm
  · intro j _
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact dep_ne x j h1 h2.symm

lemma gen_eq (lam α : ℝ) (μ : Fin n → ℝ) (x y : State n) :
    gen n lam α μ x y = (if y = x then -hold lam α μ x else 0) + offRate lam α μ x y := by
  by_cases h : y = x
  · subst h
    rw [offRate_self]
    simp [gen, hold]
  · simp only [gen, h, if_false, zero_add]
    rfl

lemma holdRate_eq (lam α : ℝ) (μ : Fin n → ℝ) (x : State n) :
    holdRate (gen n lam α μ) x = hold lam α μ x := by
  simp [holdRate, gen, hold]

lemma jumpP_eq (lam α : ℝ) (μ : Fin n → ℝ) (x y : State n) (hh : hold lam α μ x ≠ 0) :
    jumpP (gen n lam α μ) x y = offRate lam α μ x y / hold lam α μ x := by
  unfold jumpP
  rw [holdRate_eq, if_neg hh]
  by_cases h : y = x
  · subst h; rw [if_pos rfl, offRate_self]; simp
  · rw [if_neg h, gen_eq, if_neg h, zero_add]

lemma ite_and_mul (c : Prop) [Decidable c] (y d : State n) (a : ℝ) (f : State n → ℝ) :
    (if c ∧ y = d then a else 0) * f y = if y = d then (if c then a * f d else 0) else 0 := by
  by_cases hy : y = d
  · subst hy; by_cases hc : c <;> simp [hc]
  · simp [hy]

lemma hasSum_offRate (lam α : ℝ) (μ : Fin n → ℝ) (x : State n) (f : State n → ℝ) :
    HasSum (fun y => offRate lam α μ x y * f y) (Dr lam α μ x f) := by
  have hpt : (fun y => offRate lam α μ x y * f y) = fun y =>
      (if y = arr x then lam * n * f (arr x) else 0)
      + ∑ j, (if y = dep x j then (if 1 ≤ x.1 j then μ j * f (dep x j) else 0) else 0)
      + ∑ j, (if y = sw x j then (if x.1 j < x.1 x.2 then α * f (sw x j) else 0) else 0) := by
    funext y
    unfold offRate
    rw [add_mul, add_mul, Finset.sum_mul, Finset.sum_mul]
    congr 1
    congr 1
    · by_cases hy : y = arr x
      · subst hy; simp
      · simp [hy]
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      exact ite_and_mul _ _ _ _ _
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      exact ite_and_mul _ _ _ _ _
  rw [hpt]
  unfold Dr
  refine HasSum.add (HasSum.add (hasSum_ite_eq _ _) ?_) ?_
  · exact hasSum_sum (fun j _ => hasSum_ite_eq _ _)
  · exact hasSum_sum (fun j _ => hasSum_ite_eq _ _)

section Pos

variable (lam α : ℝ) (μ : Fin n → ℝ) (hlam : 0 < lam) (hα : 0 < α) (hμ : ∀ j, 0 < μ j)
include hlam hα hμ

lemma offRate_nonneg (x y : State n) : 0 ≤ offRate lam α μ x y := by
  unfold offRate
  refine add_nonneg (add_nonneg ?_ ?_) ?_
  · split_ifs <;> positivity
  · exact Finset.sum_nonneg (fun j _ => by split_ifs <;> [exact (hμ j).le; exact le_rfl])
  · exact Finset.sum_nonneg (fun j _ => by split_ifs <;> [exact hα.le; exact le_rfl])

lemma hold_ge (x : State n) : lam * n ≤ hold lam α μ x := by
  unfold hold
  have h1 : 0 ≤ ∑ j, (if 1 ≤ x.1 j then μ j else 0) :=
    Finset.sum_nonneg (fun j _ => by split_ifs <;> [exact (hμ j).le; exact le_rfl])
  have h2 : 0 ≤ ∑ j, (if x.1 j < x.1 x.2 then α else 0) :=
    Finset.sum_nonneg (fun j _ => by split_ifs <;> [exact hα.le; exact le_rfl])
  linarith

lemma hold_le (hsum : ∑ j, μ j = n) (x : State n) :
    hold lam α μ x ≤ lam * n + n + n * α := by
  unfold hold
  have h1 : ∑ j, (if 1 ≤ x.1 j then μ j else 0) ≤ ∑ j, μ j :=
    Finset.sum_le_sum (fun j _ => by split_ifs <;> [exact le_rfl; exact (hμ j).le])
  have h2 : ∑ j, (if x.1 j < x.1 x.2 then α else 0) ≤ ∑ _j : Fin n, α :=
    Finset.sum_le_sum (fun j _ => by split_ifs <;> [exact le_rfl; exact hα.le])
  simp at h2
  linarith

lemma jumpP_nonneg [NeZero n] (x y : State n) : 0 ≤ jumpP (gen n lam α μ) x y := by
  have hpos : 0 < hold lam α μ x :=
    lt_of_lt_of_le (by have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_neZero n
                       positivity) (hold_ge lam α μ hlam hα hμ x)
  rw [jumpP_eq lam α μ x y hpos.ne']
  exact div_nonneg (offRate_nonneg lam α μ hlam hα hμ x y) hpos.le

lemma tsum_jump [NeZero n] (x : State n) (f : State n → ℝ) (hf : ∀ y, 0 ≤ f y) :
    ∑' y, ENNReal.ofReal (jumpP (gen n lam α μ) x y) * ENNReal.ofReal (f y)
      = ENNReal.ofReal (Dr lam α μ x f / hold lam α μ x) := by
  have hpos : 0 < hold lam α μ x :=
    lt_of_lt_of_le (by have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_neZero n
                       positivity) (hold_ge lam α μ hlam hα hμ x)
  have hs : HasSum (fun y => jumpP (gen n lam α μ) x y * f y) (Dr lam α μ x f / hold lam α μ x) := by
    have := (hasSum_offRate lam α μ x f).div_const (hold lam α μ x)
    have hfun : (fun y => jumpP (gen n lam α μ) x y * f y)
        = fun y => offRate lam α μ x y * f y / hold lam α μ x := by
      funext y
      rw [jumpP_eq lam α μ x y hpos.ne']
      ring
    rw [hfun]; exact this
  have hnn : ∀ y, 0 ≤ jumpP (gen n lam α μ) x y * f y :=
    fun y => mul_nonneg (jumpP_nonneg lam α μ hlam hα hμ x y) (hf y)
  rw [← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg hnn hs.summable]
  refine tsum_congr (fun y => ?_)
  rw [ENNReal.ofReal_mul (jumpP_nonneg lam α μ hlam hα hμ x y)]

lemma Dr_nonneg (x : State n) (f : State n → ℝ) (hf : ∀ y, 0 ≤ f y) : 0 ≤ Dr lam α μ x f := by
  unfold Dr
  refine add_nonneg (add_nonneg ?_ ?_) ?_
  · have := hf (arr x); positivity
  · exact Finset.sum_nonneg (fun j _ => by
      split_ifs <;> [exact mul_nonneg (hμ j).le (hf _); exact le_rfl])
  · exact Finset.sum_nonneg (fun j _ => by
      split_ifs <;> [exact mul_nonneg hα.le (hf _); exact le_rfl])

lemma Dr_one (x : State n) : Dr lam α μ x (fun _ => 1) = hold lam α μ x := by
  unfold Dr hold
  simp

lemma stoch [NeZero n] (x : State n) :
    ∑' y, ENNReal.ofReal (jumpP (gen n lam α μ) x y) = 1 := by
  have hpos : 0 < hold lam α μ x :=
    lt_of_lt_of_le (by have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_neZero n
                       positivity) (hold_ge lam α μ hlam hα hμ x)
  have := tsum_jump lam α μ hlam hα hμ x (fun _ => 1) (fun _ => zero_le_one)
  simp only [ENNReal.ofReal_one, mul_one] at this
  rw [this, Dr_one lam α μ hlam hα hμ, div_self hpos.ne', ENNReal.ofReal_one]

lemma offRate_arr (x : State n) : lam * n ≤ offRate lam α μ x (arr x) := by
  unfold offRate
  rw [if_pos rfl]
  have h1 : 0 ≤ ∑ j, (if 1 ≤ x.1 j ∧ arr x = dep x j then μ j else 0) :=
    Finset.sum_nonneg (fun j _ => by split_ifs <;> [exact (hμ j).le; exact le_rfl])
  have h2 : 0 ≤ ∑ j, (if x.1 j < x.1 x.2 ∧ arr x = sw x j then α else 0) :=
    Finset.sum_nonneg (fun j _ => by split_ifs <;> [exact hα.le; exact le_rfl])
  linarith

lemma offRate_dep (x : State n) (j : Fin n) (hj : 1 ≤ x.1 j) :
    μ j ≤ offRate lam α μ x (dep x j) := by
  unfold offRate
  have h0 : 0 ≤ (if dep x j = arr x then lam * n else 0) := by
    split_ifs <;> [exact (mul_pos hlam (by
      have : (0:ℝ) < n := by
        have : 0 < n := Fin.pos j
        exact_mod_cast this
      exact this)).le; exact le_rfl]
  have h1 : μ j ≤ ∑ k, (if 1 ≤ x.1 k ∧ dep x j = dep x k then μ k else 0) := by
    have := Finset.single_le_sum (f := fun k => if 1 ≤ x.1 k ∧ dep x j = dep x k then μ k else 0)
      (fun k _ => by split_ifs <;> [exact (hμ k).le; exact le_rfl]) (Finset.mem_univ j)
    simpa [hj] using this
  have h2 : 0 ≤ ∑ k, (if x.1 k < x.1 x.2 ∧ dep x j = sw x k then α else 0) :=
    Finset.sum_nonneg (fun k _ => by split_ifs <;> [exact hα.le; exact le_rfl])
  linarith

lemma offRate_sw (x : State n) (j : Fin n) (hj : x.1 j < x.1 x.2) :
    α ≤ offRate lam α μ x (sw x j) := by
  unfold offRate
  have h0 : 0 ≤ (if sw x j = arr x then lam * n else 0) := by
    split_ifs <;> [exact (mul_pos hlam (by
      have : (0:ℝ) < n := by
        have : 0 < n := Fin.pos j
        exact_mod_cast this
      exact this)).le; exact le_rfl]
  have h1 : 0 ≤ ∑ k, (if 1 ≤ x.1 k ∧ sw x j = dep x k then μ k else 0) :=
    Finset.sum_nonneg (fun k _ => by split_ifs <;> [exact (hμ k).le; exact le_rfl])
  have h2 : α ≤ ∑ k, (if x.1 k < x.1 x.2 ∧ sw x j = sw x k then α else 0) := by
    have := Finset.single_le_sum (f := fun k => if x.1 k < x.1 x.2 ∧ sw x j = sw x k then α else 0)
      (fun k _ => by split_ifs <;> [exact hα.le; exact le_rfl]) (Finset.mem_univ j)
    simpa [hj] using this
  linarith

end Pos

section Reach

variable (R : State n → State n → Prop)
  (h1 : ∀ x, R x (arr x)) (h2 : ∀ x j, 1 ≤ x.1 j → R x (dep x j))
  (h3 : ∀ x j, x.1 j < x.1 x.2 → R x (sw x j))

open Relation

include h1 in
lemma up_stored (q : Fin n → ℕ) (s : Fin n) :
    ∀ m, ReflTransGen R (q, s) (Function.update q s (q s + m), s)
  | 0 => by simpa using (ReflTransGen.refl : ReflTransGen R (q, s) (q, s))
  | m + 1 => by
    refine (up_stored q s m).tail ?_
    have := h1 (Function.update q s (q s + m), s)
    simpa [arr, Function.update_idem, add_assoc] using this

include h2 in
lemma down_at (q : Fin n → ℕ) (a j : Fin n) :
    ∀ m, ReflTransGen R (Function.update q a (q a + m), j) (q, j)
  | 0 => by simpa using (ReflTransGen.refl : ReflTransGen R (q, j) (q, j))
  | m + 1 => by
    refine ReflTransGen.head ?_ (down_at q a j m)
    have := h2 (Function.update q a (q a + (m + 1)), j) a (by simp; omega)
    simpa [dep, Function.update_idem] using this

include h1 h2 h3 in
lemma switch_any (q : Fin n → ℕ) (s j : Fin n) : ReflTransGen R (q, s) (q, j) := by
  by_cases hjs : j = s
  · subst hjs; exact ReflTransGen.refl
  have hA := up_stored R h1 q s (q j + 1)
  have hB : R (Function.update q s (q s + (q j + 1)), s) (Function.update q s (q s + (q j + 1)), j) := by
    have := h3 (Function.update q s (q s + (q j + 1)), s) j (by
      simp [Function.update_of_ne hjs]; omega)
    simpa [sw] using this
  exact (hA.tail hB).trans (down_at R h2 q s j (q j + 1))

include h1 h2 h3 in
lemma up_any (q : Fin n → ℕ) (s j : Fin n) :
    ReflTransGen R (q, s) (Function.update q j (q j + 1), s) := by
  refine (switch_any R h1 h2 h3 q s j).trans ?_
  refine ReflTransGen.head (h1 (q, j)) ?_
  exact switch_any R h1 h2 h3 _ j s

include h1 h2 h3 in
lemma raise_coord (q : Fin n → ℕ) (s j : Fin n) :
    ∀ m, ReflTransGen R (Function.update q j 0, s) (Function.update q j m, s)
  | 0 => ReflTransGen.refl
  | m + 1 => by
    refine (raise_coord q s j m).trans ?_
    have := up_any R h1 h2 h3 (Function.update q j m) s j
    simpa [Function.update_idem] using this

include h2 in
lemma lower_coord (q : Fin n → ℕ) (s j : Fin n) :
    ∀ m, ReflTransGen R (Function.update q j m, s) (Function.update q j 0, s)
  | 0 => ReflTransGen.refl
  | m + 1 => by
    refine ReflTransGen.head ?_ (lower_coord q s j m)
    have := h2 (Function.update q j (m + 1), s) j (by simp)
    simpa [dep, Function.update_idem] using this

include h1 h2 h3 in
lemma reach_all (x y : State n) : ReflTransGen R x y := by
  classical
  obtain ⟨q, s⟩ := x
  obtain ⟨q', k⟩ := y
  have key : ∀ A : Finset (Fin n),
      ReflTransGen R (q, s) (fun j => if j ∈ A then q' j else q j, s) := by
    intro A
    induction A using Finset.induction_on with
    | empty => simpa using (ReflTransGen.refl : ReflTransGen R (q, s) (q, s))
    | insert a A haA ih =>
      set g : Fin n → ℕ := fun j => if j ∈ A then q' j else q j with hg
      have hnew : (fun j => if j ∈ insert a A then q' j else q j) = Function.update g a (q' a) := by
        funext j
        by_cases hja : j = a
        · subst hja; simp
        · simp [hja, hg]
      rw [hnew]
      refine ih.trans ?_
      have e1 : Function.update g a (g a) = g := Function.update_eq_self a g
      have hl := lower_coord R h2 g s a (g a)
      rw [e1] at hl
      exact hl.trans (raise_coord R h1 h2 h3 g s a (q' a))
  have := key Finset.univ
  simp only [Finset.mem_univ, if_true] at this
  exact this.trans (switch_any R h1 h2 h3 q' s k)

end Reach

section Drift

lemma Dr_affine (lam α : ℝ) (μ : Fin n → ℝ) (x : State n) (a b : ℝ) (f : State n → ℝ) :
    Dr lam α μ x (fun y => a * f y + b) = a * Dr lam α μ x f + b * hold lam α μ x := by
  unfold Dr hold
  have e1 : ∑ j, (if 1 ≤ x.1 j then μ j * (a * f (dep x j) + b) else 0)
      = a * ∑ j, (if 1 ≤ x.1 j then μ j * f (dep x j) else 0)
        + b * ∑ j, (if 1 ≤ x.1 j then μ j else 0) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs <;> ring
  have e2 : ∑ j, (if x.1 j < x.1 x.2 then α * (a * f (sw x j) + b) else 0)
      = a * ∑ j, (if x.1 j < x.1 x.2 then α * f (sw x j) else 0)
        + b * ∑ j, (if x.1 j < x.1 x.2 then α else 0) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs <;> ring
  rw [e1, e2]
  ring

lemma Dr_add (lam α : ℝ) (μ : Fin n → ℝ) (x : State n) (f g : State n → ℝ) :
    Dr lam α μ x (fun y => f y + g y) = Dr lam α μ x f + Dr lam α μ x g := by
  unfold Dr
  have e1 : ∑ j, (if 1 ≤ x.1 j then μ j * (f (dep x j) + g (dep x j)) else 0)
      = ∑ j, (if 1 ≤ x.1 j then μ j * f (dep x j) else 0)
        + ∑ j, (if 1 ≤ x.1 j then μ j * g (dep x j) else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs <;> ring
  have e2 : ∑ j, (if x.1 j < x.1 x.2 then α * (f (sw x j) + g (sw x j)) else 0)
      = ∑ j, (if x.1 j < x.1 x.2 then α * f (sw x j) else 0)
        + ∑ j, (if x.1 j < x.1 x.2 then α * g (sw x j) else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs <;> ring
  rw [e1, e2]
  ring

lemma hasSum_drift (lam α : ℝ) (μ : Fin n → ℝ) (x : State n) (f : State n → ℝ) :
    HasSum (fun y => (f y - f x) * gen n lam α μ x y) (Dr lam α μ x (fun y => f y - f x)) := by
  have hfun : (fun y => (f y - f x) * gen n lam α μ x y)
      = fun y => offRate lam α μ x y * (f y - f x) := by
    funext y
    rw [gen_eq]
    by_cases h : y = x
    · subst h; rw [offRate_self]; simp
    · rw [if_neg h, zero_add, mul_comm]
  rw [hfun]
  exact hasSum_offRate lam α μ x _

lemma sum_update_sq (q : Fin n → ℕ) (j : Fin n) (v : ℕ) :
    ∑ k, ((Function.update q j v k : ℕ) : ℝ) ^ 2
      = ∑ k, ((q k : ℕ) : ℝ) ^ 2 - ((q j : ℕ) : ℝ) ^ 2 + ((v : ℕ) : ℝ) ^ 2 := by
  classical
  have hfun : (fun k => ((Function.update q j v k : ℕ) : ℝ) ^ 2)
      = Function.update (fun k => ((q k : ℕ) : ℝ) ^ 2) j (((v : ℕ) : ℝ) ^ 2) := by
    funext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [Function.update_of_ne hk]
  rw [hfun, Finset.sum_update_of_mem (Finset.mem_univ j), Finset.sdiff_singleton_eq_erase,
    ← Finset.sum_erase_add Finset.univ (fun k => ((q k : ℕ) : ℝ) ^ 2) (Finset.mem_univ j)]
  ring

lemma A4_value (lam α : ℝ) (μ : Fin n → ℝ) (q : Fin n → ℕ) (i : Fin n) :
    Dr lam α μ (q, i) (fun y => Xi2 y - Xi2 (q, i))
      = lam * n * (2 * (q i : ℝ) + 1)
          - ∑ j, μ j * (2 * (q j : ℝ) - 1) * (if 1 ≤ q j then 1 else 0) := by
  classical
  unfold Dr
  simp only [Xi2, arr, dep, sw, sum_update_sq]
  have e2 : ∑ j, (if 1 ≤ q j then μ j * (∑ k, ((q k : ℕ) : ℝ) ^ 2 - ((q j : ℕ) : ℝ) ^ 2
      + (((q j - 1 : ℕ)) : ℝ) ^ 2 - ∑ k, ((q k : ℕ) : ℝ) ^ 2) else 0)
      = - ∑ j, μ j * (2 * (q j : ℝ) - 1) * (if 1 ≤ q j then 1 else 0) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs with h
    · rw [Nat.cast_sub h]; push_cast; ring
    · ring
  rw [e2]
  simp
  ring

variable [NeZero n]

lemma muMax_ge (μ : Fin n → ℝ) (j : Fin n) : μ j ≤ muMax μ :=
  Finset.le_sup' μ (Finset.mem_univ j)

lemma muMin_le (μ : Fin n → ℝ) (j : Fin n) : muMin μ ≤ μ j :=
  Finset.inf'_le μ (Finset.mem_univ j)

lemma muMin_pos (μ : Fin n → ℝ) (hμ : ∀ j, 0 < μ j) : 0 < muMin μ := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty μ
  unfold muMin; rw [hj]; exact hμ j

lemma A3_value (lam α : ℝ) (μ : Fin n → ℝ) (hα : 0 < α) (q : Fin n → ℕ) (i : Fin n) :
    Dr lam α μ (q, i) (fun y => Xi1 μ α y - Xi1 μ α (q, i))
      = lam * n * (2 * muMax μ / α) - 2 * muMax μ / α * μ i * (if 1 ≤ q i then 1 else 0)
          - ∑ j, 2 * muMax μ * max ((q i : ℝ) - (q j : ℝ)) 0 := by
  classical
  unfold Dr
  simp only [Xi1, arr, dep, sw, Function.update_self]
  have e2 : ∑ j, (if 1 ≤ q j then μ j * (2 * muMax μ / α * ((Function.update q j (q j - 1) i : ℕ) : ℝ)
      - 2 * muMax μ / α * (q i : ℝ)) else 0)
      = - (2 * muMax μ / α * μ i * (if 1 ≤ q i then 1 else 0)) := by
    rw [Finset.sum_eq_single i]
    · simp only [Function.update_self]
      split_ifs with h
      · rw [Nat.cast_sub h]; push_cast; ring
      · ring
    · intro j _ hji
      rw [Function.update_of_ne (Ne.symm hji)]
      split_ifs <;> ring
    · simp
  have e3 : ∑ j, (if q j < q i then α * (2 * muMax μ / α * (q j : ℝ) - 2 * muMax μ / α * (q i : ℝ))
      else 0) = - ∑ j, 2 * muMax μ * max ((q i : ℝ) - (q j : ℝ)) 0 := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs with h
    · have h' : (q j : ℝ) < q i := by exact_mod_cast h
      rw [max_eq_left (by linarith)]
      field_simp
      ring
    · have h' : (q i : ℝ) ≤ q j := by exact_mod_cast (not_lt.1 h)
      rw [max_eq_right (by linarith)]
      ring
  rw [e2, e3]
  push_cast
  ring

end Drift

section Bound

variable [NeZero n]

lemma Fn_finite (lam α : ℝ) (μ : Fin n → ℝ) : (Fn n lam α μ).Finite := by
  set B := (lam * n * (1 + 2 * muMax μ / α) + n + 1) / (2 * min (1 - lam) (muMin μ))
  set N := ⌈B⌉₊
  have hsub : Fn n lam α μ ⊆ (Set.pi Set.univ (fun _ => Set.Iic N)) ×ˢ Set.univ := by
    intro x hx
    simp only [Fn, Set.mem_setOf_eq] at hx
    refine ⟨fun j _ => ?_, Set.mem_univ _⟩
    simp only [Set.mem_Iic]
    have h1 : ((x.1 j : ℕ) : ℝ) ≤ ∑ k, ((x.1 k : ℕ) : ℝ) :=
      Finset.single_le_sum (f := fun k => ((x.1 k : ℕ) : ℝ)) (fun k _ => by positivity)
        (Finset.mem_univ j)
    have h2 : ((x.1 j : ℕ) : ℝ) ≤ N := by
      have := Nat.le_ceil B
      linarith
    exact_mod_cast h2
  exact Set.Finite.subset ((Set.Finite.pi (fun _ => Set.finite_Iic N)).prod Set.finite_univ) hsub

lemma drift_bound (lam α : ℝ) (μ : Fin n → ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hα : 0 < α) (hμ : μ ∈ Sigma n) (x : State n) (hx : x ∉ Fn n lam α μ) :
    Dr lam α μ x (fun y => Xi μ α y - Xi μ α x) ≤ -1 := by
  obtain ⟨q, i⟩ := x
  have hsplit : (fun y => Xi μ α y - Xi μ α (q, i))
      = fun y => (Xi1 μ α y - Xi1 μ α (q, i)) + (Xi2 y - Xi2 (q, i)) := by
    funext y; unfold Xi; ring
  rw [hsplit, Dr_add, A3_value lam α μ hα, A4_value]
  obtain ⟨hμpos, hμsum⟩ := hμ
  set M := muMax μ
  set m := min (1 - lam) (muMin μ)
  set c := 2 * M / α
  have hmpos : 0 < m := lt_min (by linarith) (muMin_pos μ hμpos)
  have hm1 : m ≤ 1 - lam := min_le_left _ _
  have hmμ : ∀ j, m ≤ μ j := fun j => (min_le_right _ _).trans (muMin_le μ j)
  have hM : ∀ j, μ j ≤ M := fun j => muMax_ge μ j
  have hMpos : 0 < M := lt_of_lt_of_le (hμpos i) (hM i)
  have hc : 0 ≤ c := by positivity
  have hn : (0 : ℝ) ≤ n := by positivity
  have hqi : (0 : ℝ) ≤ q i := by positivity
  -- notation
  set Sq := ∑ j, (q j : ℝ)
  set S1 := ∑ j, μ j * (q j : ℝ)
  set S2 := ∑ j, max ((q i : ℝ) - (q j : ℝ)) 0
  set S3 := ∑ j, μ j * max ((q j : ℝ) - (q i : ℝ)) 0
  set S4 := ∑ j, max ((q j : ℝ) - (q i : ℝ)) 0
  have hF5 : lam * n * (1 + c) + n + 1 ≤ 2 * m * Sq := by
    simp only [Fn, Set.mem_setOf_eq, not_lt] at hx
    rw [div_le_iff₀ (by positivity)] at hx
    linarith
  have hF1 : n * (q i : ℝ) + S3 ≤ S1 + M * S2 := by
    have hn' : (n : ℝ) * q i = ∑ j, μ j * (q i : ℝ) := by rw [← Finset.sum_mul, hμsum]
    rw [hn', Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun j _ => ?_)
    rcases le_total (q j : ℝ) (q i) with h | h
    · rw [max_eq_right (by linarith : (q j : ℝ) - q i ≤ 0), max_eq_left (by linarith)]
      have := hM j
      nlinarith
    · rw [max_eq_left (by linarith : (0 : ℝ) ≤ q j - q i), max_eq_right (by linarith)]
      ring_nf; rfl
  have hF2 : m * S4 ≤ S3 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    exact mul_le_mul_of_nonneg_right (hmμ j) (le_max_right _ _)
  have hF3 : Sq ≤ n * (q i : ℝ) + S4 := by
    have hn' : (n : ℝ) * q i = ∑ _j : Fin n, (q i : ℝ) := by simp
    rw [hn', ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun j _ => ?_)
    have := le_max_left ((q j : ℝ) - q i) 0
    linarith
  have hF4 : 2 * S1 - n ≤ ∑ j, μ j * (2 * (q j : ℝ) - 1) * (if 1 ≤ q j then 1 else 0) := by
    have : 2 * S1 - n = ∑ j, (2 * (μ j * (q j : ℝ)) - μ j) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hμsum]
    rw [this]
    refine Finset.sum_le_sum (fun j _ => ?_)
    split_ifs with h
    · ring_nf; rfl
    · have : q j = 0 := by omega
      rw [this]; simp; exact (hμpos j).le
  have hA3 : 0 ≤ c * μ i * (if 1 ≤ q i then 1 else 0) := by
    have := (hμpos i).le
    split_ifs <;> positivity
  have hS2 : ∑ j, 2 * M * max ((q i : ℝ) - (q j : ℝ)) 0 = 2 * M * S2 := by
    rw [Finset.mul_sum]
  rw [hS2]
  have hp1 : m * (n * (q i : ℝ)) ≤ (1 - lam) * (n * (q i : ℝ)) :=
    mul_le_mul_of_nonneg_right hm1 (by positivity)
  have hp2 : m * Sq ≤ m * (n * (q i : ℝ) + S4) := mul_le_mul_of_nonneg_left hF3 hmpos.le
  nlinarith

end Bound

end

end SDChain

open StableDispatch.Markov in
theorem solution (n : ℕ) [NeZero n] (lam α : ℝ) (μ : Fin n → ℝ) (hlam0 : 0 < lam)
    (hlam1 : lam < 1) (hα : 0 < α) (hμ : μ ∈ Sigma n) :
    ∀ x : State n,
      Summable (fun y : State n => if y = x then 0 else Xi μ α y * gen n lam α μ x y) := by
  intro x
  have hfun : (fun y : State n => if y = x then 0 else Xi μ α y * gen n lam α μ x y)
      = fun y => SDChain.offRate lam α μ x y * Xi μ α y := by
    funext y
    by_cases h : y = x
    · subst h; rw [if_pos rfl, SDChain.offRate_self, zero_mul]
    · rw [if_neg h, SDChain.gen_eq, if_neg h, zero_add, mul_comm]
  rw [hfun]
  exact (SDChain.hasSum_offRate lam α μ x _).summable
