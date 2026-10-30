-- Prove2me | solution 1 for StableDispatch.Markov.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T12:18:44.634478+00:00
-- url     : https://prove2.me/submissions/ebcd0ecc-8601-4dd3-9219-4cbf070c4d83

import Mathlib
import Definitions.Def_MatrixAnalytic_Tree_Process
import Definitions.Def_StableDispatch_Markov_Setting
import Theorems.Thm_StableDispatch_Markov_irreducible
import Theorems.Thm_StableDispatch_Markov_exit_sum_finite
import Theorems.Thm_StableDispatch_Markov_drift_outside_Fn

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

namespace SDGen

noncomputable section

open MatrixAnalytic.Tree

variable {V : Type*} [Countable V] [DecidableEq V]

lemma jumpP_off (Q : V → V → ℝ) (x y : V) (hh : 0 < holdRate Q x) :
    jumpP Q x y = (if y = x then 0 else Q x y) / holdRate Q x := by
  unfold jumpP
  rw [if_neg hh.ne']
  split_ifs <;> simp

lemma jumpP_nonneg (Q : V → V → ℝ) (hQ : IsGenerator Q) (x y : V) (hh : 0 < holdRate Q x) :
    0 ≤ jumpP Q x y := by
  rw [jumpP_off Q x y hh]
  refine div_nonneg ?_ hh.le
  split_ifs with h
  · exact le_rfl
  · exact hQ.1 x y (Ne.symm h)

lemma hasSum_off (Q : V → V → ℝ) (hQ : IsGenerator Q) (x : V) :
    HasSum (fun y => if y = x then 0 else Q x y) (holdRate Q x) := by
  have h := (hQ.2 x).sub (hasSum_ite_eq x (Q x x))
  have hfun : (fun y => if y = x then 0 else Q x y) = fun y => Q x y - (if y = x then Q x x else 0) := by
    funext y; by_cases hy : y = x
    · subst hy; simp
    · simp [hy]
  rw [hfun]
  simpa [holdRate] using h

lemma stoch (Q : V → V → ℝ) (hQ : IsGenerator Q) (x : V) (hh : 0 < holdRate Q x) :
    ∑' y, ENNReal.ofReal (jumpP Q x y) = 1 := by
  have hs : HasSum (fun y => jumpP Q x y) 1 := by
    have := (hasSum_off Q hQ x).div_const (holdRate Q x)
    rw [div_self hh.ne'] at this
    have hfun : (fun y => jumpP Q x y) = fun y => (if y = x then 0 else Q x y) / holdRate Q x := by
      funext y; exact jumpP_off Q x y hh
    rw [hfun]; exact this
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun y => jumpP_nonneg Q hQ x y hh) hs.summable, hs.tsum_eq,
    ENNReal.ofReal_one]

lemma irr (Q : V → V → ℝ) (hh : ∀ x, 0 < holdRate Q x) (hI : IsIrreducibleGen Q) (x y : V) :
    Relation.ReflTransGen (fun a b => 0 < jumpP Q a b) x y := by
  refine Relation.ReflTransGen.mono (fun a b hab => ?_) x y (hI x y)
  rw [jumpP_off Q a b (hh a), if_neg hab.1.symm]
  exact div_pos hab.2 (hh a)

lemma tsum_jump (Q : V → V → ℝ) (hQ : IsGenerator Q) (x : V) (hh : 0 < holdRate Q x)
    (Ξ : V → ℝ) (hΞ : ∀ y, 0 ≤ Ξ y) (K : ℝ) (hK : 0 ≤ K)
    (hsum : Summable (fun y => if y = x then 0 else Ξ y * Q x y)) :
    ∑' y, ENNReal.ofReal (jumpP Q x y) * ENNReal.ofReal (K * Ξ y)
      = ENNReal.ofReal (K / holdRate Q x * ∑' y, (if y = x then 0 else Ξ y * Q x y)) := by
  have hs : HasSum (fun y => jumpP Q x y * (K * Ξ y))
      (K / holdRate Q x * ∑' y, (if y = x then 0 else Ξ y * Q x y)) := by
    have := hsum.hasSum.mul_left (K / holdRate Q x)
    have hfun : (fun y => jumpP Q x y * (K * Ξ y))
        = fun y => K / holdRate Q x * (if y = x then 0 else Ξ y * Q x y) := by
      funext y
      rw [jumpP_off Q x y hh]
      split_ifs <;> ring
    rw [hfun]; exact this
  have hnn : ∀ y, 0 ≤ jumpP Q x y * (K * Ξ y) :=
    fun y => mul_nonneg (jumpP_nonneg Q hQ x y hh) (mul_nonneg hK (hΞ y))
  rw [← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg hnn hs.summable]
  refine tsum_congr (fun y => ?_)
  rw [ENNReal.ofReal_mul (jumpP_nonneg Q hQ x y hh)]

lemma drift_value (Q : V → V → ℝ) (hQ : IsGenerator Q) (x : V) (Ξ : V → ℝ)
    (hsum : Summable (fun y => if y = x then 0 else Ξ y * Q x y)) (d : ℝ)
    (hd : HasSum (fun y => (Ξ y - Ξ x) * Q x y) d) :
    ∑' y, (if y = x then 0 else Ξ y * Q x y) = d + Ξ x * holdRate Q x := by
  have h2 := hsum.hasSum.sub ((hasSum_off Q hQ x).mul_left (Ξ x))
  have hfun : (fun y => (if y = x then 0 else Ξ y * Q x y) - Ξ x * (if y = x then 0 else Q x y))
      = fun y => (Ξ y - Ξ x) * Q x y := by
    funext y; by_cases hy : y = x
    · subst hy; simp
    · simp [hy]; ring
  rw [hfun] at h2
  have := h2.unique hd
  linarith

end

end SDGen

open StableDispatch.Markov MatrixAnalytic.Tree in
theorem solution (n : ℕ) (α : ℝ) (hα : 0 < α) :
    ∀ lam : ℝ, 0 < lam → lam < 1 → stabilityRegion n lam α = Sigma n := by
  intro lam hlam0 hlam1
  ext μ
  constructor
  · exact fun h => h.1
  · intro hμ
    refine ⟨hμ, ?_⟩
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      intro x; exact x.2.elim0
    have : NeZero n := ⟨hn.ne'⟩
    obtain ⟨hgen, hirr⟩ := irreducible n lam α μ hlam0 hlam1 hα hμ
    have hexit := exit_sum_finite n lam α μ hlam0 hlam1 hα hμ
    obtain ⟨hFfin, hdr⟩ := drift_outside_Fn n lam α μ hlam0 hlam1 hα hμ
    obtain ⟨hμpos, hμsum⟩ := hμ
    have hnr : (0:ℝ) < n := by exact_mod_cast hn
    -- the holding rates
    have hhold : ∀ x : State n, holdRate (gen n lam α μ) x
        = lam * n + ∑ j, (if 1 ≤ x.1 j then μ j else 0) + ∑ j, (if x.1 j < x.1 x.2 then α else 0) := by
      intro x; simp [holdRate, gen]
    have hge : ∀ x : State n, lam * n ≤ holdRate (gen n lam α μ) x := by
      intro x
      rw [hhold]
      have h1 : 0 ≤ ∑ j, (if 1 ≤ x.1 j then μ j else 0) :=
        Finset.sum_nonneg (fun j _ => by split_ifs <;> [exact (hμpos j).le; exact le_rfl])
      have h2 : 0 ≤ ∑ j, (if x.1 j < x.1 x.2 then α else 0) :=
        Finset.sum_nonneg (fun j _ => by split_ifs <;> [exact hα.le; exact le_rfl])
      linarith
    set K : ℝ := lam * n + n + n * α with hKdef
    have hle : ∀ x : State n, holdRate (gen n lam α μ) x ≤ K := by
      intro x
      rw [hhold]
      have h1 : ∑ j, (if 1 ≤ x.1 j then μ j else 0) ≤ ∑ j, μ j :=
        Finset.sum_le_sum (fun j _ => by split_ifs <;> [exact le_rfl; exact (hμpos j).le])
      have h2 : ∑ j, (if x.1 j < x.1 x.2 then α else 0) ≤ ∑ _j : Fin n, α :=
        Finset.sum_le_sum (fun j _ => by split_ifs <;> [exact le_rfl; exact hα.le])
      simp at h2
      linarith
    have hpos : ∀ x : State n, 0 < holdRate (gen n lam α μ) x :=
      fun x => lt_of_lt_of_le (by positivity) (hge x)
    have hK0 : 0 ≤ K := by positivity
    have hMax : 0 < muMax μ :=
      lt_of_lt_of_le (hμpos 0) (Finset.le_sup' μ (Finset.mem_univ 0))
    have hXi : ∀ y, 0 ≤ Xi μ α y := by
      intro y
      unfold Xi Xi1 Xi2
      have : 0 ≤ ∑ j, ((y.1 j : ℕ) : ℝ) ^ 2 := Finset.sum_nonneg (fun j _ => by positivity)
      have : 0 ≤ 2 * muMax μ / α * ((y.1 y.2 : ℕ) : ℝ) := by positivity
      linarith
    refine SDFoster.foster_ct (gen n lam α μ) (lam * n) (by positivity) hge
      (fun x => SDGen.stoch _ hgen x (hpos x)) (SDGen.irr _ hpos hirr) (Fn n lam α μ) hFfin
      (fun y => ENNReal.ofReal (K * Xi μ α y)) (fun y => ENNReal.ofReal_ne_top) ?_ ?_
    · intro y hy
      obtain ⟨d, hd, hd1⟩ := hdr y hy
      have hS0 : 0 ≤ ∑' w, (if w = y then 0 else Xi μ α w * gen n lam α μ y w) :=
        tsum_nonneg (fun w => by
          split_ifs with hw
          · exact le_rfl
          · exact mul_nonneg (hXi w) (hgen.1 y w (Ne.symm hw)))
      have hval := SDGen.drift_value _ hgen y (Xi μ α) (hexit y) d hd
      rw [SDGen.tsum_jump _ hgen y (hpos y) (Xi μ α) hXi K hK0 (hexit y)]
      have hr : 0 ≤ K / holdRate (gen n lam α μ) y
          * ∑' w, (if w = y then 0 else Xi μ α w * gen n lam α μ y w) :=
        mul_nonneg (div_nonneg hK0 (hpos y).le) hS0
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one hr]
      apply ENNReal.ofReal_le_ofReal
      rw [hval]
      set h := holdRate (gen n lam α μ) y
      have hh : 0 < h := hpos y
      have hKh : h ≤ K := hle y
      have hKD : K * d ≤ -h := by nlinarith
      have e : K / h * (d + Xi μ α y * h) = K * d / h + K * Xi μ α y := by
        field_simp
      rw [e]
      have : K * d / h ≤ -1 := by
        rw [div_le_iff₀ hh]; linarith
      linarith
    · intro y _
      rw [SDGen.tsum_jump _ hgen y (hpos y) (Xi μ α) hXi K hK0 (hexit y)]
      exact ENNReal.ofReal_ne_top
