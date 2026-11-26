-- Prove2me | solution 1 for PvsNP.PublicGame.lower_labels_coin_depth_bound
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T17:54:17.302885+00:00
-- url     : https://prove2.me/submissions/564411e5-3387-426e-bbe1-3d0ec703aa97

import Definitions.Def_RoundedPublicCoinLowerLabels
import Mathlib.Tactic

set_option autoImplicit false

namespace PvsNP.PublicGame

variable {S : Type}

/-- Each numerator fits in `r+1` binary bits, including at certainty. -/
theorem value_le_power (G : Game S) (r : ℕ) (s : S) : value G r s ≤ 2^r := by
  induction r generalizing s with
  | zero => cases move : G.move 0 s <;> simp [value,finish,move]; split <;> decide
  | succ r ih =>
    cases move : G.move (r+1) s with
    | stop b => cases b <;> simp [value,move]
    | pick s₀ s₁ =>
      simp only [value,move,Nat.pow_succ']
      exact Nat.mul_le_mul_left 2 (max_le (ih _) (ih _))
    | toss s₀ s₁ =>
      simp only [value,move,Nat.pow_succ']
      have h₀ := ih s₀
      have h₁ := ih s₁
      omega

theorem lowerValue_valid (G : Game S) (M H : ℕ) :
    LowerLabels G M H (lowerValue G M) := by
  intro r _ s
  cases r with
  | zero => rfl
  | succ r =>
    cases move : G.move (r+1) s with
    | stop b => cases b <;> simp [lowerValue,doubleUpdate,move]
    | pick a b => simp [lowerValue,doubleUpdate,move]
    | toss a b =>
      simp only [lowerValue,doubleUpdate,move]
      simpa only [Nat.mul_comm 2] using
        Nat.div_mul_le_self (lowerValue G M r a + lowerValue G M r b) 2

/-- The rounded-down recurrence gives the greatest feasible local lower
label function. In particular the verifier may ignore all zero labels. -/
theorem lowerValue_dominates {G : Game S} {M H : ℕ} {u : ℕ → S → ℕ}
    (valid : LowerLabels G M H u) (r : ℕ) (fit : r ≤ H) (s : S) :
    u r s ≤ lowerValue G M r s := by
  induction r generalizing s with
  | zero =>
    have thisMove := valid 0 fit s
    simp only [lowerValue]
    simp only [doubleUpdate] at thisMove
    omega
  | succ r ih =>
    have prev : r ≤ H := by omega
    have thisMove := valid (r+1) fit s
    cases move : G.move (r+1) s with
    | stop b =>
      simp only [doubleUpdate,move] at thisMove
      cases b <;> simp_all [lowerValue]
    | pick a b =>
      simp only [lowerValue,move]
      simp only [doubleUpdate,move] at thisMove
      exact (by omega : u (r+1) s ≤ max (u r a) (u r b)).trans
        (max_le_max (ih prev a) (ih prev b))
    | toss a b =>
      simp only [lowerValue,move]
      simp only [doubleUpdate,move] at thisMove
      apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
      rw [Nat.mul_comm _ 2]
      exact thisMove.trans (Nat.add_le_add (ih prev a) (ih prev b))

/-- The approximation error accumulates with coin depth, even if
deterministic stretches have a much larger horizon. -/
theorem lowerValue_error (G : Game S) (M r : ℕ) (s : S) :
    lowerValue G M r s * 2^r ≤ M*value G r s ∧
    M*value G r s ≤ (lowerValue G M r s + coinDepth G r s)*2^r := by
  induction r generalizing s with
  | zero => simp [lowerValue,coinDepth,value]
  | succ r ih =>
    let D : ℕ := 2^r
    have power : 2^(r+1) = 2*D := Nat.pow_succ' ..
    cases move : G.move (r+1) s with
    | stop b => cases b <;> simp [lowerValue,coinDepth,value,move]
    | pick a b =>
      let l := max (lowerValue G M r a) (lowerValue G M r b)
      let c := max (coinDepth G r a) (coinDepth G r b)
      let v := max (value G r a) (value G r b)
      simp only [lowerValue,coinDepth,value,move,power]
      change l*(2*D) ≤ M*(2*v) ∧ M*(2*v) ≤ (l+c)*(2*D)
      have below : l*D ≤ M*v := by
        dsimp only [l,v]
        rw [max_mul, mul_max]
        exact max_le_max (ih a).1 (ih b).1
      have above : M*v ≤ (l+c)*D := by
        dsimp only [v]
        rw [mul_max]
        apply max_le
        · apply (ih a).2.trans
          exact Nat.mul_le_mul_right _ (Nat.add_le_add (le_max_left _ _) (le_max_left _ _))
        · apply (ih b).2.trans
          exact Nat.mul_le_mul_right _ (Nat.add_le_add (le_max_right _ _) (le_max_right _ _))
      exact ⟨by simpa only [Nat.mul_left_comm _ 2] using Nat.mul_le_mul_left 2 below,
        by simpa only [Nat.mul_left_comm _ 2] using Nat.mul_le_mul_left 2 above⟩
    | toss a b =>
      let l := lowerValue G M r a + lowerValue G M r b
      let c := max (coinDepth G r a) (coinDepth G r b)
      let v := value G r a + value G r b
      simp only [lowerValue,coinDepth,value,move,power]
      change (l/2)*(2*D) ≤ M*v ∧ M*v ≤ (l/2+(c+1))*(2*D)
      have floor : 2*(l/2) ≤ l := Nat.mul_comm (l/2) 2 ▸ Nat.div_mul_le_self l 2
      have remainder : l ≤ 2*(l/2)+1 := by
        have eq := Nat.mod_add_div l 2
        have small := Nat.mod_lt l (by decide : 0 < 2)
        omega
      constructor
      · calc
          _ = (2*(l/2))*D := by ring
          _ ≤ l*D := Nat.mul_le_mul_right _ floor
          _ ≤ M*v := by
            dsimp only [l,v]
            rw [Nat.add_mul,Nat.mul_add]
            exact Nat.add_le_add (ih a).1 (ih b).1
      · have f (q : S) (cap : coinDepth G r q ≤ c) :
            M*value G r q ≤ (lowerValue G M r q+c)*D :=
          (ih q).2.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_left cap _))
        calc
          _ ≤ (l + 2*c)*D := by
            dsimp only [v,l]
            rw [Nat.mul_add]
            have bound := Nat.add_le_add (f a (le_max_left _ _)) (f b (le_max_right _ _))
            convert bound using 1; ring
          _ ≤ (2*(l/2)+1+2*c)*D := Nat.mul_le_mul_right _ (Nat.add_le_add_right remainder _)
          _ ≤ (l/2+(c+1))*(2*D) := by
            have amount : 2*(l/2)+1+2*c ≤ 2*(l/2+(c+1)) := by omega
            simpa only [Nat.mul_assoc, Nat.mul_left_comm 2] using Nat.mul_le_mul_right D amount

/-- Any locally justified label is a lower bound on the optimal
acceptance probability, after accounting for its integer scale. -/
theorem lowerLabels_sound {G : Game S} {M H : ℕ} {u : ℕ → S → ℕ}
    (valid : LowerLabels G M H u) (r : ℕ) (fit : r ≤ H) (s : S) :
    u r s * 2^r ≤ M*value G r s :=
  (Nat.mul_le_mul_right _ (lowerValue_dominates valid r fit s)).trans (lowerValue_error G M r s).1

theorem lowerValue_trim_valid (G : Game S) (keep : ℕ → S → Bool) (M H : ℕ) :
    LowerLabels G M H (lowerValue (trimGame G keep) M) := by
  intro r fit s
  have valid := lowerValue_valid (trimGame G keep) M H r fit s
  cases r with
  | zero => cases h : keep 0 s <;> simp_all [lowerValue,doubleUpdate,finish,trimGame]
  | succ r =>
    cases h : keep (r+1) s
    · simp [lowerValue,trimGame,h]
    · simpa only [doubleUpdate, trimGame, h, if_true] using valid


end PvsNP.PublicGame

open PvsNP.PublicGame

theorem solution {S : Type} (G : Game S) (M H : ℕ) (s : S) :
    let l := lowerValue G M
    LowerLabels G M H l ∧
    (∀ u : ℕ → S → ℕ, LowerLabels G M H u → u H s ≤ l H s) ∧
    l H s * 2^H ≤ M * value G H s ∧
    M * value G H s ≤ (l H s + coinDepth G H s) * 2^H ∧
    (∀ keep : ℕ → S → Bool, LowerLabels G M H (lowerValue (trimGame G keep) M)) := by
  obtain ⟨low, high⟩ := lowerValue_error G M H s
  exact ⟨lowerValue_valid G M H, fun _ valid => lowerValue_dominates valid H le_rfl s,
    low, high, fun keep => lowerValue_trim_valid G keep M H⟩
