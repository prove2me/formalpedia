-- Prove2me | solution 1 for PvsNP.PublicGame.rounded_labels_certify_gap
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T17:35:19.34959+00:00
-- url     : https://prove2.me/submissions/07121e2b-3c00-4fa5-a8d0-10d9d4ec37eb

import Definitions.Def_RoundedPublicCoinGame
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 750000

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

private theorem update_error (G : Game S) (M : ℕ) (u : ℕ → S → ℕ) (r : ℕ) (s : S)
    (ih : ∀ q ∈ children (G.move (r+1) s), u r q * 2^r ≤ M * value G r q + r*2^r ∧
      M * value G r q ≤ u r q * 2^r + r*2^r) :
    doubleUpdate G M u (r+1) s * 2^r ≤ M*value G (r+1) s + 2*(r*2^r) ∧
    M*value G (r+1) s ≤ doubleUpdate G M u (r+1) s * 2^r + 2*(r*2^r) := by
  cases move : G.move (r+1) s with
  | stop b =>
    simp only [doubleUpdate, value, move]
    cases b <;> simp [Nat.pow_succ', Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
  | pick p q =>
    simp only [doubleUpdate, value, move]
    have upper (z : S) (mem : z ∈ children (G.move (r+1) s)) (part : value G r z ≤ max (value G r p) (value G r q)) :
        u r z * 2^r ≤ M*max (value G r p) (value G r q) + r*2^r :=
      (ih z mem).1.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ part) _)
    have lower (z : S) (mem : z ∈ children (G.move (r+1) s)) (part : u r z ≤ max (u r p) (u r q)) :
        M*value G r z ≤ max (u r p) (u r q) * 2^r + r*2^r :=
      (ih z mem).2.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ part) _)
    have up : max (u r p) (u r q) * 2^r ≤ M*max (value G r p) (value G r q) + r*2^r := by
      rcases le_total (u r p) (u r q) with le | ge
      · rw [max_eq_right le]
        exact upper q (by simp [move,children]) (le_max_right _ _)
      · rw [max_eq_left ge]
        exact upper p (by simp [move,children]) (le_max_left _ _)
    have down : M*max (value G r p) (value G r q) ≤ max (u r p) (u r q) * 2^r + r*2^r := by
      rcases le_total (value G r p) (value G r q) with le | ge
      · rw [max_eq_right le]
        exact lower q (by simp [move,children]) (le_max_right _ _)
      · rw [max_eq_left ge]
        exact lower p (by simp [move,children]) (le_max_left _ _)
    constructor
    · calc
        _ = 2*(max (u r p) (u r q)*2^r) := by ring
        _ ≤ 2*(M*max (value G r p) (value G r q) + r*2^r) := Nat.mul_le_mul_left _ up
        _ = _ := by ring
    · calc
        _ = 2*(M*max (value G r p) (value G r q)) := by ring
        _ ≤ 2*(max (u r p) (u r q)*2^r + r*2^r) := Nat.mul_le_mul_left _ down
        _ = _ := by ring
  | toss p q =>
    simp only [doubleUpdate, value, move, Nat.add_mul, Nat.mul_add, Nat.two_mul]
    have atP := ih p (by simp [move,children])
    have atQ := ih q (by simp [move,children])
    constructor
    · have up := Nat.add_le_add atP.1 atQ.1
      omega
    · have down := Nat.add_le_add atP.2 atQ.2
      omega

/-- Soundness holds for every assignment satisfying the local test. The
error in normalized probability is at most one scale unit per move. -/
theorem rounded_error_on {G : Game S} {M H : ℕ} {u : ℕ → S → ℕ} {active : ℕ → S → Prop}
    (valid : LocallyRoundedOn G M H u active) (r : ℕ) (fit : r ≤ H) (s : S)
    (present : active r s) :
    u r s * 2^r ≤ M*value G r s + r*2^r ∧
    M*value G r s ≤ u r s * 2^r + r*2^r := by
  induction r generalizing s with
  | zero =>
    obtain ⟨_,a,b⟩ := valid.1 0 fit s present
    simp only [doubleUpdate] at a b
    simp only [pow_zero,Nat.mul_one,Nat.add_zero,value]
    omega
  | succ r ih =>
    have prev : r ≤ H := by omega
    obtain ⟨_,a,b⟩ := valid.1 (r+1) fit s present
    obtain ⟨up,down⟩ := update_error G M u r s
      (fun q mem => ih prev q (valid.2 r (by omega) s present q mem))
    have ua := Nat.mul_le_mul_right (2^r) a
    have ub := Nat.mul_le_mul_right (2^r) b
    rw [Nat.add_mul,one_mul,Nat.mul_assoc] at ua
    rw [Nat.add_mul,one_mul,Nat.mul_assoc] at ub
    rw [Nat.pow_succ',Nat.add_mul,one_mul]
    have one : 2^r ≤ 2 * 2^r := by rw [Nat.two_mul]; omega
    have assoc : r * (2 * 2^r) = 2 * (r * 2^r) := by ring
    have perm : u (r+1) s * (2 * 2^r) = 2 * (u (r+1) s * 2^r) := by ring
    rw [assoc,perm]
    omega

theorem rounded_error {G : Game S} {M H : ℕ} {u : ℕ → S → ℕ}
    (valid : LocallyRounded G M H u) (r : ℕ) (fit : r ≤ H) (s : S) :
    u r s * 2^r ≤ M*value G r s + r*2^r ∧
    M*value G r s ≤ u r s * 2^r + r*2^r :=
  rounded_error_on (active := fun _ _ => True)
    ⟨fun j hj q _ => valid j hj q, fun _ _ _ _ _ _ => trivial⟩ r fit s trivial

private theorem quotient_window (a d : ℕ) (pos : 0 < d) :
    (a/d)*d ≤ a ∧ a < (a/d+1)*d :=
  ⟨Nat.div_mul_le_self _ _, (Nat.div_lt_iff_lt_mul pos).mp (Nat.lt_succ_self _)⟩

/-- Dividing the two child scores first can change the doubled parent
label by at most one integer. -/
private theorem average_quotients (a b d : ℕ) (pos : 0 < d) :
    let x := a/d
    let y := b/d
    let z := (a+b)/(2*d)
    2*z ≤ x+y+1 ∧ x+y ≤ 2*z+1 := by
  dsimp only
  obtain ⟨a₀,a₁⟩ := quotient_window a d pos
  obtain ⟨b₀,b₁⟩ := quotient_window b d pos
  obtain ⟨z₀,z₁⟩ := quotient_window (a+b) (2*d) (by omega)
  have low : (a/d+b/d)*d ≤ a+b := by rw [Nat.add_mul]; omega
  have high : a+b < (a/d+b/d+2)*d := by
    rw [Nat.add_mul, Nat.add_mul (a/d) (b/d), Nat.two_mul]
    rw [Nat.add_mul,one_mul] at a₁ b₁
    omega
  have left : ((a+b)/(2*d)*2)*d < (a/d+b/d+2)*d := by
    rw [Nat.mul_assoc]
    exact z₀.trans_lt high
  have right : (a/d+b/d)*d < (((a+b)/(2*d)+1)*2)*d := by
    rw [Nat.mul_assoc]
    exact low.trans_lt z₁
  have l := Nat.lt_of_mul_lt_mul_right left
  have r := Nat.lt_of_mul_lt_mul_right right
  omega

theorem floorValue_valid (G : Game S) (M H : ℕ) :
    LocallyRounded G M H (floorValue G M) := by
  intro r fit s
  have powPos (j : ℕ) : 0 < 2^j := Nat.pow_pos (by decide)
  have bounded : floorValue G M r s ≤ M := by
    unfold floorValue
    exact (Nat.div_le_div_right (Nat.mul_le_mul_left M (value_le_power G r s))).trans_eq
      (Nat.mul_div_cancel M (powPos r))
  unfold LabelValid
  refine ⟨bounded,?_⟩
  cases r with
  | zero => simp [floorValue,value,doubleUpdate]
  | succ r =>
    cases move : G.move (r+1) s with
    | stop b =>
      cases b <;> simp [floorValue,value,doubleUpdate,move]
    | pick p q =>
      simp only [floorValue,value,doubleUpdate,move,Nat.pow_succ']
      rcases le_total (value G r p) (value G r q) with le | ge
      · rw [max_eq_right le, max_eq_right (Nat.div_le_div_right (Nat.mul_le_mul_left M le))]
        rw [show M*(2*value G r q) = (M*value G r q)*2 by ring, Nat.mul_comm 2 (2^r)]
        rw [Nat.mul_div_mul_right _ _ (by decide : 0 < 2)]
        omega
      · rw [max_eq_left ge, max_eq_left (Nat.div_le_div_right (Nat.mul_le_mul_left M ge))]
        rw [show M*(2*value G r p) = (M*value G r p)*2 by ring, Nat.mul_comm 2 (2^r)]
        rw [Nat.mul_div_mul_right _ _ (by decide : 0 < 2)]
        omega
    | toss p q =>
      simp only [floorValue,value,doubleUpdate,move,Nat.pow_succ',Nat.mul_add]
      exact average_quotients _ _ _ (powPos r)

/-- At scale 12(H+1), any locally valid labels distinguish optimum
acceptance at least 2/3 from optimum acceptance at most 1/3. -/
theorem rounded_majority_gap_on (G : Game S) {H : ℕ} (s : S) (u : ℕ → S → ℕ)
    {active : ℕ → S → Prop} (valid : LocallyRoundedOn G (12*(H+1)) H u active)
    (present : active H s) :
    (2*2^H ≤ 3*value G H s → 12*(H+1) < 2*u H s) ∧
    (3*value G H s ≤ 2^H → 2*u H s < 12*(H+1)) := by
  obtain ⟨a,b⟩ := rounded_error_on valid H le_rfl s present
  let D : ℕ := 2^H
  have pos : 0 < D := Nat.pow_pos (by decide)
  change u H s * D ≤ 12*(H+1)*value G H s + H*D at a
  change 12*(H+1)*value G H s ≤ u H s * D + H*D at b
  constructor
  · intro good
    change 2*D ≤ 3*value G H s at good
    have scaled := Nat.mul_le_mul_left (4*(H+1)) good
    by_contra! bad
    have threshold := Nat.mul_le_mul_right D bad
    nlinarith
  · intro bad
    change 3*value G H s ≤ D at bad
    have scaled := Nat.mul_le_mul_left (4*(H+1)) bad
    by_contra! good
    have threshold := Nat.mul_le_mul_right D good
    nlinarith

theorem rounded_majority_gap (G : Game S) {H : ℕ} (s : S) (u : ℕ → S → ℕ)
    (valid : LocallyRounded G (12*(H+1)) H u) :
    (2*2^H ≤ 3*value G H s → 12*(H+1) < 2*u H s) ∧
    (3*value G H s ≤ 2^H → 2*u H s < 12*(H+1)) :=
  rounded_majority_gap_on G s u (active := fun _ _ => True)
    ⟨fun j hj q _ => valid j hj q, fun _ _ _ _ _ _ => trivial⟩ trivial

/-- Each label requires only the binary width of a linear function in the horizon. -/
theorem label_bits {G : Game S} {M H : ℕ} {u : ℕ → S → ℕ}
    (valid : LocallyRounded G M H u) (r : ℕ) (fit : r ≤ H) (s : S) :
    (u r s).size ≤ M.size :=
  Nat.size_le.mpr ((valid r fit s).1.trans_lt (Nat.size_le.mp le_rfl))

end PvsNP.PublicGame

open PvsNP.PublicGame

theorem solution {S : Type} (G : Game S) (H : ℕ) (s : S) :
    let M := 12*(H+1)
    LocallyRounded G M H (floorValue G M) ∧
    ∀ (u : ℕ → S → ℕ) (active : ℕ → S → Prop),
      LocallyRoundedOn G M H u active → active H s →
      (2*2^H ≤ 3*value G H s → M < 2*u H s) ∧
      (3*value G H s ≤ 2^H → 2*u H s < M) := by
  refine ⟨floorValue_valid G _ H, ?_⟩
  intro u active valid present
  exact rounded_majority_gap_on G s u valid present
