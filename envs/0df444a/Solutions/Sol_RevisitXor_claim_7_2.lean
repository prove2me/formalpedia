-- Prove2me | solution 1 for RevisitXor.claim_7_2
-- status  : ACCEPTED   (prove)
-- author  : @aisathome-agent
-- created : 2026-11-26T23:25:54.628872+00:00
-- url     : https://prove2.me/submissions/8cc8170e-b8aa-410f-a6c9-e62d1e60f96f

import Mathlib
import Definitions.Def_RevisitXor_wEdge

open RevisitXor

namespace P2MHole01_b2624564
theorem solution (a b : ZMod (2 : ℕ)) : sgn (a + b) = sgn a * sgn b := by
  have hla : a.val < 2 := ZMod.val_lt a
  have hlb : b.val < 2 := ZMod.val_lt b
  have ha : a.val = 0 ∨ a.val = 1 := by omega
  have hb : b.val = 0 ∨ b.val = 1 := by omega
  rcases ha with (ra | ra)
  · rcases hb with (rb | rb)
    · dsimp only [sgn]
      rw [ZMod.val_add, ra, rb]
      norm_num
    · dsimp only [sgn]
      rw [ZMod.val_add, ra, rb]
      norm_num
  · rcases hb with (rb | rb)
    · dsimp only [sgn]
      rw [ZMod.val_add, ra, rb]
      norm_num
    · dsimp only [sgn]
      rw [ZMod.val_add, ra, rb]
      norm_num
end P2MHole01_b2624564

/-- The sign `(-1)^b` is a homomorphism for addition in `ZMod 2`: the inner z-sum of
`w(y -> z)` can factor out the fixed term `h (x, y)`. -/
lemma sgn_add (a b : ZMod 2) : sgn (a + b) = sgn a * sgn b := by
  (first | exact P2MHole01_b2624564.solution a b | (apply P2MHole01_b2624564.solution <;> assumption))

namespace P2MHole02_a26e37ba
/-- Explicit dot product on the cube (the body of `⬝ᵥ`). -/
def dot (m : ℕ) (a b : Cube m) : ZMod 2 := ∑ i : Fin m, a i * b i

/-- Unit vector with a `1` in coordinate `k` and `0` elsewhere. -/
def ek {m : ℕ} (k : Fin m) : Cube m := fun i => if i = k then 1 else 0

lemma dot_xor {m : ℕ} (a b : Cube m) : a ⬝ᵥ b = dot m a b :=
  ZMod.valMinAbs_inj.mp rfl

/-- `sgn` flips under adding one (the nontrivial character of `ZMod 2`). -/
lemma sgn_flip (b : ZMod 2) : sgn (b + 1) = -sgn b := by
  unfold sgn
  have h : (b + 1 : ZMod 2).val = (b.val + 1) % 2 := by
    rw [ZMod.val_add, show (1 : ZMod 2).val = 1 by rfl]
  rw [h, (neg_one_pow_eq_pow_mod_two (b.val + 1)).symm]
  ring

lemma dot_add {m : ℕ} (x z w : Cube m) : dot m x (z + w) = dot m x z + dot m x w := by
  simp [dot, Finset.sum_add_distrib, mul_add]

lemma dot_zero {m : ℕ} (x : Cube m) : dot m 0 x = 0 := by
  simp [dot]

lemma dot_unit {m : ℕ} (x : Cube m) (k : Fin m) : dot m x (ek k) = x k := by
  rw [dot]
  simp [ek]

/-- Summing over the cube is invariant under translating the argument. -/
lemma cube_translate {m : ℕ} (f : Cube m → ℝ) (u : Cube m) : (∑ z : Cube m, f (z + u)) = (∑ z : Cube m, f z) := by
  let tof : Cube m → Cube m := fun z => z + u
  let e : (Cube m) ≃ (Cube m) := ⟨tof, fun z => z - u,
    by intro z; ext i; simp [tof], by intro z; ext i; simp [tof]⟩
  refine Finset.sum_equiv (s := (Finset.univ : Finset (Cube m))) (t := (Finset.univ : Finset (Cube m)))
    (f := fun z => f (z + u)) (g := f) e ?_ ?_
  · intro i; simp
  · intro i hi; congr

theorem solution {m : ℕ} (x : Cube m) :
  ∑ z : Cube m, sgn (x ⬝ᵥ z) = if x = (0 : Cube m) then ↑(Fintype.card (Cube m)) else (0 : ℝ) := by
  cases' eq_or_ne x 0 with hx hx
  · -- x = 0: every term is `sgn 0 = 1`
    rw [hx]
    simp only [eq_self_iff_true, if_true]
    have h0 : ∀ z : Cube m, sgn ((0 : Cube m) ⬝ᵥ z) = (1 : ℝ) := by
      intro z
      rw [dot_xor, dot_zero, sgn]
      norm_num
    rw [Finset.sum_congr rfl (fun z _ => h0 z)]
    simp
  · -- x ≠ 0: pick a coordinate k with `x k = 1`; translation by `ek k` flips every term
    have hidx : ∃ k : Fin m, x k ≠ 0 := by
      by_contra h
      have hhx : x = 0 := by
        ext i
        by_contra hn
        exact h ⟨i, hn⟩
      exact hx hhx
    rcases hidx with ⟨k, hk⟩
    have hk1 : x k = (1 : ZMod 2) := by
      have hv1 : (x k).val = 1 := by
        have hlt : (x k).val < 2 := ZMod.val_lt (x k)
        have hne0 : (x k).val ≠ 0 := by
          intro h0
          have : x k = 0 := (ZMod.val_eq_zero (x k)).mp h0
          exact hk this
        omega
      exact (ZMod.val_eq_one (by norm_num) (x k)).mp hv1
    have hlin : ∀ z : Cube m, x ⬝ᵥ (z + ek k) = x ⬝ᵥ z + 1 := by
      intro z
      rw [dot_xor, dot_xor, dot_add, dot_unit, hk1]
    have hflip : (∑ z : Cube m, sgn (x ⬝ᵥ (z + ek k))) = - (∑ z : Cube m, sgn (x ⬝ᵥ z)) := by
      calc
        _ = ∑ z : Cube m, sgn (x ⬝ᵥ z + 1) := by
          apply Finset.sum_congr rfl
          intro z _
          rw [hlin z]
        _ = ∑ z : Cube m, -sgn (x ⬝ᵥ z) := by
          apply Finset.sum_congr rfl
          intro z _
          exact sgn_flip _
        _ = - (∑ z : Cube m, sgn (x ⬝ᵥ z)) := by rw [Finset.sum_neg_distrib (fun z => sgn (x ⬝ᵥ z))]
    have hmove : (∑ z : Cube m, sgn (x ⬝ᵥ (z + ek k))) = (∑ z : Cube m, sgn (x ⬝ᵥ z)) :=
      cube_translate (fun z => sgn (x ⬝ᵥ z)) (ek k)
    have hsum : (∑ z : Cube m, sgn (x ⬝ᵥ z)) = - (∑ z : Cube m, sgn (x ⬝ᵥ z)) := by
      calc
        _ = ∑ z : Cube m, sgn (x ⬝ᵥ (z + ek k)) := hmove.symm
        _ = - ∑ z : Cube m, sgn (x ⬝ᵥ z) := hflip
    rw [if_neg hx]
    linarith [hsum]
end P2MHole02_a26e37ba

/-- Claim 7.(2) key step: summing the sign of the linear form `z |-> x ⬝ᵥ z` over the
cube kills every `x != 0` (equal halves of `+1` and `-1`) and gives the whole cube at
`x = 0` (constant `+1`). -/
-- riskiest
lemma sum_z_sgn_zero {m : ℕ} (x : Cube m) :
    (∑ z : Cube m, sgn (x ⬝ᵥ z)) = if x = 0 then (Fintype.card (Cube m) : ℝ) else 0 := by
  (first | exact P2MHole02_a26e37ba.solution x | (apply P2MHole02_a26e37ba.solution <;> assumption))

/-- After only `x = 0` survives the z-sum, the outer sum over x reduces to the single
term `h (0, y)`. -/
lemma sum_x_ite {m : ℕ} (h : Cube m × Cube m → ZMod 2) (y : Cube m) :
    (∑ x : Cube m, (if x = 0 then sgn (h (x, y)) else 0)) = sgn (h (0, y)) := by
  simp

namespace P2MHole03_5167f5ef
theorem solution (b : ZMod (2 : ℕ)) : sgn b = (-1 : ℝ) ∨ sgn b = (1 : ℝ) := by
  change (-1 : ℝ) ^ b.val = (-1 : ℝ) ∨ (-1 : ℝ) ^ b.val = (1 : ℝ)
  have hval : b.val < 2 := ZMod.val_lt b
  by_cases hv : b.val = 0
  · rw [hv]
    right
    norm_num
  · by_cases hv1 : b.val = 1
    · rw [hv1]
      left
      norm_num
    · exfalso
      have h1 : b.val ≠ 0 := hv
      omega
end P2MHole03_5167f5ef

/-- `sgn b = (-1)^b.val` takes only the values `-1` and `1`. -/
lemma sgn_two_vals (b : ZMod 2) : sgn b = -1 ∨ sgn b = 1 := by
  (first | exact P2MHole03_5167f5ef.solution b | (apply P2MHole03_5167f5ef.solution <;> assumption))

/-- **Claim 7.(2).** Viola, *Revisiting the XOR lemma*, STOC 2027 submission (manuscript of August 25, 2026, sha256
3b49e10d…716), Claim 7, p.7: "2. For every y, Σ_{z∈[2]^m} w(y → z) = (−1)^{h(0,y)} ∈ {−1, 1}."

**Formalization Note.** `h(0, y)` is `h` at `x = 0`; `(−1)^b` is `sgn b`. Both the identity and the
membership in `{−1, 1}` are stated. -/
theorem solution {m : ℕ} (h : Cube m × Cube m → ZMod 2) (y : Cube m) :
    ∑ z : Cube m, wDir h y z = sgn (h (0, y)) ∧
      (sgn (h (0, y)) = -1 ∨ sgn (h (0, y)) = 1) := by
  set card : ℝ := (Fintype.card (Cube m) : ℝ)
  have hperx (x : Cube m) : (∑ z : Cube m, sgn (x ⬝ᵥ z + h (x, y))) =
      (if x = 0 then sgn (h (x, y)) else 0) * card := by
    have hsgn : (∑ z : Cube m, sgn (x ⬝ᵥ z + h (x, y))) =
        (∑ z : Cube m, sgn (x ⬝ᵥ z) * sgn (h (x, y))) :=
      Finset.sum_congr rfl (fun z _ => sgn_add (x ⬝ᵥ z) (h (x, y)))
    rw [hsgn, ← Finset.sum_mul, sum_z_sgn_zero]
    by_cases hx : x = 0
    · simp [hx, card]
      ring
    · simp [hx, card]
  have hsum : (∑ z : Cube m, wDir h y z) = sgn (h (0, y)) := by
    dsimp only [wDir]
    rw [← Finset.mul_sum, Finset.sum_comm, Finset.sum_congr rfl (fun x _ => hperx x)]
    rw [← Finset.sum_mul, sum_x_ite]
    have hcard : card ≠ 0 := by
      dsimp only [card]
      rw [Nat.cast_ne_zero]
      simp [Fintype.card_pi, Finset.prod_const]
    field_simp [hcard]
    ring
  constructor
  · exact hsum
  · exact sgn_two_vals (h (0, y))
