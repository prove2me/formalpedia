-- Prove2me | solution 1 for TopDownParity1043.Main.parity_finite_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T16:42:17.060855+00:00
-- url     : https://prove2.me/submissions/d65efe7d-c812-4aa1-8ac0-e66b0f9495fe

import Mathlib
import Theorems.Thm_TopDownParity1043_Main_limit_protocol_obstruction
import Theorems.Thm_TopDownParity1043_Main_parity_initial_invariant
set_option autoImplicit false
open TopDownParity1043.Main
private theorem deficit_count_iff {V : Type} [Fintype V] [DecidableEq V]
    (t : ℕ) (X : Finset (V → Bool)) (hX : X.Nonempty) (k : ℝ) :
    setDeficit t X ≤ k ↔ (2 : ℝ) ^ ((t : ℝ)-k) ≤ X.card := by
  have hxpos : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  unfold setDeficit
  rw [← Real.le_logb_iff_rpow_le (by norm_num) hxpos]
  constructor <;> intro h <;> linarith

private theorem message_class {V : Type} [Fintype V] [DecidableEq V]
    (X : Finset (V → Bool)) (k : ℝ) (hX : SetDeficitLE X k)
    (m b : ℕ) (hb : b ≤ 2^m) (msg : (V → Bool) → Fin b) :
    ∃ j : Fin b, SetDeficitLE (X.filter fun x => msg x = j) (k+m) := by
  classical
  obtain ⟨x,hx⟩ := hX.1
  have ht : (Finset.univ : Finset (Fin b)).Nonempty := ⟨msg x,Finset.mem_univ _⟩
  have hcount := (deficit_count_iff (Fintype.card V) X hX.1 k).mp hX.2
  have hm : (b : ℝ) ≤ (2 : ℝ)^m := by exact_mod_cast hb
  have hnum : (Finset.univ : Finset (Fin b)).card •
      ((2 : ℝ)^((Fintype.card V : ℝ)-(k+m))) ≤ (X.card : ℝ) := by
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc
      _ ≤ (2 : ℝ)^m * 2^((Fintype.card V : ℝ)-(k+m)) :=
        mul_le_mul_of_nonneg_right hm (by positivity)
      _ = (2 : ℝ)^((Fintype.card V : ℝ)-k) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
        congr 1
        ring
      _ ≤ _ := hcount
  obtain ⟨j,hj,hcard⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := X) (t := (Finset.univ : Finset (Fin b))) (f := msg)
    (fun x hx => Finset.mem_univ _) ht hnum
  have hpos : 0 < (X.filter fun x => msg x = j).card := by
    have hh : (0 : ℝ) < (X.filter fun x => msg x = j).card :=
      (show (0 : ℝ) < (2 : ℝ)^((Fintype.card V : ℝ)-(k+m)) by positivity).trans_le hcard
    exact_mod_cast hh
  refine ⟨j,⟨Finset.card_pos.mp hpos, ?_⟩⟩
  exact (deficit_count_iff (Fintype.card V) _ (Finset.card_pos.mp hpos) (k+m)).mpr hcard

private theorem limit_mono_k {V : Type} [Fintype V] [DecidableEq V]
    (p : Bias) (k l : ℝ) (hkl : k ≤ l) (Y : Finset (V → Bool)) (x : V → Bool)
    (h : IsPKLimit p k Y x) : IsPKLimit p l Y x := by
  classical
  apply h.trans
  unfold setProb
  apply Finset.sum_le_sum
  intro P hP
  by_cases hg : (2 : ℝ)^((P.card : ℝ)-k) ≤ (fibre Y x P).card
  · have hh : (2 : ℝ)^((P.card : ℝ)-l) ≤ (fibre Y x P).card := by
      apply le_trans _ hg
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    simp [hg,hh]
  · simp only [if_neg hg]
    split_ifs
    · unfold setWeight
      positivity [p.property.1,p.property.2]
    · exact le_rfl

theorem solution (n d m : ℕ) (hn : 0 < n) (hd : 1 ≤ d)
    (p : Bias) (hp : 0 < (p : ℝ)) (hnp : 2 ≤ (n : ℝ)*(p : ℝ))
    (hb : (32768*(196 : ℝ)^(d-1)*((m : ℝ)+1))^(d-1)*(p : ℝ) ≤ 1/2) :
    ¬HasKWProtocol (parity n) d m := by
  classical
  let X := Finset.univ.filter (fun x : Fin n → Bool => parity n x = false)
  let Y := Finset.univ.filter (fun x : Fin n → Bool => parity n x = true)
  obtain ⟨hX,hY,hL,hR⟩ := parity_initial_invariant n hn p hnp
  change SetDeficitLE X 1 at hX
  change SetDeficitLE Y 1 at hY
  change LeftLimit p 1 X Y at hL
  change RightLimit p 1 X Y at hR
  have hk : 1 ≤ (m : ℝ)+1 := le_add_of_nonneg_left (Nat.cast_nonneg m)
  have hm : (m : ℝ) ≤ (m : ℝ)+1 := by linarith
  have hX' : SetDeficitLE X ((m : ℝ)+1) := ⟨hX.1,hX.2.trans hk⟩
  have hY' : SetDeficitLE Y ((m : ℝ)+1) := ⟨hY.1,hY.2.trans hk⟩
  rintro ⟨P,hrounds,hcost,hsolves⟩
  have hsolve : SolvesKW P X Y := by
    intro x hx y hy
    exact hsolves x (Finset.mem_filter.mp hx).2 y (Finset.mem_filter.mp hy).2
  cases P with
  | leaf o =>
    apply limit_protocol_obstruction (Fin n) (d-1) m X Y ((m : ℝ)+1) hk hm hX' hY' p hp hb
      (Or.inl (fun x hx => limit_mono_k p 1 ((m : ℝ)+1) hk Y x (hL x hx)))
    exact ⟨.leaf o, by simp [Protocol.rounds],hcost,hsolve⟩
  | alice b msg next =>
    obtain ⟨j,hD⟩ := message_class X 1 hX m b hcost.1 msg
    let X' := X.filter (fun x => msg x = j)
    have hD' : SetDeficitLE X' ((m : ℝ)+1) := by
      simpa only [add_comm] using hD
    have hlim : LeftLimit p ((m : ℝ)+1) X' Y := by
      intro x hx
      exact limit_mono_k p 1 ((m : ℝ)+1) hk Y x (hL x (Finset.mem_filter.mp hx).1)
    apply limit_protocol_obstruction (Fin n) (d-1) m X' Y ((m : ℝ)+1) hk hm hD' hY' p hp hb (Or.inl hlim)
    refine ⟨next j,?_,hcost.2 j,?_⟩
    · have hh := Finset.le_sup (f := fun j : Fin b => (next j).rounds) (Finset.mem_univ j)
      change 1 + Finset.univ.sup (fun j : Fin b => (next j).rounds) ≤ d at hrounds
      omega
    · intro x hx y hy
      obtain ⟨hxX,hxj⟩ := Finset.mem_filter.mp hx
      simpa only [Protocol.run,hxj] using hsolve x hxX y hy
  | bob b msg next =>
    obtain ⟨j,hD⟩ := message_class Y 1 hY m b hcost.1 msg
    let Y' := Y.filter (fun y => msg y = j)
    have hD' : SetDeficitLE Y' ((m : ℝ)+1) := by
      simpa only [add_comm] using hD
    have hlim : RightLimit p ((m : ℝ)+1) X Y' := by
      intro y hy
      exact limit_mono_k p 1 ((m : ℝ)+1) hk X y (hR y (Finset.mem_filter.mp hy).1)
    apply limit_protocol_obstruction (Fin n) (d-1) m X Y' ((m : ℝ)+1) hk hm hX' hD' p hp hb (Or.inr hlim)
    refine ⟨next j,?_,hcost.2 j,?_⟩
    · have hh := Finset.le_sup (f := fun j : Fin b => (next j).rounds) (Finset.mem_univ j)
      change 1 + Finset.univ.sup (fun j : Fin b => (next j).rounds) ≤ d at hrounds
      omega
    · intro x hx y hy
      obtain ⟨hyY,hyj⟩ := Finset.mem_filter.mp hy
      simpa only [Protocol.run,hyj] using hsolve x hx y hyY


