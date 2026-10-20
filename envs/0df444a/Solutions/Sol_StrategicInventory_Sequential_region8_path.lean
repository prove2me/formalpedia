-- Prove2me | solution 1 for StrategicInventory.Sequential.region8_path
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-19T21:17:16.786962+00:00
-- url     : https://prove2.me/submissions/2ef0e146-3e4f-43c5-a77b-f4594c316d59

import Mathlib
import Definitions.Def_StrategicInventory_Sequential_Game
import Definitions.Def_StrategicInventory_Sequential_IsSPE
import Definitions.Def_StrategicInventory_Sequential_Thresholds

set_option autoImplicit false
set_option linter.all false

namespace SI8

/-- stage-3 direct quantity -/
noncomputable def qsD (α s q : ℝ) : ℝ := max (α - q - s) 0 / 2
/-- buyer period-2 revenue -/
noncomputable def rev (α s q : ℝ) : ℝ := (α - q - qsD α s q) * q
/-- buyer period-2 objective (with the cheapest order) -/
noncomputable def bf (α s I w q : ℝ) : ℝ := rev α s q - w * max (q - I) 0

theorem rev_le1 (α s q : ℝ) (hq : 0 ≤ q) : rev α s q ≤ q * (α - q + s) / 2 := by
  unfold rev qsD
  rcases le_total 0 (α - q - s) with h | h
  · rw [max_eq_left h]; exact le_of_eq (by ring)
  · rw [max_eq_right h]; linarith [mul_nonneg hq (neg_nonneg.2 h)]

theorem rev_le2 (α s q : ℝ) (hq : 0 ≤ q) : rev α s q ≤ q * (α - q) := by
  unfold rev qsD
  rcases le_total 0 (α - q - s) with h | h
  · rw [max_eq_left h]; linarith [mul_nonneg hq h]
  · rw [max_eq_right h]; exact le_of_eq (by ring)

theorem rev_eq1 (α s q : ℝ) (h : q ≤ α - s) : rev α s q = q * (α - q + s) / 2 := by
  unfold rev qsD; rw [max_eq_left (by linarith)]; ring

theorem rev_eq2 (α s q : ℝ) (h : α - s ≤ q) : rev α s q = q * (α - q) := by
  unfold rev qsD; rw [max_eq_right (by linarith)]; ring

theorem bf_le (α s I w q : ℝ) (hw : 0 ≤ w) :
    bf α s I w q ≤ rev α s q - w * (q - I) ∧ bf α s I w q ≤ rev α s q := by
  unfold bf
  exact ⟨by linarith [mul_le_mul_of_nonneg_left (le_max_left (q - I) 0) hw],
    by linarith [mul_nonneg hw (le_max_right (q - I) 0)]⟩

/-- case A: buyer buys on the upper piece -/
theorem caseA (α s I w : ℝ) (hα : 0 < α) (hs1 : α / 2 < s) (hs2 : s < α)
    (hI : 0 ≤ I) (hw : 0 ≤ w) (hwA : w ≤ 2 * s - α) (hvI : I ≤ (α - w) / 2)
    (q : ℝ) (hq : 0 ≤ q) :
    bf α s I w q ≤ bf α s I w ((α - w) / 2) - (q - (α - w) / 2) ^ 2 / 2 := by
  have h1 := (bf_le α s I w q hw).1
  have h2 := rev_le2 α s q hq
  have ev : bf α s I w ((α - w) / 2) = (α - w) / 2 * (α - (α - w) / 2) - w * ((α - w) / 2 - I) := by
    unfold bf; rw [rev_eq2 α s _ (by linarith), max_eq_left (by linarith)]
  linarith [sq_nonneg (q - (α - w) / 2)]

/-- case K: buyer buys up to the kink -/
theorem caseK (α s I w : ℝ) (hα : 0 < α) (hs1 : α / 2 < s) (hs2 : s < α)
    (hI : 0 ≤ I) (hw : 0 ≤ w) (hw1 : 2 * s - α ≤ w) (hw2 : w ≤ (3 * s - α) / 2)
    (hvI : I ≤ α - s) (q : ℝ) (hq : 0 ≤ q) :
    bf α s I w q ≤ bf α s I w (α - s) - (q - (α - s)) ^ 2 / 2 := by
  have h1 := (bf_le α s I w q hw).1
  have ev : bf α s I w (α - s) = (α - s) * (α - (α - s)) - w * (α - s - I) := by
    unfold bf; rw [rev_eq2 α s _ le_rfl, max_eq_left (by linarith)]
  rcases le_total q (α - s) with hc | hc
  · have h2 := rev_le1 α s q hq
    linarith [mul_nonneg (by linarith : (0:ℝ) ≤ (3 * s - α) / 2 - w) (by linarith : (0:ℝ) ≤ α - s - q)]
  · have h2 := rev_le2 α s q hq
    linarith [mul_nonneg (by linarith : (0:ℝ) ≤ w - (2 * s - α)) (by linarith : (0:ℝ) ≤ q - (α - s)),
      sq_nonneg (q - (α - s))]

/-- case F: buyer buys on the lower piece -/
theorem caseF (α s I w : ℝ) (hα : 0 < α) (hs1 : α / 2 < s) (hs2 : s < α)
    (hI : 0 ≤ I) (hw : 0 ≤ w) (hw1 : (3 * s - α) / 2 ≤ w) (hw2 : w ≤ (α + s) / 2)
    (hvI : I ≤ (α + s) / 2 - w) (q : ℝ) (hq : 0 ≤ q) :
    bf α s I w q ≤ bf α s I w ((α + s) / 2 - w) - (q - ((α + s) / 2 - w)) ^ 2 / 2 := by
  have h1 := (bf_le α s I w q hw).1
  have h2 := rev_le1 α s q hq
  have ev : bf α s I w ((α + s) / 2 - w) = ((α + s) / 2 - w) * (α - ((α + s) / 2 - w) + s) / 2 -
      w * ((α + s) / 2 - w - I) := by
    unfold bf; rw [rev_eq1 α s _ (by linarith), max_eq_left (by linarith)]
  linarith

/-- case I: buyer sells exactly its inventory -/
theorem caseI (α s I w : ℝ) (hα : 0 < α) (hs1 : α / 2 < s) (hs2 : s < α)
    (hI : 0 ≤ I) (hIa : I ≤ α / 2) (hw : 0 ≤ w)
    (hm1 : α - s ≤ I → α - 2 * I ≤ w) (hm2 : I < α - s → (α + s) / 2 - I ≤ w)
    (q : ℝ) (hq : 0 ≤ q) :
    bf α s I w q ≤ bf α s I w I - (q - I) ^ 2 / 2 := by
  have h1 := bf_le α s I w q hw
  rcases lt_or_ge I (α - s) with hc | hc
  · have hm := hm2 hc
    have ev : bf α s I w I = I * (α - I + s) / 2 := by
      unfold bf; rw [rev_eq1 α s _ hc.le, max_eq_right (by linarith)]; ring
    have h2 := rev_le1 α s q hq
    rcases le_total q I with hd | hd
    · linarith [mul_nonneg (by linarith : (0:ℝ) ≤ (α + s) / 2 - I) (by linarith : (0:ℝ) ≤ I - q)]
    · linarith [mul_nonneg (by linarith : (0:ℝ) ≤ w - ((α + s) / 2 - I)) (by linarith : (0:ℝ) ≤ q - I)]
  · have hm := hm1 hc
    have ev : bf α s I w I = I * (α - I) := by
      unfold bf; rw [rev_eq2 α s _ hc, max_eq_right (by linarith)]; ring
    have h2 := rev_le2 α s q hq
    rcases le_total q I with hd | hd
    · linarith [mul_nonneg (by linarith : (0:ℝ) ≤ α - 2 * I) (by linarith : (0:ℝ) ≤ I - q),
        sq_nonneg (q - I)]
    · linarith [mul_nonneg (by linarith : (0:ℝ) ≤ w - (α - 2 * I)) (by linarith : (0:ℝ) ≤ q - I),
        sq_nonneg (q - I)]

/-- case H: inventory beyond the monopoly quantity -/
theorem caseH (α s I w : ℝ) (hα : 0 < α) (hs1 : α / 2 < s) (hs2 : s < α)
    (hIa : α / 2 ≤ I) (hw : 0 ≤ w) (q : ℝ) (hq : 0 ≤ q) :
    bf α s I w q ≤ bf α s I w (α / 2) - (q - α / 2) ^ 2 / 2 := by
  have h1 := (bf_le α s I w q hw).2
  have h2 := rev_le2 α s q hq
  have ev : bf α s I w (α / 2) = α / 2 * (α - α / 2) := by
    unfold bf; rw [rev_eq2 α s _ (by linarith), max_eq_right (by linarith)]; ring
  linarith [sq_nonneg (q - α / 2)]

/-- the buyer's period-2 sales under SPE -/
noncomputable def q2s (α s I w : ℝ) : ℝ :=
  if α / 2 ≤ I then α / 2
  else if w ≤ 2 * s - α then max ((α - w) / 2) I
  else if w ≤ (3 * s - α) / 2 then max (α - s) I
  else if w ≤ (α + s) / 2 then max ((α + s) / 2 - w) I
  else I

theorem q2s_nonneg (α s I w : ℝ) (hα : 0 < α) (hI : 0 ≤ I) : 0 ≤ q2s α s I w := by
  unfold q2s
  split_ifs <;> first | linarith | exact le_trans hI (le_max_right _ _)

theorem bf_opt (α s I w : ℝ) (hα : 0 < α) (hs1 : α / 2 < s) (hs2 : s < α)
    (hI : 0 ≤ I) (hw : 0 ≤ w) (q : ℝ) (hq : 0 ≤ q) :
    bf α s I w q ≤ bf α s I w (q2s α s I w) - (q - q2s α s I w) ^ 2 / 2 := by
  unfold q2s
  split_ifs with c0 c1 c2 c3
  · exact caseH α s I w hα hs1 hs2 c0 hw q hq
  · rcases le_total I ((α - w) / 2) with hd | hd
    · rw [max_eq_left hd]; exact caseA α s I w hα hs1 hs2 hI hw c1 hd q hq
    · rw [max_eq_right hd]
      exact caseI α s I w hα hs1 hs2 hI (by linarith) hw (fun _ => by linarith)
        (fun _ => by linarith) q hq
  · rcases le_total I (α - s) with hd | hd
    · rw [max_eq_left hd]; exact caseK α s I w hα hs1 hs2 hI hw (by linarith) c2 hd q hq
    · rw [max_eq_right hd]
      exact caseI α s I w hα hs1 hs2 hI (by linarith) hw (fun _ => by linarith)
        (fun _ => by linarith) q hq
  · rcases le_total I ((α + s) / 2 - w) with hd | hd
    · rw [max_eq_left hd]; exact caseF α s I w hα hs1 hs2 hI hw (by linarith) c3 hd q hq
    · rw [max_eq_right hd]
      exact caseI α s I w hα hs1 hs2 hI (by linarith) hw (fun _ => by linarith)
        (fun _ => by linarith) q hq
  · exact caseI α s I w hα hs1 hs2 hI (by linarith) hw (fun _ => by linarith)
        (fun _ => by linarith) q hq

open StrategicInventory.Sequential in
theorem direct_pin (α h s : ℝ) (σ : Profile) (hσ : IsSPE α h s σ)
    (w1 Q1 q1 w2 Q2 q2 : ℝ) (hw1 : 0 ≤ w1) (hq1 : 0 ≤ q1) (hq1Q1 : q1 ≤ Q1)
    (hw2 : 0 ≤ w2) (hQ2 : 0 ≤ Q2) (hq2 : 0 ≤ q2) (hq2I : q2 ≤ (Q1 - q1) + Q2) :
    σ.direct w1 Q1 q1 w2 Q2 q2 = qsD α s q2 := by
  unfold qsD
  obtain ⟨hx0, hopt⟩ := hσ.1 w1 Q1 q1 w2 Q2 q2 hw1 hq1 hq1Q1 hw2 hQ2 hq2 hq2I
  set x := σ.direct w1 Q1 q1 w2 Q2 q2 with hxdef
  have key : ∀ qs : ℝ, 0 ≤ qs →
      (α - q2 - qs - s) * qs ≤ (α - q2 - x - s) * x := by
    intro qs hqs
    have := hopt qs hqs
    simp only [supplierPayoff, Profile.outcomeAtDirect] at this
    rw [← hxdef] at this
    linarith
  rcases le_or_gt 0 (α - q2 - s) with hc | hc
  · rw [max_eq_left hc]
    have h1 := key ((α - q2 - s) / 2) (by linarith)
    have hsq : (x - (α - q2 - s) / 2) ^ 2 ≤ 0 := by nlinarith
    have : (x - (α - q2 - s) / 2) ^ 2 = 0 := le_antisymm hsq (sq_nonneg _)
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith
  · rw [max_eq_right hc.le]
    have h1 := key 0 le_rfl
    rcases hx0.lt_or_eq with hxp | hxe
    · nlinarith
    · rw [← hxe]; norm_num

open StrategicInventory.Sequential in
/-- period-2 buyer pinning under SPE -/
theorem period2_pin (α h s : ℝ) (hα : 0 < α) (hs1 : α / 2 < s) (hs2 : s < α)
    (σ : Profile) (hσ : IsSPE α h s σ)
    (w1 Q1 q1 w2 : ℝ) (hw1 : 0 ≤ w1) (hq1 : 0 ≤ q1) (hq1Q1 : q1 ≤ Q1) (hw2 : 0 ≤ w2) :
    (σ.period2 w1 Q1 q1 w2).2 = q2s α s (Q1 - q1) w2 ∧
      w2 * (σ.period2 w1 Q1 q1 w2).1 = w2 * max (q2s α s (Q1 - q1) w2 - (Q1 - q1)) 0 := by
  obtain ⟨hQ0, hq0, hqI, hopt⟩ := hσ.2.1 w1 Q1 q1 w2 hw1 hq1 hq1Q1 hw2
  set Q2 := (σ.period2 w1 Q1 q1 w2).1 with hQ2
  set q2 := (σ.period2 w1 Q1 q1 w2).2 with hq2
  set I := Q1 - q1 with hIdef
  have hI : 0 ≤ I := by rw [hIdef]; linarith
  set v := q2s α s I w2 with hv
  have hv0 : 0 ≤ v := q2s_nonneg α s I w2 hα hI
  have hc := hopt (max (v - I) 0) v (le_max_right _ _) hv0 (by linarith [le_max_left (v - I) 0])
  have hd1 := direct_pin α h s σ hσ w1 Q1 q1 w2 (max (v - I) 0) v hw1 hq1 hq1Q1 hw2
    (le_max_right _ _) hv0 (by linarith [le_max_left (v - I) 0])
  have hd2 := direct_pin α h s σ hσ w1 Q1 q1 w2 Q2 q2 hw1 hq1 hq1Q1 hw2 hQ0 hq0 hqI
  simp only [buyerPayoff, Profile.outcomeAtOrder2, Profile.outcomeAtDirect] at hc
  rw [hd1, ← hQ2, ← hq2, hd2] at hc
  have hmx : w2 * max (q2 - I) 0 ≤ w2 * Q2 :=
    mul_le_mul_of_nonneg_left (max_le (by linarith) hQ0) hw2
  have hb := bf_opt α s I w2 hα hs1 hs2 hI hw2 q2 hq0
  rw [← hv] at hb
  simp only [bf, rev] at hb
  have hsq : (q2 - v) ^ 2 = 0 := by
    have := sq_nonneg (q2 - v); linarith
  have heq : q2 = v := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq; linarith
  refine ⟨heq, ?_⟩
  rw [heq] at hc hmx
  apply le_antisymm
  · linarith
  · exact hmx

/-- supplier's period-2 profit when the buyer best-responds -/
noncomputable def sval (α s I w : ℝ) : ℝ :=
  w * max (q2s α s I w - I) 0 +
    (α - q2s α s I w - qsD α s (q2s α s I w) - s) * qsD α s (q2s α s I w)

theorem sval_le (α s I w : ℝ) (hα : 0 < α) (hs1 : 3 * α / 4 ≤ s) (hs2 : s < α)
    (hI : 0 ≤ I) (hIa : I < α / 2) (hw : 0 ≤ w) :
    sval α s I w ≤ max ((3 * s - α) / 2 * (α - s - I)) ((α - 2 * I) ^ 2 / 8) := by
  unfold sval q2s
  rw [if_neg (not_le.2 hIa)]
  split_ifs with c1 c2 c3
  · rcases le_total I ((α - w) / 2) with hd | hd
    · rw [max_eq_left hd]; apply le_max_of_le_right
      rw [max_eq_left (by linarith : (0:ℝ) ≤ (α - w) / 2 - I)]
      unfold qsD; rw [max_eq_right (by linarith : α - (α - w) / 2 - s ≤ 0)]
      linarith [sq_nonneg (w - (α / 2 - I))]
    · rw [max_eq_right hd]; apply le_max_of_le_right
      rw [max_eq_right (by linarith : I - I ≤ 0)]
      unfold qsD; rw [max_eq_right (by linarith : α - I - s ≤ 0)]
      linarith [sq_nonneg (α - 2 * I)]
  · rcases le_total I (α - s) with hd | hd
    · rw [max_eq_left hd]; apply le_max_of_le_left
      rw [max_eq_left (by linarith : (0:ℝ) ≤ α - s - I)]
      unfold qsD; rw [max_eq_right (by linarith : α - (α - s) - s ≤ 0)]
      linarith [mul_nonneg (by linarith : (0:ℝ) ≤ (3 * s - α) / 2 - w) (by linarith : (0:ℝ) ≤ α - s - I)]
    · rw [max_eq_right hd]; apply le_max_of_le_right
      rw [max_eq_right (by linarith : I - I ≤ 0)]
      unfold qsD; rw [max_eq_right (by linarith : α - I - s ≤ 0)]
      linarith [sq_nonneg (α - 2 * I)]
  · rcases le_total I ((α + s) / 2 - w) with hd | hd
    · rw [max_eq_left hd]; apply le_max_of_le_left
      rw [max_eq_left (by linarith : (0:ℝ) ≤ (α + s) / 2 - w - I)]
      unfold qsD; rw [max_eq_left (by linarith : (0:ℝ) ≤ α - ((α + s) / 2 - w) - s)]
      linarith [mul_nonneg (by linarith : (0:ℝ) ≤ w - (3 * s - α) / 2)
        (by linarith : (0:ℝ) ≤ (3 * s - α) / 2 + I - α + s), sq_nonneg (w - (3 * s - α) / 2)]
    · rw [max_eq_right hd]
      rcases lt_or_ge I (α - s) with he | he
      · apply le_max_of_le_left
        rw [max_eq_right (by linarith : I - I ≤ 0)]
        unfold qsD; rw [max_eq_left (by linarith : (0:ℝ) ≤ α - I - s)]
        linarith [mul_nonneg (by linarith : (0:ℝ) ≤ α - s - I)
          (by linarith : (0:ℝ) ≤ (3 * s - α) / 2 - (α - s - I) / 4)]
      · apply le_max_of_le_right
        rw [max_eq_right (by linarith : I - I ≤ 0)]
        unfold qsD; rw [max_eq_right (by linarith : α - I - s ≤ 0)]
        linarith [sq_nonneg (α - 2 * I)]
  · rcases lt_or_ge I (α - s) with he | he
    · apply le_max_of_le_left
      rw [max_eq_right (by linarith : I - I ≤ 0)]
      unfold qsD; rw [max_eq_left (by linarith : (0:ℝ) ≤ α - I - s)]
      linarith [mul_nonneg (by linarith : (0:ℝ) ≤ α - s - I)
        (by linarith : (0:ℝ) ≤ (3 * s - α) / 2 - (α - s - I) / 4)]
    · apply le_max_of_le_right
      rw [max_eq_right (by linarith : I - I ≤ 0)]
      unfold qsD; rw [max_eq_right (by linarith : α - I - s ≤ 0)]
      linarith [sq_nonneg (α - 2 * I)]

theorem sval_lt (α s I w : ℝ) (hα : 0 < α) (hs1 : 3 * α / 4 ≤ s) (hs2 : s < α)
    (hI : 0 ≤ I) (hIa : I < α / 2) (hw : 0 ≤ w)
    (hA : w ≠ α / 2 - I) (hK : w ≠ (3 * s - α) / 2) :
    sval α s I w < max ((3 * s - α) / 2 * (α - s - I)) ((α - 2 * I) ^ 2 / 8) := by
  have hA' : 0 < (w - (α / 2 - I)) ^ 2 := by
    have := sub_ne_zero.2 hA; positivity
  unfold sval q2s
  rw [if_neg (not_le.2 hIa)]
  split_ifs with c1 c2 c3
  · rcases le_total I ((α - w) / 2) with hd | hd
    · rw [max_eq_left hd]; apply lt_max_of_lt_right
      rw [max_eq_left (by linarith : (0:ℝ) ≤ (α - w) / 2 - I)]
      unfold qsD; rw [max_eq_right (by linarith : α - (α - w) / 2 - s ≤ 0)]
      linarith
    · rw [max_eq_right hd]; apply lt_max_of_lt_right
      rw [max_eq_right (by linarith : I - I ≤ 0)]
      unfold qsD; rw [max_eq_right (by linarith : α - I - s ≤ 0)]
      linarith [pow_pos (by linarith : (0:ℝ) < α - 2 * I) 2]
  · have c2' : w < (3 * s - α) / 2 := lt_of_le_of_ne c2 hK
    rcases lt_or_ge I (α - s) with hd | hd
    · rw [max_eq_left hd.le]; apply lt_max_of_lt_left
      rw [max_eq_left (by linarith : (0:ℝ) ≤ α - s - I)]
      unfold qsD; rw [max_eq_right (by linarith : α - (α - s) - s ≤ 0)]
      linarith [mul_pos (by linarith : (0:ℝ) < (3 * s - α) / 2 - w) (by linarith : (0:ℝ) < α - s - I)]
    · rw [max_eq_right hd]; apply lt_max_of_lt_right
      rw [max_eq_right (by linarith : I - I ≤ 0)]
      unfold qsD; rw [max_eq_right (by linarith : α - I - s ≤ 0)]
      linarith [pow_pos (by linarith : (0:ℝ) < α - 2 * I) 2]
  · rcases le_total I ((α + s) / 2 - w) with hd | hd
    · rw [max_eq_left hd]; apply lt_max_of_lt_left
      rw [max_eq_left (by linarith : (0:ℝ) ≤ (α + s) / 2 - w - I)]
      unfold qsD; rw [max_eq_left (by linarith : (0:ℝ) ≤ α - ((α + s) / 2 - w) - s)]
      linarith [mul_pos (by linarith : (0:ℝ) < w - (3 * s - α) / 2)
        (by linarith : (0:ℝ) < (3 * s - α) / 2 + I - α + s), sq_nonneg (w - (3 * s - α) / 2)]
    · rw [max_eq_right hd]
      rcases lt_or_ge I (α - s) with he | he
      · apply lt_max_of_lt_left
        rw [max_eq_right (by linarith : I - I ≤ 0)]
        unfold qsD; rw [max_eq_left (by linarith : (0:ℝ) ≤ α - I - s)]
        linarith [mul_pos (by linarith : (0:ℝ) < α - s - I)
          (by linarith : (0:ℝ) < (3 * s - α) / 2 - (α - s - I) / 4)]
      · apply lt_max_of_lt_right
        rw [max_eq_right (by linarith : I - I ≤ 0)]
        unfold qsD; rw [max_eq_right (by linarith : α - I - s ≤ 0)]
        linarith [pow_pos (by linarith : (0:ℝ) < α - 2 * I) 2]
  · rcases lt_or_ge I (α - s) with he | he
    · apply lt_max_of_lt_left
      rw [max_eq_right (by linarith : I - I ≤ 0)]
      unfold qsD; rw [max_eq_left (by linarith : (0:ℝ) ≤ α - I - s)]
      linarith [mul_pos (by linarith : (0:ℝ) < α - s - I)
        (by linarith : (0:ℝ) < (3 * s - α) / 2 - (α - s - I) / 4)]
    · apply lt_max_of_lt_right
      rw [max_eq_right (by linarith : I - I ≤ 0)]
      unfold qsD; rw [max_eq_right (by linarith : α - I - s ≤ 0)]
      linarith [pow_pos (by linarith : (0:ℝ) < α - 2 * I) 2]

theorem q2s_A (α s I : ℝ) (hα : 0 < α) (hs1 : 3 * α / 4 ≤ s) (hs2 : s < α)
    (hI : 0 ≤ I) (hIa : I < α / 2) :
    q2s α s I (α / 2 - I) = (α + 2 * I) / 4 := by
  unfold q2s
  rw [if_neg (not_le.2 hIa), if_pos (by linarith), max_eq_left (by linarith)]
  ring

theorem q2s_K (α s I : ℝ) (hα : 0 < α) (hs1 : 3 * α / 4 ≤ s) (hs2 : s < α)
    (hI : 0 ≤ I) (hIa : I ≤ α - s) :
    q2s α s I ((3 * s - α) / 2) = α - s := by
  unfold q2s
  rw [if_neg (by linarith), if_neg (by linarith), if_pos le_rfl, max_eq_left hIa]

theorem q2s_H (α s I w : ℝ) (hIa : α / 2 ≤ I) : q2s α s I w = α / 2 := by
  unfold q2s; rw [if_pos hIa]

theorem sval_A (α s I : ℝ) (hα : 0 < α) (hs1 : 3 * α / 4 ≤ s) (hs2 : s < α)
    (hI : 0 ≤ I) (hIa : I < α / 2) :
    sval α s I (α / 2 - I) = (α - 2 * I) ^ 2 / 8 := by
  unfold sval; rw [q2s_A α s I hα hs1 hs2 hI hIa]
  unfold qsD
  rw [max_eq_left (by linarith : (0:ℝ) ≤ (α + 2 * I) / 4 - I),
    max_eq_right (by linarith : α - (α + 2 * I) / 4 - s ≤ 0)]
  ring

theorem sval_K (α s I : ℝ) (hα : 0 < α) (hs1 : 3 * α / 4 ≤ s) (hs2 : s < α)
    (hI : 0 ≤ I) (hIa : I ≤ α - s) :
    sval α s I ((3 * s - α) / 2) = (3 * s - α) / 2 * (α - s - I) := by
  unfold sval; rw [q2s_K α s I hα hs1 hs2 hI hIa]
  unfold qsD
  rw [max_eq_left (by linarith : (0:ℝ) ≤ α - s - I),
    max_eq_right (by linarith : α - (α - s) - s ≤ 0)]
  ring

theorem sval_H (α s I w : ℝ) (hα : 0 < α) (hs1 : 3 * α / 4 ≤ s) (hIa : α / 2 ≤ I) :
    sval α s I w = 0 := by
  unfold sval; rw [q2s_H α s I w hIa]
  unfold qsD
  rw [max_eq_right (by linarith : α / 2 - I ≤ 0),
    max_eq_right (by linarith : α - α / 2 - s ≤ 0)]
  ring

theorem bval_A (α s I : ℝ) (hα : 0 < α) (hs1 : 3 * α / 4 ≤ s) (hs2 : s < α)
    (hI : 0 ≤ I) (hIa : I < α / 2) :
    bf α s I (α / 2 - I) (q2s α s I (α / 2 - I)) = (α ^ 2 + 12 * α * I - 12 * I ^ 2) / 16 := by
  rw [q2s_A α s I hα hs1 hs2 hI hIa]
  unfold bf
  rw [rev_eq2 α s _ (by linarith), max_eq_left (by linarith : (0:ℝ) ≤ (α + 2 * I) / 4 - I)]
  ring

theorem bval_K (α s I : ℝ) (hα : 0 < α) (hs1 : 3 * α / 4 ≤ s) (hs2 : s < α)
    (hI : 0 ≤ I) (hIa : I ≤ α - s) :
    bf α s I ((3 * s - α) / 2) (q2s α s I ((3 * s - α) / 2)) =
      (α - s) * s - (3 * s - α) / 2 * (α - s - I) := by
  rw [q2s_K α s I hα hs1 hs2 hI hIa]
  unfold bf
  rw [rev_eq2 α s _ le_rfl, max_eq_left (by linarith : (0:ℝ) ≤ α - s - I)]
  ring

theorem bval_H (α s I w : ℝ) (hα : 0 < α) (hs1 : 3 * α / 4 ≤ s) (hIa : α / 2 ≤ I) :
    bf α s I w (q2s α s I w) = α ^ 2 / 4 := by
  rw [q2s_H α s I w hIa]
  unfold bf
  rw [rev_eq2 α s _ (by linarith), max_eq_right (by linarith : α / 2 - I ≤ 0)]
  ring

noncomputable def VK0 (α s : ℝ) : ℝ := (α - s) * s - (3 * s - α) / 2 * (α - s)
noncomputable def VA (α I : ℝ) : ℝ := (α ^ 2 + 12 * α * I - 12 * I ^ 2) / 16

noncomputable def Vbar (α s J I : ℝ) : ℝ :=
  if α / 2 ≤ I then α ^ 2 / 4 else if I < J then VK0 α s + (3 * s - α) / 2 * I else VA α I

noncomputable def Mf (α s J I : ℝ) : ℝ :=
  if α / 2 ≤ I then 0 else if I < J then (3 * s - α) / 2 * (α - s - I) else (α - 2 * I) ^ 2 / 8

noncomputable def Fs (α s J w1 I : ℝ) : ℝ := w1 * (max (α - w1) 0 / 2 + I) + Mf α s J I


theorem Vbar_K (α s J I : ℝ) (h1 : I < α / 2) (h2 : I < J) :
    Vbar α s J I = VK0 α s + (3 * s - α) / 2 * I := by
  unfold Vbar; rw [if_neg (not_le.2 h1), if_pos h2]
theorem Vbar_A (α s J I : ℝ) (h1 : I ≤ α / 2) (h2 : J ≤ I) :
    Vbar α s J I = VA α I := by
  unfold Vbar VA
  rcases eq_or_lt_of_le h1 with h | h
  · rw [if_pos h.ge, h]; ring
  · rw [if_neg (not_le.2 h), if_neg (not_lt.2 h2)]
theorem Vbar_H (α s J I : ℝ) (h1 : α / 2 ≤ I) : Vbar α s J I = α ^ 2 / 4 := by
  unfold Vbar; rw [if_pos h1]
theorem Mf_K (α s J I : ℝ) (h1 : I < α / 2) (h2 : I < J) :
    Mf α s J I = (3 * s - α) / 2 * (α - s - I) := by
  unfold Mf; rw [if_neg (not_le.2 h1), if_pos h2]
theorem Mf_A (α s J I : ℝ) (h1 : I ≤ α / 2) (h2 : J ≤ I) :
    Mf α s J I = (α - 2 * I) ^ 2 / 8 := by
  unfold Mf
  rcases eq_or_lt_of_le h1 with h | h
  · rw [if_pos h.ge, h]; ring
  · rw [if_neg (not_le.2 h), if_neg (not_lt.2 h2)]
theorem Mf_H (α s J I : ℝ) (h1 : α / 2 ≤ I) : Mf α s J I = 0 := by
  unfold Mf; rw [if_pos h1]


theorem sval_K_hi (α s I : ℝ) (hα : 0 < α) (hs1 : 3 * α / 4 ≤ s) (hs2 : s < α)
    (hI : α - s ≤ I) (hIa : I < α / 2) : sval α s I ((3 * s - α) / 2) = 0 := by
  have hq : q2s α s I ((3 * s - α) / 2) = I := by
    unfold q2s
    rw [if_neg (not_le.2 hIa), if_neg (by linarith), if_pos le_rfl, max_eq_right hI]
  unfold sval; rw [hq]
  unfold qsD
  rw [max_eq_right (by linarith : I - I ≤ 0), max_eq_right (by linarith : α - I - s ≤ 0)]
  ring

open StrategicInventory.Sequential in
theorem order2_vals (α h s : ℝ) (hα : 0 < α) (hs1 : α / 2 < s) (hs2 : s < α)
    (σ : Profile) (hσ : IsSPE α h s σ)
    (w1 Q1 q1 w2 : ℝ) (hw1 : 0 ≤ w1) (hq1 : 0 ≤ q1) (hq1Q1 : q1 ≤ Q1) (hw2 : 0 ≤ w2) :
    supplierPayoff α s (σ.outcomeAtOrder2 w1 Q1 q1 w2) = w1 * Q1 + sval α s (Q1 - q1) w2 ∧
    buyerPayoff α h (σ.outcomeAtOrder2 w1 Q1 q1 w2) = (α - q1) * q1 - w1 * Q1 - h * (Q1 - q1) +
      bf α s (Q1 - q1) w2 (q2s α s (Q1 - q1) w2) := by
  obtain ⟨hq, hQ⟩ := period2_pin α h s hα hs1 hs2 σ hσ w1 Q1 q1 w2 hw1 hq1 hq1Q1 hw2
  obtain ⟨hQ0, hq0, hqI, -⟩ := hσ.2.1 w1 Q1 q1 w2 hw1 hq1 hq1Q1 hw2
  have hd := direct_pin α h s σ hσ w1 Q1 q1 w2 _ _ hw1 hq1 hq1Q1 hw2 hQ0 hq0 hqI
  simp only [Profile.outcomeAtOrder2, Profile.outcomeAtDirect, supplierPayoff, buyerPayoff,
    sval, bf, rev]
  rw [hd, hq]
  constructor
  · linear_combination hQ
  · linear_combination (-1 : ℝ) * hQ

theorem AK_sign (α s J I : ℝ) (hrel : J * (2 * α - 3 * s - J) = (5 * α ^ 2 - 16 * α * s + 12 * s ^ 2) / 4) :
    (α - 2 * I) ^ 2 / 8 - (3 * s - α) / 2 * (α - s - I) = (I - J) * (I - (2 * α - 3 * s - J)) / 2 := by
  linear_combination (-1 / 2 : ℝ) * hrel

open StrategicInventory.Sequential in
theorem price2_vals (α h s J : ℝ) (hα : 0 < α) (hs1 : 3 * α / 4 ≤ s) (hs2' : s < α)
    (hJs : J < α - s) (hx : 0 ≤ 2 * J - 2 * α + 3 * s)
    (hrel : J * (2 * α - 3 * s - J) = (5 * α ^ 2 - 16 * α * s + 12 * s ^ 2) / 4)
    (hVA0 : 0 ≤ J → VK0 α s + (3 * s - α) / 2 * J < VA α J)
    (σ : Profile) (hσ : IsSPE α h s σ)
    (w1 Q1 q1 : ℝ) (hw1 : 0 ≤ w1) (hq1 : 0 ≤ q1) (hq1Q1 : q1 ≤ Q1) :
    supplierPayoff α s (σ.outcomeAtPrice2 w1 Q1 q1) = w1 * Q1 + Mf α s J (Q1 - q1) ∧
    buyerPayoff α h (σ.outcomeAtPrice2 w1 Q1 q1) ≤
      (α - q1) * q1 - w1 * Q1 - h * (Q1 - q1) + Vbar α s J (Q1 - q1) ∧
    (Q1 - q1 ≠ J → buyerPayoff α h (σ.outcomeAtPrice2 w1 Q1 q1) =
      (α - q1) * q1 - w1 * Q1 - h * (Q1 - q1) + Vbar α s J (Q1 - q1)) ∧
    (Q1 - q1 = J → buyerPayoff α h (σ.outcomeAtPrice2 w1 Q1 q1) =
      (α - q1) * q1 - w1 * Q1 - h * (Q1 - q1) + Vbar α s J (Q1 - q1) →
      σ.price2 w1 Q1 q1 = α / 2 - J) ∧
    (J < Q1 - q1 → Q1 - q1 < α / 2 → σ.price2 w1 Q1 q1 = α / 2 - (Q1 - q1)) := by
  have hs1' : α / 2 < s := by linarith
  obtain ⟨hp0, hpopt⟩ := hσ.2.2.1 w1 Q1 q1 hw1 hq1 hq1Q1
  set p := σ.price2 w1 Q1 q1 with hpdef
  have hI : 0 ≤ Q1 - q1 := by linarith
  set I := Q1 - q1 with hIdef
  have hout : σ.outcomeAtPrice2 w1 Q1 q1 = σ.outcomeAtOrder2 w1 Q1 q1 p := rfl
  have hv := order2_vals α h s hα hs1' hs2' σ hσ w1 Q1 q1 p hw1 hq1 hq1Q1 hp0
  rw [hout, hv.1, hv.2]
  have hcmp : ∀ w2, 0 ≤ w2 → sval α s I w2 ≤ sval α s I p := by
    intro w2 hw2
    have := hpopt w2 hw2
    rw [hout, hv.1, (order2_vals α h s hα hs1' hs2' σ hσ w1 Q1 q1 w2 hw1 hq1 hq1Q1 hw2).1] at this
    linarith
  have hsg := AK_sign α s J I hrel
  rcases le_or_gt (α / 2) I with hH | hH
  · rw [Mf_H α s J I hH, Vbar_H α s J I hH, sval_H α s I p hα hs1 hH,
      bval_H α s I p hα hs1 hH]
    refine ⟨by ring, le_rfl, fun _ => rfl, fun hIJ => ?_, fun _ h2 => absurd h2 (not_lt.2 hH)⟩
    exfalso; linarith
  · have hle := sval_le α s I p hα hs1 hs2' hI hH hp0
    have hA := hcmp (α / 2 - I) (by linarith)
    rw [sval_A α s I hα hs1 hs2' hI hH] at hA
    rcases lt_trichotomy I J with hIJ | hIJ | hIJ
    · -- K regime
      have hK := hcmp ((3 * s - α) / 2) (by linarith)
      rw [sval_K α s I hα hs1 hs2' hI (by linarith)] at hK
      have hKA : (α - 2 * I) ^ 2 / 8 < (3 * s - α) / 2 * (α - s - I) := by
        have := mul_pos (sub_pos.2 hIJ) (by linarith : (0:ℝ) < I - (2 * α - 3 * s - J)); linarith
      have hpK : p = (3 * s - α) / 2 := by
        by_contra hne
        by_cases hpA : p = α / 2 - I
        · rw [hpA, sval_A α s I hα hs1 hs2' hI hH] at hK; linarith
        · have := sval_lt α s I p hα hs1 hs2' hI hH hp0 hpA hne
          rw [max_eq_left hKA.le] at this; linarith
      rw [hpK, sval_K α s I hα hs1 hs2' hI (by linarith), bval_K α s I hα hs1 hs2' hI (by linarith),
        Mf_K α s J I hH hIJ, Vbar_K α s J I hH hIJ]
      unfold VK0
      refine ⟨by ring, by linarith, fun _ => by ring, fun h => absurd h (ne_of_lt hIJ),
        fun h _ => absurd h (not_lt.2 hIJ.le)⟩
    · -- tie at J
      have hVA := hVA0 (by rw [← hIJ]; exact hI)
      have hKA : (α - 2 * I) ^ 2 / 8 = (3 * s - α) / 2 * (α - s - I) := by
        rw [hIJ] at hsg ⊢; linarith [hsg]
      have hpp : p = α / 2 - I ∨ p = (3 * s - α) / 2 := by
        by_contra hne; rw [not_or] at hne
        have := sval_lt α s I p hα hs1 hs2' hI hH hp0 hne.1 hne.2
        rw [← hKA, max_self] at this; linarith
      have hMf : Mf α s J I = (α - 2 * I) ^ 2 / 8 := Mf_A α s J I hH.le hIJ.ge
      have hVb : Vbar α s J I = VA α I := Vbar_A α s J I hH.le hIJ.ge
      rw [hMf, hVb]
      have hnl : ¬ (J < I) := by rw [hIJ]; exact lt_irrefl J
      rcases hpp with hp | hp
      · rw [hp, sval_A α s I hα hs1 hs2' hI hH, bval_A α s I hα hs1 hs2' hI hH]
        unfold VA
        refine ⟨by ring, le_rfl, fun h => absurd hIJ h, fun _ _ => by rw [hIJ],
          fun h _ => absurd h hnl⟩
      · rw [hp, sval_K α s I hα hs1 hs2' hI (by linarith), bval_K α s I hα hs1 hs2' hI (by linarith)]
        rw [← hIJ] at hVA
        unfold VK0 at hVA
        refine ⟨by linarith, by linarith, fun h => absurd hIJ h, fun _ h => ?_,
          fun h _ => absurd h hnl⟩
        exfalso; linarith
    · -- A regime
      have hKA : (3 * s - α) / 2 * (α - s - I) < (α - 2 * I) ^ 2 / 8 := by
        have := mul_pos (sub_pos.2 hIJ) (by linarith : (0:ℝ) < I - (2 * α - 3 * s - J)); linarith
      have hpA : p = α / 2 - I := by
        by_contra hne
        by_cases hpK : p = (3 * s - α) / 2
        · rcases le_or_gt I (α - s) with h1 | h1
          · rw [hpK, sval_K α s I hα hs1 hs2' hI h1] at hA; linarith
          · rw [hpK, sval_K_hi α s I hα hs1 hs2' h1.le hH] at hA
            have : 0 < (α - 2 * I) ^ 2 / 8 := by
              have : 0 < α - 2 * I := by linarith
              positivity
            linarith
        · have := sval_lt α s I p hα hs1 hs2' hI hH hp0 hne hpK
          rw [max_eq_right hKA.le] at this; linarith
      rw [hpA, sval_A α s I hα hs1 hs2' hI hH, bval_A α s I hα hs1 hs2' hI hH,
        Mf_A α s J I hH.le hIJ.le, Vbar_A α s J I hH.le hIJ.le]
      unfold VA
      refine ⟨by ring, le_rfl, fun _ => rfl, fun h => absurd h (ne_of_gt hIJ), fun _ _ => rfl⟩

theorem g_strong (α w1 q : ℝ) (hq : 0 ≤ q) :
    (α - q) * q - w1 * q ≤
      (α - max (α - w1) 0 / 2) * (max (α - w1) 0 / 2) - w1 * (max (α - w1) 0 / 2) -
        (q - max (α - w1) 0 / 2) ^ 2 := by
  rcases le_total 0 (α - w1) with h | h
  · rw [max_eq_left h]; nlinarith
  · rw [max_eq_right h]; nlinarith

theorem limit_arg (U g c VJ J ε0 : ℝ) (hε0 : 0 < ε0)
    (h : ∀ ε, 0 < ε → ε < ε0 → g + VJ - (c + 1) * ε ≤ U) (hc : 0 ≤ c) : g + VJ ≤ U := by
  by_contra hlt
  push Not at hlt
  set δ := g + VJ - U with hδ
  have hδ0 : 0 < δ := by linarith
  set ε := min (ε0 / 2) (δ / (2 * (c + 1))) with hεdef
  have hε0' : 0 < ε := lt_min (by linarith) (div_pos hδ0 (by linarith))
  have hε1 : ε < ε0 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hε2 : ε ≤ δ / (2 * (c + 1)) := min_le_right _ _
  have := h ε hε0' hε1
  have h3 : (c + 1) * ε ≤ δ / 2 := by
    calc (c + 1) * ε ≤ (c + 1) * (δ / (2 * (c + 1))) :=
          mul_le_mul_of_nonneg_left hε2 (by linarith)
      _ = δ / 2 := by field_simp
  linarith

open StrategicInventory.Sequential in
theorem buyer1 (α h s J : ℝ) (hα : 0 < α) (hs1 : 3 * α / 4 ≤ s) (hs2 : s < α) (hh : 0 ≤ h)
    (hJs : J < α - s) (hx : 0 ≤ 2 * J - 2 * α + 3 * s)
    (hrel : J * (2 * α - 3 * s - J) = (5 * α ^ 2 - 16 * α * s + 12 * s ^ 2) / 4)
    (hVA0 : 0 ≤ J → VK0 α s + (3 * s - α) / 2 * J < VA α J)
    (σ : Profile) (hσ : IsSPE α h s σ) (w1 : ℝ) (hw1 : 0 ≤ w1) :
    (σ.period1 w1).2 = max (α - w1) 0 / 2 ∧
    (∀ I', 0 ≤ I' → Vbar α s J I' - (w1 + h) * I' ≤
        Vbar α s J ((σ.period1 w1).1 - (σ.period1 w1).2) -
          (w1 + h) * ((σ.period1 w1).1 - (σ.period1 w1).2)) ∧
    buyerPayoff α h (σ.outcomeAtOrder1 w1) =
      (α - (σ.period1 w1).2) * (σ.period1 w1).2 - w1 * (σ.period1 w1).1 -
        h * ((σ.period1 w1).1 - (σ.period1 w1).2) +
        Vbar α s J ((σ.period1 w1).1 - (σ.period1 w1).2) := by
  obtain ⟨hq0, hqQ, hopt⟩ := hσ.2.2.2.1 w1 hw1
  set Q1 := (σ.period1 w1).1 with hQ1
  set q1 := (σ.period1 w1).2 with hq1
  set qs := max (α - w1) 0 / 2 with hqs
  have hqs0 : 0 ≤ qs := by rw [hqs]; have := le_max_right (α - w1) 0; linarith
  have hJa : J < α / 2 := by linarith
  have hout : σ.outcomeAtOrder1 w1 = σ.outcomeAtPrice2 w1 Q1 q1 := rfl
  set U := buyerPayoff α h (σ.outcomeAtOrder1 w1) with hU
  set gs := (α - qs) * qs - w1 * qs with hgs
  have hv := price2_vals α h s J hα hs1 hs2 hJs hx hrel hVA0 σ hσ w1 Q1 q1 hw1 hq0 hqQ
  rw [← hout] at hv
  -- alternatives with a pinned period-2 regime
  have halt : ∀ I', 0 ≤ I' → I' ≠ J → gs + (Vbar α s J I' - (w1 + h) * I') ≤ U := by
    intro I' hI' hne
    have hb := hopt (qs + I') qs hqs0 (by linarith)
    have hv' := price2_vals α h s J hα hs1 hs2 hJs hx hrel hVA0 σ hσ w1 (qs + I') qs hw1 hqs0
      (by linarith)
    have e : qs + I' - qs = I' := by ring
    rw [e] at hv'
    rw [(hv'.2.2.1 hne)] at hb
    rw [hgs]; linarith
  have hallJ : 0 ≤ J → gs + (Vbar α s J J - (w1 + h) * J) ≤ U := by
    intro hJ0
    rw [Vbar_A α s J J hJa.le le_rfl]
    apply limit_arg U gs (w1 + h) (VA α J - (w1 + h) * J) J (min 1 (α / 2 - J))
      (lt_min one_pos (by linarith)) _ (by linarith)
    intro ε hε hεlt
    have hε1 : ε < 1 := lt_of_lt_of_le hεlt (min_le_left _ _)
    have hε2 : ε < α / 2 - J := lt_of_lt_of_le hεlt (min_le_right _ _)
    have := halt (J + ε) (by linarith) (by linarith)
    rw [Vbar_A α s J (J + ε) (by linarith) (by linarith)] at this
    unfold VA at this ⊢
    linarith [mul_nonneg (by linarith : (0:ℝ) ≤ α - 2 * J) hε.le,
      mul_le_mul_of_nonneg_left hε1.le hε.le]
  have hall : ∀ I', 0 ≤ I' → gs + (Vbar α s J I' - (w1 + h) * I') ≤ U := by
    intro I' hI'
    by_cases hne : I' = J
    · rw [hne]; exact hallJ (by rw [← hne]; exact hI')
    · exact halt I' hI' hne
  have hI0 : 0 ≤ Q1 - q1 := by linarith
  have hgq := g_strong α w1 q1 hq0
  rw [← hqs] at hgq
  have hUle := hv.2.1
  have hself := hall (Q1 - q1) hI0
  have e : (α - q1) * q1 - w1 * Q1 - h * (Q1 - q1) =
      ((α - q1) * q1 - w1 * q1) - (w1 + h) * (Q1 - q1) := by ring
  rw [e] at hUle
  have hsq : (q1 - qs) ^ 2 = 0 := by
    have := sq_nonneg (q1 - qs); rw [← hgs] at hgq; linarith
  have hq1eq : q1 = qs := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq; linarith
  have hgeq : (α - q1) * q1 - w1 * q1 = gs := by rw [hgs, hq1eq]
  refine ⟨hq1eq, ?_, ?_⟩
  · intro I' hI'
    have := hall I' hI'
    linarith
  · rw [e]; linarith

open StrategicInventory.Sequential in
theorem s3_gt (α : ℝ) (hα : 0 < α) : 77 * α / 100 < s3 α := by
  unfold s3
  have h65 : Real.sqrt 65 < 41 / 5 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hin : (88 / 25 : ℝ) < Real.sqrt (37 - 3 * Real.sqrt 65) := by
    rw [Real.lt_sqrt (by norm_num)]; nlinarith
  nlinarith

open StrategicInventory.Sequential in
theorem xRoot_facts (α s : ℝ) (hα : 0 < α) (h1 : α / 3 ≤ s) (h2 : s ≤ α) :
    0 ≤ xRoot α s ∧ xRoot α s ^ 2 = 4 * α * s - α ^ 2 - 3 * s ^ 2 := by
  unfold xRoot
  refine ⟨Real.sqrt_nonneg _, Real.sq_sqrt ?_⟩
  nlinarith

theorem J_pos (α s x : ℝ) (hα : 0 < α) (hsl : 77 * α / 100 ≤ s) (hsu : s < 5 * α / 6)
    (hx0 : 0 ≤ x) (hx2 : x ^ 2 = 4 * α * s - α ^ 2 - 3 * s ^ 2) : 0 < 2 * α - 3 * s + x := by
  rcases le_or_gt (3 * s - 2 * α) 0 with h | h
  · nlinarith
  · nlinarith [sq_nonneg (x - (3 * s - 2 * α))]

theorem x_lt_s (α s x : ℝ) (hα : 0 < α) (hsl : 77 * α / 100 ≤ s) (hsu : s < 5 * α / 6)
    (hx0 : 0 ≤ x) (hx2 : x ^ 2 = 4 * α * s - α ^ 2 - 3 * s ^ 2) : x < s := by
  nlinarith [sq_nonneg (2 * s - α)]

/-- V_A(J) > V_K(J) -/
theorem VA_gt_VK (α s x : ℝ) (hα : 0 < α) (hsl : 77 * α / 100 ≤ s) (hsu : s < 5 * α / 6)
    (hx0 : 0 ≤ x) (hx2 : x ^ 2 = 4 * α * s - α ^ 2 - 3 * s ^ 2) :
    (α - s) * s - (3 * s - α) / 2 * (α - s - (2 * α - 3 * s + x) / 2) <
      (α ^ 2 + 12 * α * ((2 * α - 3 * s + x) / 2) - 12 * ((2 * α - 3 * s + x) / 2) ^ 2) / 16 := by
  have hJ := J_pos α s x hα hsl hsu hx0 hx2
  have hxs := x_lt_s α s x hα hsl hsu hx0 hx2
  nlinarith

theorem Jfacts (α s J : ℝ) (hα : 0 < α) (hsl : 77 * α / 100 ≤ s) (hsu : s < 5 * α / 6)
    (hx0 : 0 ≤ 2 * J - 2 * α + 3 * s)
    (hx2 : (2 * J - 2 * α + 3 * s) ^ 2 = 4 * α * s - α ^ 2 - 3 * s ^ 2) :
    0 < J ∧ J < α - s ∧ VK0 α s + (3 * s - α) / 2 * J < VA α J ∧
      VA α J - VK0 α s < (α / 2 + J) ^ 2 / 2 ∧
      (3 * s - α) / 2 * (α - s) < (α ^ 2 + 4 * J ^ 2) / 4 := by
  have e : (2 * α - 3 * s + (2 * J - 2 * α + 3 * s)) / 2 = J := by ring
  have h1 := J_pos α s _ hα hsl hsu hx0 hx2
  have h2 := x_lt_s α s _ hα hsl hsu hx0 hx2
  have h3 := VA_gt_VK α s _ hα hsl hsu hx0 hx2
  rw [e] at h3
  refine ⟨by linarith, by linarith, ?_, ?_, ?_⟩
  · unfold VK0 VA; nlinarith
  · unfold VK0 VA; nlinarith
  · nlinarith [sq_nonneg (3 * s - 2 * α)]

theorem phiA_gap (α c I : ℝ) :
    (VA α (α / 2 - 2 * c / 3) - c * (α / 2 - 2 * c / 3)) - (VA α I - c * I) =
      3 / 4 * (I - (α / 2 - 2 * c / 3)) ^ 2 := by unfold VA; ring

theorem phiA_diff (α c I J : ℝ) :
    (VA α J - c * J) - (VA α I - c * I) = 3 / 4 * (I - J) * (I + J - 2 * (α / 2 - 2 * c / 3)) := by
  unfold VA; ring
theorem corner_lo (α J w1 : ℝ) :
    w1 * ((α - w1) / 2 + J) + (α - 2 * J) ^ 2 / 8 =
      (α ^ 2 + 4 * J ^ 2) / 4 - (w1 - (α / 2 + J)) ^ 2 / 2 := by ring

/-- bundled facts for Region 8 -/
def Hyp8 (α s J h : ℝ) : Prop :=
  0 < α ∧ 77 * α / 100 ≤ s ∧ s < α ∧ 0 ≤ 2 * J - 2 * α + 3 * s ∧
  (2 * J - 2 * α + 3 * s) ^ 2 = 4 * α * s - α ^ 2 - 3 * s ^ 2 ∧
  0 ≤ h ∧ h < α / 4 ∧ (0 < J → 68 * J ^ 2 < (α - 4 * h) ^ 2)

theorem J_pos_s (α s J : ℝ) (hα : 0 < α) (hsl : 77 * α / 100 ≤ s)
    (hx0 : 0 ≤ 2 * J - 2 * α + 3 * s)
    (hx2 : (2 * J - 2 * α + 3 * s) ^ 2 = 4 * α * s - α ^ 2 - 3 * s ^ 2) (hJ : 0 < J) :
    s < 5 * α / 6 := by
  by_contra hc
  push Not at hc
  have h1 : 0 ≤ (6 * s - 5 * α) * (2 * s - α) := mul_nonneg (by linarith) (by linarith)
  nlinarith [mul_pos hJ (show (0:ℝ) < 3 * s - 2 * α + J by linarith)]

theorem J8facts (α s J h : ℝ) (H : Hyp8 α s J h) :
    J < α - s ∧ J < α / 2 ∧
    J * (2 * α - 3 * s - J) = (5 * α ^ 2 - 16 * α * s + 12 * s ^ 2) / 4 ∧
    (0 ≤ J → VK0 α s + (3 * s - α) / 2 * J < VA α J) := by
  obtain ⟨hα, hsl, hsu, hx0, hx2, hh, hh4, h68⟩ := H
  have hJs : J < α - s := by
    by_contra hc
    push Not at hc
    have h1 : s ≤ 2 * J - 2 * α + 3 * s := by linarith
    have h2 := mul_le_mul h1 h1 (by linarith) hx0
    nlinarith [mul_pos (by linarith : (0:ℝ) < 2 * s - α) (by linarith : (0:ℝ) < 2 * s - α)]
  refine ⟨hJs, by linarith, by linear_combination (-1 / 4 : ℝ) * hx2, fun hJ0 => ?_⟩
  rcases hJ0.lt_or_eq with hJ | hJ
  · exact (Jfacts α s J hα hsl (J_pos_s α s J hα hsl hx0 hx2 hJ) hx0 hx2).2.2.1
  · rw [← hJ]; unfold VK0 VA
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ α - s) (by linarith : (0:ℝ) ≤ s - 77 * α / 100),
      mul_pos hα hα]

theorem VAkey (α s J : ℝ)
    (hrel : J * (2 * α - 3 * s - J) = (5 * α ^ 2 - 16 * α * s + 12 * s ^ 2) / 4) :
    VA α J - VK0 α s = (2 * α ^ 2 - 8 * α * s + 7 * s ^ 2) / 4 + 3 * (3 * s - α) * J / 4 := by
  unfold VA VK0; linear_combination (3 / 4 : ℝ) * hrel

theorem Nbound (α s J : ℝ) (hα : 0 < α) (hsl : 77 * α / 100 ≤ s) (hsu : s < 5 * α / 6)
    (hx0 : 0 ≤ 2 * J - 2 * α + 3 * s)
    (hx2 : (2 * J - 2 * α + 3 * s) ^ 2 = 4 * α * s - α ^ 2 - 3 * s ^ 2) :
    (5 * α - 6 * s) / 4 ≤ J ∧
    37 / 50 * α * J < (9 * s - 6 * α) * J + (2 * α ^ 2 - 8 * α * s + 7 * s ^ 2) := by
  have hxa : α / 2 ≤ 2 * J - 2 * α + 3 * s := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 5 * α - 6 * s) (by linarith : (0:ℝ) ≤ 2 * s - α)]
  have hJlb : (5 * α - 6 * s) / 4 ≤ J := by linarith
  refine ⟨hJlb, ?_⟩
  have h1 : (9 * s - 6 * α - 37 / 50 * α) * ((5 * α - 6 * s) / 4) ≤
      (9 * s - 6 * α - 37 / 50 * α) * J :=
    mul_le_mul_of_nonneg_left hJlb (by linarith)
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ s - 77 * α / 100) (by linarith : (0:ℝ) ≤ 5 * α / 6 - s)]

/-- K-regime supplier bound -/
theorem Kbound (α s J h w1 : ℝ) (hα : 0 < α) (hsl : 77 * α / 100 ≤ s) (hsu : s < 5 * α / 6)
    (hx0 : 0 ≤ 2 * J - 2 * α + 3 * s)
    (hx2 : (2 * J - 2 * α + 3 * s) ^ 2 = 4 * α * s - α ^ 2 - 3 * s ^ 2)
    (hJ0 : 0 < J) (hh : 0 ≤ h) (hh4 : h < α / 4) (hw1 : 0 ≤ w1)
    (hc : VA α J - VK0 α s ≤ (w1 + h) * J) :
    w1 * (max (α - w1) 0 / 2 + 0) + (3 * s - α) / 2 * (α - s - 0) < (α ^ 2 + 4 * J ^ 2) / 4 := by
  have hrel : J * (2 * α - 3 * s - J) = (5 * α ^ 2 - 16 * α * s + 12 * s ^ 2) / 4 := by
    linear_combination (-1 / 4 : ℝ) * hx2
  obtain ⟨hJlb, hN⟩ := Nbound α s J hα hsl hsu hx0 hx2
  have hkey := VAkey α s J hrel
  have hr : 4 * (2 * J - 2 * α + 3 * s) ^ 2 - α ^ 2 - 8 * J ^ 2 ≤ 27 / 200 * α ^ 2 := by
    have h1 : ((5 * α - 6 * s) / 4) ^ 2 ≤ J ^ 2 := by
      have h0 : 0 ≤ (5 * α - 6 * s) / 4 := by linarith
      nlinarith
    rw [hx2]; nlinarith [sq_nonneg (s - 23 * α / 30)]
  have hJh : h * J ≤ α / 4 * J := mul_le_mul_of_nonneg_right hh4.le hJ0.le
  have hw : 37 / 100 * α < 2 * w1 - α := by
    by_contra hcon
    push Not at hcon
    have := mul_le_mul_of_nonneg_right hcon hJ0.le
    nlinarith
  rcases le_total α w1 with hw' | hw'
  · rw [max_eq_right (by linarith)]
    nlinarith [sq_nonneg (s - 2 * α / 3), sq_nonneg J, mul_pos hα hα]
  · rw [max_eq_left (by linarith)]
    nlinarith [mul_pos (by linarith : (0:ℝ) < 2 * w1 - α - 37 / 100 * α)
      (by linarith : (0:ℝ) < 2 * w1 - α + 37 / 100 * α)]

theorem S8_gt_corner (α h J : ℝ) (hh4 : h < α / 4)
    (h68 : 0 < J → 68 * J ^ 2 < (α - 4 * h) ^ 2) :
    (α ^ 2 + 4 * (max J 0) ^ 2) / 4 < (9 * α - 2 * h) ^ 2 / 306 + 2 * h ^ 2 / 9 := by
  rcases le_or_gt J 0 with hJ | hJ
  · rw [max_eq_right hJ]; nlinarith [pow_pos (by linarith : (0:ℝ) < α - 4 * h) 2]
  · rw [max_eq_left hJ.le]; nlinarith [h68 hJ]

theorem interior_eq (α h w1 : ℝ) :
    w1 * ((α - w1) / 2 + (α / 2 - 2 * (w1 + h) / 3)) + (α - 2 * (α / 2 - 2 * (w1 + h) / 3)) ^ 2 / 8 =
      (9 * α - 2 * h) ^ 2 / 306 + 2 * h ^ 2 / 9 - 17 / 18 * (w1 - (9 * α - 2 * h) / 17) ^ 2 := by
  ring

theorem Jc_facts (α J : ℝ) (hJa : J < α / 2) (hα : 0 < α) :
    J ≤ max J 0 ∧ 0 ≤ max J 0 ∧ max J 0 < α / 2 :=
  ⟨le_max_left _ _, le_max_right _ _, max_lt hJa (by linarith)⟩

/-- supplier bound, K regime -/
theorem CL8_K (α s J h w1 I : ℝ) (H : Hyp8 α s J h) (hw1 : 0 ≤ w1) (hI : 0 ≤ I) (hIJ : I < J)
    (hopt : ∀ I', 0 ≤ I' → Vbar α s J I' - (w1 + h) * I' ≤ Vbar α s J I - (w1 + h) * I) :
    Fs α s J w1 I < (9 * α - 2 * h) ^ 2 / 306 + 2 * h ^ 2 / 9 := by
  obtain ⟨hα, hsl, hsu, hx0, hx2, hh, hh4, h68⟩ := H
  have hJ0 : 0 < J := lt_of_le_of_lt hI hIJ
  have hs56 := J_pos_s α s J hα hsl hx0 hx2 hJ0
  obtain ⟨hJ0', hJs, hVA, hVc, hwK⟩ := Jfacts α s J hα hsl hs56 hx0 hx2
  have hIa : I < α / 2 := by linarith
  have o0 := hopt 0 le_rfl
  have oJ := hopt J hJ0.le
  rw [Vbar_K α s J I hIa hIJ, Vbar_K α s J 0 (by linarith) hJ0] at o0
  rw [Vbar_K α s J I hIa hIJ, Vbar_A α s J J (by linarith) le_rfl] at oJ
  have hI0 : I = 0 := by
    by_contra hne
    have hIp : 0 < I := lt_of_le_of_ne hI (Ne.symm hne)
    rcases le_or_gt (w1 + h) ((3 * s - α) / 2) with hc | hc
    · linarith [mul_nonneg (sub_nonneg.2 hc) (sub_nonneg.2 hIJ.le)]
    · linarith [mul_pos (sub_pos.2 hc) hIp]
  subst hI0
  have hc : VA α J - VK0 α s ≤ (w1 + h) * J := by linarith
  unfold Fs
  rw [Mf_K α s J 0 hIa hIJ]
  have hK := Kbound α s J h w1 hα hsl hs56 hx0 hx2 hJ0 hh hh4 hw1 hc
  have hS := S8_gt_corner α h J hh4 h68
  rw [max_eq_left hJ0.le] at hS
  linarith

/-- supplier bound, A regime -/
theorem CL8_A (α s J h w1 I : ℝ) (H : Hyp8 α s J h) (hw1 : 0 ≤ w1)
    (hJI : J ≤ I) (hI : 0 ≤ I) (hIa : I < α / 2)
    (hopt : ∀ I', 0 ≤ I' → Vbar α s J I' - (w1 + h) * I' ≤ Vbar α s J I - (w1 + h) * I) :
    Fs α s J w1 I ≤ (9 * α - 2 * h) ^ 2 / 306 + 2 * h ^ 2 / 9 ∧
      ((9 * α - 2 * h) ^ 2 / 306 + 2 * h ^ 2 / 9 ≤ Fs α s J w1 I → w1 = (9 * α - 2 * h) / 17) := by
  have H' := H
  obtain ⟨hα, hsl, hsu, hx0, hx2, hh, hh4, h68⟩ := H
  obtain ⟨hJs, hJa, hrel, hVA0⟩ := J8facts α s J h H'
  obtain ⟨hJJc, hJc0, hJca⟩ := Jc_facts α J hJa hα
  have hS := S8_gt_corner α h J hh4 h68
  have hopt' := hopt
  rw [Vbar_A α s J I hIa.le hJI] at hopt'
  have hIJc : max J 0 ≤ I := max_le hJI hI
  have hcase : I = max J 0 ∨ I = α / 2 - 2 * (w1 + h) / 3 := by
    rcases le_or_gt (max J 0) (α / 2 - 2 * (w1 + h) / 3) with hc | hc
    · right
      have oc := hopt' (α / 2 - 2 * (w1 + h) / 3) (by linarith)
      rw [Vbar_A α s J _ (by linarith) (by linarith)] at oc
      have hg := phiA_gap α (w1 + h) I
      have hsq : (I - (α / 2 - 2 * (w1 + h) / 3)) ^ 2 = 0 := by
        have := sq_nonneg (I - (α / 2 - 2 * (w1 + h) / 3)); linarith
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq; linarith
    · left
      by_contra hne
      have hgt : max J 0 < I := lt_of_le_of_ne hIJc (Ne.symm hne)
      have oJ := hopt' (max J 0) hJc0
      rw [Vbar_A α s J (max J 0) hJca.le hJJc] at oJ
      have hd := phiA_diff α (w1 + h) I (max J 0)
      have := mul_pos (mul_pos (by norm_num : (0:ℝ) < 3 / 4) (sub_pos.2 hgt))
        (by linarith : (0:ℝ) < I + max J 0 - 2 * (α / 2 - 2 * (w1 + h) / 3))
      linarith
  unfold Fs
  rcases hcase with hIc | hIc
  · -- corner
    have hlt : w1 * (max (α - w1) 0 / 2 + I) + Mf α s J I <
        (9 * α - 2 * h) ^ 2 / 306 + 2 * h ^ 2 / 9 := by
      rw [Mf_A α s J I hIa.le hJI, hIc]
      rcases le_total w1 α with hw | hw
      · rw [max_eq_left (show 0 ≤ α - w1 by linarith), corner_lo]
        nlinarith [sq_nonneg (w1 - (α / 2 + max J 0))]
      · rw [max_eq_right (show α - w1 ≤ 0 by linarith)]
        rcases le_or_gt J 0 with hJ | hJ
        · rw [max_eq_right hJ]
          nlinarith [pow_pos (by linarith : (0:ℝ) < α - 4 * h) 2]
        · rw [max_eq_left hJ.le]
          rw [max_eq_left hJ.le] at hS hIc
          have hs56 := J_pos_s α s J hα hsl hx0 hx2 hJ
          obtain ⟨-, -, -, hVc, -⟩ := Jfacts α s J hα hsl hs56 hx0 hx2
          have o0 := hopt 0 le_rfl
          rw [Vbar_K α s J 0 (by linarith) hJ, hIc, Vbar_A α s J J hJa.le le_rfl] at o0
          have : 0 ≤ h * J := mul_nonneg hh hJ.le
          nlinarith
    exact ⟨hlt.le, fun hge => absurd hge (not_le.2 hlt)⟩
  · rw [Mf_A α s J I hIa.le hJI, hIc]
    rw [hIc] at hIJc
    have hwa : w1 ≤ α := by linarith
    rw [max_eq_left (show 0 ≤ α - w1 by linarith), interior_eq]
    constructor
    · nlinarith [sq_nonneg (w1 - (9 * α - 2 * h) / 17)]
    · intro hge
      have h0 : (w1 - (9 * α - 2 * h) / 17) ^ 2 = 0 := by
        have := sq_nonneg (w1 - (9 * α - 2 * h) / 17); linarith
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0; linarith

/-- supplier bound, saturated regime -/
theorem CL8_H (α s J h w1 I : ℝ) (H : Hyp8 α s J h) (hw1 : 0 ≤ w1) (hIa : α / 2 ≤ I)
    (hopt : ∀ I', 0 ≤ I' → Vbar α s J I' - (w1 + h) * I' ≤ Vbar α s J I - (w1 + h) * I) :
    Fs α s J w1 I < (9 * α - 2 * h) ^ 2 / 306 + 2 * h ^ 2 / 9 := by
  have H' := H
  obtain ⟨hα, hsl, hsu, hx0, hx2, hh, hh4, h68⟩ := H
  obtain ⟨hJs, hJa, hrel, hVA0⟩ := J8facts α s J h H'
  obtain ⟨hJJc, hJc0, hJca⟩ := Jc_facts α J hJa hα
  have hopt' := hopt
  rw [Vbar_H α s J I hIa] at hopt'
  have hc0 : w1 + h = 0 := by
    by_contra hne
    have hcp : 0 < w1 + h := lt_of_le_of_ne (by linarith) (Ne.symm hne)
    rcases le_or_gt (max J 0) (α / 2 - 2 * (w1 + h) / 3) with hc | hc
    · have oc := hopt' (α / 2 - 2 * (w1 + h) / 3) (by linarith)
      rw [Vbar_A α s J _ (by linarith) (by linarith)] at oc
      unfold VA at oc
      linarith [mul_le_mul_of_nonneg_left hIa hcp.le, mul_pos hcp hcp]
    · have oJ := hopt' (max J 0) hJc0
      rw [Vbar_A α s J _ hJca.le hJJc] at oJ
      unfold VA at oJ
      linarith [mul_le_mul_of_nonneg_left hIa hcp.le,
        mul_pos (by linarith : (0:ℝ) < α / 2 - max J 0)
          (by linarith : (0:ℝ) < (w1 + h) - 3 / 4 * (α / 2 - max J 0))]
  have hw0 : w1 = 0 := by linarith
  unfold Fs
  rw [Mf_H α s J I hIa, hw0]
  nlinarith [pow_pos (by linarith : (0:ℝ) < 9 * α - 2 * h) 2, sq_nonneg h]

theorem CL8 (α s J h w1 I : ℝ) (H : Hyp8 α s J h) (hw1 : 0 ≤ w1) (hI : 0 ≤ I)
    (hopt : ∀ I', 0 ≤ I' → Vbar α s J I' - (w1 + h) * I' ≤ Vbar α s J I - (w1 + h) * I) :
    Fs α s J w1 I ≤ (9 * α - 2 * h) ^ 2 / 306 + 2 * h ^ 2 / 9 ∧
      ((9 * α - 2 * h) ^ 2 / 306 + 2 * h ^ 2 / 9 ≤ Fs α s J w1 I → w1 = (9 * α - 2 * h) / 17) := by
  rcases le_or_gt (α / 2) I with h1 | h1
  · have := CL8_H α s J h w1 I H hw1 h1 hopt
    exact ⟨this.le, fun hge => absurd hge (not_le.2 this)⟩
  · rcases lt_or_ge I J with h2 | h2
    · have := CL8_K α s J h w1 I H hw1 hI h2 hopt
      exact ⟨this.le, fun hge => absurd hge (not_le.2 this)⟩
    · exact CL8_A α s J h w1 I H hw1 h2 hI h1 hopt

theorem I8_facts (α s J h : ℝ) (H : Hyp8 α s J h) :
    J < 5 * (α - 4 * h) / 34 ∧ 0 < 5 * (α - 4 * h) / 34 ∧ 5 * (α - 4 * h) / 34 < α / 2 ∧
    max J 0 ≤ 5 * (α - 4 * h) / 34 := by
  obtain ⟨hα, hsl, hsu, hx0, hx2, hh, hh4, h68⟩ := H
  have hp : 0 < 5 * (α - 4 * h) / 34 := by linarith
  have hJ : J < 5 * (α - 4 * h) / 34 := by
    rcases le_or_gt J 0 with hJ | hJ
    · linarith
    · have := h68 hJ
      by_contra hc
      push Not at hc
      nlinarith [mul_le_mul hc hc hp.le (by linarith)]
  exact ⟨hJ, hp, by linarith, max_le hJ.le hp.le⟩

/-- at the equilibrium price the buyer's best inventory is uniquely I8 -/
theorem AMstar8 (α s J h I : ℝ) (H : Hyp8 α s J h) (hI : 0 ≤ I) (hne : I ≠ 5 * (α - 4 * h) / 34) :
    Vbar α s J I - ((9 * α - 2 * h) / 17 + h) * I <
      Vbar α s J (5 * (α - 4 * h) / 34) -
        ((9 * α - 2 * h) / 17 + h) * (5 * (α - 4 * h) / 34) := by
  have H' := H
  obtain ⟨hα, hsl, hsu, hx0, hx2, hh, hh4, h68⟩ := H
  obtain ⟨hJs, hJa, hrel, hVA0⟩ := J8facts α s J h H'
  obtain ⟨hJ8, h80, h8a, hJc8⟩ := I8_facts α s J h H'
  rw [Vbar_A α s J _ h8a.le hJ8.le]
  have hgap : ∀ I', (VA α (5 * (α - 4 * h) / 34) -
      ((9 * α - 2 * h) / 17 + h) * (5 * (α - 4 * h) / 34)) -
      (VA α I' - ((9 * α - 2 * h) / 17 + h) * I') =
        3 / 4 * (I' - 5 * (α - 4 * h) / 34) ^ 2 := by
    intro I'; unfold VA; ring
  rcases le_or_gt (α / 2) I with h1 | h1
  · rw [Vbar_H α s J I h1]
    have hg := hgap (α / 2)
    have e : VA α (α / 2) = α ^ 2 / 4 := by unfold VA; ring
    rw [e] at hg
    have := mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ (9 * α - 2 * h) / 17 + h)
    have := pow_pos (by linarith : (0:ℝ) < α / 2 - 5 * (α - 4 * h) / 34) 2
    linarith
  · rcases lt_or_ge I J with h2 | h2
    · have hJ0 : 0 < J := lt_of_le_of_lt hI h2
      have hs56 := J_pos_s α s J hα hsl hx0 hx2 hJ0
      have hVA := hVA0 hJ0.le
      rw [Vbar_K α s J I h1 h2]
      have hgJ := hgap J
      have hkey := VAkey α s J hrel
      have hN := (Nbound α s J hα hsl hs56 hx0 hx2).2
      have hcP : ((9 * α - 2 * h) / 17 + h) * J < VA α J - VK0 α s := by
        have : ((9 * α - 2 * h) / 17 + h) * J ≤ 3 * α / 4 * J :=
          mul_le_mul_of_nonneg_right (by linarith) hJ0.le
        nlinarith
      rcases le_or_gt ((9 * α - 2 * h) / 17 + h) ((3 * s - α) / 2) with h3 | h3
      · have := mul_le_mul_of_nonneg_left h2.le
          (by linarith : (0:ℝ) ≤ (3 * s - α) / 2 - ((9 * α - 2 * h) / 17 + h))
        nlinarith [sq_nonneg (J - 5 * (α - 4 * h) / 34)]
      · have := mul_nonneg (by linarith : (0:ℝ) ≤ ((9 * α - 2 * h) / 17 + h) - (3 * s - α) / 2) hI
        nlinarith [sq_nonneg (J - 5 * (α - 4 * h) / 34)]
    · rw [Vbar_A α s J I h1.le h2]
      have hg := hgap I
      have : 0 < (I - 5 * (α - 4 * h) / 34) ^ 2 := by
        have := sub_ne_zero.2 hne; positivity
      linarith

/-- the A-regime candidate -/
noncomputable def Ia (α J c : ℝ) : ℝ := if J ≤ α / 2 - 2 * c / 3 then α / 2 - 2 * c / 3 else J

/-- the buyer's selected inventory (existence) -/
noncomputable def Isel (α s J c : ℝ) : ℝ :=
  if Vbar α s J (Ia α (max J 0) c) - c * Ia α (max J 0) c ≤ Vbar α s J 0 then 0
  else Ia α (max J 0) c

theorem Ia_mem (α Jc c : ℝ) (hJc0 : 0 ≤ Jc) (hJca : Jc < α / 2) (hc : 0 ≤ c) :
    Jc ≤ Ia α Jc c ∧ Ia α Jc c ≤ α / 2 := by
  unfold Ia; split_ifs with h <;> constructor <;> linarith

theorem phiA_le_Ia (α J c I : ℝ) (hJI : J ≤ I) :
    VA α I - c * I ≤ VA α (Ia α J c) - c * Ia α J c := by
  unfold Ia
  split_ifs with h
  · have := phiA_gap α c I; have := sq_nonneg (I - (α / 2 - 2 * c / 3)); linarith
  · have hd := phiA_diff α c I J
    have := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 3 / 4) (sub_nonneg.2 hJI))
      (by linarith : (0:ℝ) ≤ I + J - 2 * (α / 2 - 2 * c / 3))
    linarith

theorem Isel_nonneg (α s J c : ℝ) (hα : 0 < α) (hJa : J < α / 2) (hc : 0 ≤ c) :
    0 ≤ Isel α s J c := by
  unfold Isel; split_ifs
  · exact le_rfl
  · linarith [(Ia_mem α (max J 0) c (le_max_right _ _) (max_lt hJa (by linarith)) hc).1,
      le_max_right J 0]

theorem AM (α s J c I : ℝ) (hα : 0 < α) (hJa : J < α / 2)
    (hVA : 0 < J → VK0 α s + (3 * s - α) / 2 * J < VA α J) (hc : 0 ≤ c) (hI : 0 ≤ I) :
    Vbar α s J I - c * I ≤ Vbar α s J (Isel α s J c) - c * Isel α s J c := by
  have hJc0 : 0 ≤ max J 0 := le_max_right _ _
  have hJJc : J ≤ max J 0 := le_max_left _ _
  have hJca : max J 0 < α / 2 := max_lt hJa (by linarith)
  obtain ⟨hIa1, hIa2⟩ := Ia_mem α (max J 0) c hJc0 hJca hc
  have hA : Vbar α s J (Ia α (max J 0) c) = VA α (Ia α (max J 0) c) :=
    Vbar_A α s J _ hIa2 (le_trans hJJc hIa1)
  have key : Vbar α s J I - c * I ≤ max (Vbar α s J 0 - c * 0)
      (Vbar α s J (Ia α (max J 0) c) - c * Ia α (max J 0) c) := by
    rcases le_or_gt (α / 2) I with h1 | h1
    · rw [Vbar_H α s J I h1]
      have hb := phiA_le_Ia α (max J 0) c (α / 2) hJca.le
      have e : VA α (α / 2) = α ^ 2 / 4 := by unfold VA; ring
      rw [e] at hb
      have := mul_le_mul_of_nonneg_left h1 hc
      apply le_max_of_le_right; rw [hA]; linarith
    · rcases lt_or_ge I J with h2 | h2
      · have hJ0 : 0 < J := lt_of_le_of_lt hI h2
        have hV0 : Vbar α s J 0 = VK0 α s + (3 * s - α) / 2 * 0 := Vbar_K α s J 0 (by linarith) hJ0
        have hJb := phiA_le_Ia α (max J 0) c J (max_le le_rfl hJ0.le)
        have hVAJ := hVA hJ0
        rw [Vbar_K α s J I h1 h2]
        rcases le_total c ((3 * s - α) / 2) with h3 | h3
        · apply le_max_of_le_right; rw [hA]
          have := mul_le_mul_of_nonneg_left h2.le (by linarith : (0:ℝ) ≤ (3 * s - α) / 2 - c)
          nlinarith
        · apply le_max_of_le_left; rw [hV0]
          have := mul_nonneg (by linarith : (0:ℝ) ≤ c - (3 * s - α) / 2) hI
          nlinarith
      · rw [Vbar_A α s J I h1.le h2]
        apply le_max_of_le_right; rw [hA]; exact phiA_le_Ia α (max J 0) c I (max_le h2 hI)
  unfold Isel
  split_ifs with h
  · rw [max_eq_left (by linarith)] at key; linarith
  · rw [max_eq_right (by linarith)] at key; exact key

theorem Isel_star (α s J h : ℝ) (H : Hyp8 α s J h) :
    Isel α s J ((9 * α - 2 * h) / 17 + h) = 5 * (α - 4 * h) / 34 := by
  have H' := H
  obtain ⟨hJ8, h80, h8a, hJc8⟩ := I8_facts α s J h H'
  have e : α / 2 - 2 * ((9 * α - 2 * h) / 17 + h) / 3 = 5 * (α - 4 * h) / 34 := by ring
  have hIa : Ia α (max J 0) ((9 * α - 2 * h) / 17 + h) = 5 * (α - 4 * h) / 34 := by
    unfold Ia; rw [e, if_pos hJc8]
  have hlt := AMstar8 α s J h 0 H' le_rfl (ne_of_lt h80)
  unfold Isel
  rw [hIa, if_neg (by linarith)]

noncomputable def pw (α s J I : ℝ) : ℝ :=
  if α / 2 ≤ I then 0 else if I < J then (3 * s - α) / 2 else α / 2 - I

theorem pw_vals (α s J : ℝ) (hα : 0 < α) (hs1 : 3 * α / 4 ≤ s) (hs2' : s < α)
    (hJs : J < α - s) (hx : 0 ≤ 2 * J - 2 * α + 3 * s)
    (hrel : J * (2 * α - 3 * s - J) = (5 * α ^ 2 - 16 * α * s + 12 * s ^ 2) / 4)
    (I : ℝ) (hI : 0 ≤ I) :
    0 ≤ pw α s J I ∧ sval α s I (pw α s J I) = Mf α s J I ∧
    bf α s I (pw α s J I) (q2s α s I (pw α s J I)) = Vbar α s J I ∧
    ∀ w, 0 ≤ w → sval α s I w ≤ sval α s I (pw α s J I) := by
  have hsg := AK_sign α s J I hrel
  unfold pw
  rcases le_or_gt (α / 2) I with hH | hH
  · rw [if_pos hH, sval_H α s I 0 hα hs1 hH, Mf_H α s J I hH, bval_H α s I 0 hα hs1 hH,
      Vbar_H α s J I hH]
    exact ⟨le_rfl, rfl, rfl, fun w _ => by rw [sval_H α s I w hα hs1 hH]⟩
  · rw [if_neg (not_le.2 hH)]
    rcases lt_or_ge I J with hIJ | hIJ
    · rw [if_pos hIJ, sval_K α s I hα hs1 hs2' hI (by linarith), Mf_K α s J I hH hIJ,
        bval_K α s I hα hs1 hs2' hI (by linarith), Vbar_K α s J I hH hIJ]
      have hKA : (α - 2 * I) ^ 2 / 8 ≤ (3 * s - α) / 2 * (α - s - I) := by
        have := mul_nonneg (sub_nonneg.2 hIJ.le) (by linarith : (0:ℝ) ≤ I - (2 * α - 3 * s - J))
        linarith
      refine ⟨by linarith, rfl, by unfold VK0; ring, fun w hw => ?_⟩
      have := sval_le α s I w hα hs1 hs2' hI hH hw
      rwa [max_eq_left hKA] at this
    · rw [if_neg (not_lt.2 hIJ), sval_A α s I hα hs1 hs2' hI hH, Mf_A α s J I hH.le hIJ,
        bval_A α s I hα hs1 hs2' hI hH, Vbar_A α s J I hH.le hIJ]
      have hKA : (3 * s - α) / 2 * (α - s - I) ≤ (α - 2 * I) ^ 2 / 8 := by
        have := mul_nonneg (sub_nonneg.2 hIJ) (by linarith : (0:ℝ) ≤ I - (2 * α - 3 * s - J))
        linarith
      refine ⟨by linarith, rfl, by unfold VA; ring, fun w hw => ?_⟩
      have := sval_le α s I w hα hs1 hs2' hI hH hw
      rwa [max_eq_right hKA] at this

theorem direct_opt (α s q2 qs : ℝ) (hqs : 0 ≤ qs) :
    (α - q2 - qs - s) * qs ≤ (α - q2 - qsD α s q2 - s) * qsD α s q2 := by
  unfold qsD
  rcases le_total 0 (α - q2 - s) with hc | hc
  · rw [max_eq_left hc]; nlinarith [sq_nonneg (qs - (α - q2 - s) / 2)]
  · rw [max_eq_right hc]; nlinarith

theorem c4_alg (α w1 h q1 Q1 qs Is V1 V2 : ℝ)
    (hg : (α - q1) * q1 - w1 * q1 ≤ (α - qs) * qs - w1 * qs - (q1 - qs) ^ 2)
    (hA : V1 - (w1 + h) * (Q1 - q1) ≤ V2 - (w1 + h) * Is) :
    (α - q1) * q1 - w1 * Q1 - h * (Q1 - q1) + V1 ≤
      (α - qs) * qs - w1 * (qs + Is) - h * Is + V2 := by
  nlinarith [sq_nonneg (q1 - qs)]


open StrategicInventory.Sequential in
/-- the equilibrium profile -/
noncomputable def σ8 (α h s J : ℝ) : Profile where
  w1 := (9 * α - 2 * h) / 17
  period1 := fun w1 => (max (α - w1) 0 / 2 + Isel α s J (w1 + h), max (α - w1) 0 / 2)
  price2 := fun _ Q1 q1 => pw α s J (Q1 - q1)
  period2 := fun _ Q1 q1 w2 => (max (q2s α s (Q1 - q1) w2 - (Q1 - q1)) 0, q2s α s (Q1 - q1) w2)
  direct := fun _ _ _ _ _ q2 => qsD α s q2

set_option maxHeartbeats 400000 in
open StrategicInventory.Sequential in
theorem exists_spe (α s J h : ℝ) (H : Hyp8 α s J h) : IsSPE α h s (σ8 α h s J) := by
  have H' := H
  obtain ⟨hα, hsl, hsu, hx0, hx2, hh, hh4, h68⟩ := H
  obtain ⟨hJs, hJa, hrel, hVA0⟩ := J8facts α s J h H'
  obtain ⟨hJ8, h80, h8a, hJc8⟩ := I8_facts α s J h H'
  have hVA : 0 < J → VK0 α s + (3 * s - α) / 2 * J < VA α J := fun hJ => hVA0 hJ.le
  have hs1 : 3 * α / 4 ≤ s := by linarith
  have hs1' : α / 2 < s := by linarith
  have keyB : ∀ w1 Q1 q1 : ℝ, 0 ≤ q1 → q1 ≤ Q1 →
      buyerPayoff α h ((σ8 α h s J).outcomeAtPrice2 w1 Q1 q1) =
        (α - q1) * q1 - w1 * Q1 - h * (Q1 - q1) + Vbar α s J (Q1 - q1) := by
    intro w1 Q1 q1 hq1 hqQ
    have hv := (pw_vals α s J hα hs1 hsu hJs hx0 hrel (Q1 - q1) (by linarith)).2.2.1
    simp only [buyerPayoff, Profile.outcomeAtPrice2, Profile.outcomeAtOrder2,
      Profile.outcomeAtDirect, σ8]
    unfold bf rev at hv
    linarith
  have keyS : ∀ w1 Q1 q1 : ℝ, 0 ≤ q1 → q1 ≤ Q1 →
      supplierPayoff α s ((σ8 α h s J).outcomeAtPrice2 w1 Q1 q1) =
        w1 * Q1 + Mf α s J (Q1 - q1) := by
    intro w1 Q1 q1 hq1 hqQ
    have hv := (pw_vals α s J hα hs1 hsu hJs hx0 hrel (Q1 - q1) (by linarith)).2.1
    simp only [supplierPayoff, Profile.outcomeAtPrice2, Profile.outcomeAtOrder2,
      Profile.outcomeAtDirect, σ8]
    unfold sval at hv
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w1 Q1 q1 w2 Q2 q2 _ _ _ _ _ _ _
    refine ⟨?_, fun qs hqs => ?_⟩
    · show 0 ≤ qsD α s q2
      unfold qsD; have := le_max_right (α - q2 - s) 0; linarith
    · simp only [supplierPayoff, Profile.outcomeAtDirect, σ8]
      linarith [direct_opt α s q2 qs hqs]
  · intro w1 Q1 q1 w2 hw1 hq1 hqQ hw2
    have hI : 0 ≤ Q1 - q1 := by linarith
    refine ⟨le_max_right _ _, q2s_nonneg α s (Q1 - q1) w2 hα hI, ?_,
      fun Q2 q2 hQ2 hq2 hqI => ?_⟩
    · show q2s α s (Q1 - q1) w2 ≤ Q1 - q1 + max (q2s α s (Q1 - q1) w2 - (Q1 - q1)) 0
      linarith [le_max_left (q2s α s (Q1 - q1) w2 - (Q1 - q1)) 0]
    · have hb := bf_opt α s (Q1 - q1) w2 hα hs1' hsu hI hw2 q2 hq2
      have hm : w2 * max (q2 - (Q1 - q1)) 0 ≤ w2 * Q2 :=
        mul_le_mul_of_nonneg_left (max_le (by linarith) hQ2) hw2
      simp only [buyerPayoff, Profile.outcomeAtDirect, Profile.outcomeAtOrder2, σ8]
      unfold bf rev at hb
      linarith [sq_nonneg (q2 - q2s α s (Q1 - q1) w2)]
  · intro w1 Q1 q1 hw1 hq1 hqQ
    have hI : 0 ≤ Q1 - q1 := by linarith
    have hv := pw_vals α s J hα hs1 hsu hJs hx0 hrel (Q1 - q1) hI
    refine ⟨hv.1, fun w2 hw2 => ?_⟩
    have h1 := hv.2.2.2 w2 hw2
    simp only [supplierPayoff, Profile.outcomeAtPrice2, Profile.outcomeAtOrder2,
      Profile.outcomeAtDirect, σ8]
    unfold sval at h1
    linarith
  · intro w1 hw1
    have hc : 0 ≤ w1 + h := by linarith
    have hqs : 0 ≤ max (α - w1) 0 / 2 := by have := le_max_right (α - w1) 0; linarith
    have hIs := Isel_nonneg α s J (w1 + h) hα hJa hc
    refine ⟨hqs, ?_, fun Q1 q1 hq1 hqQ => ?_⟩
    · show max (α - w1) 0 / 2 ≤ max (α - w1) 0 / 2 + Isel α s J (w1 + h)
      linarith
    · have hout : (σ8 α h s J).outcomeAtOrder1 w1 = (σ8 α h s J).outcomeAtPrice2 w1
          (max (α - w1) 0 / 2 + Isel α s J (w1 + h)) (max (α - w1) 0 / 2) := rfl
      rw [hout, keyB w1 Q1 q1 hq1 hqQ, keyB _ _ _ hqs (by linarith)]
      have e : max (α - w1) 0 / 2 + Isel α s J (w1 + h) - max (α - w1) 0 / 2 =
          Isel α s J (w1 + h) := by ring
      rw [e]
      have hg := g_strong α w1 q1 hq1
      have hA := AM α s J (w1 + h) (Q1 - q1) hα hJa hVA hc (by linarith)
      exact c4_alg α w1 h q1 Q1 _ _ _ _ hg hA
  · have hmax : max (α - ((9 * α - 2 * h) / 17)) 0 = α - ((9 * α - 2 * h) / 17) := max_eq_left (by linarith)
    have hq0' : 0 ≤ max (α - ((9 * α - 2 * h) / 17)) 0 / 2 := by
      have := le_max_right (α - ((9 * α - 2 * h) / 17)) 0; linarith
    have hle' : max (α - ((9 * α - 2 * h) / 17)) 0 / 2 ≤ max (α - ((9 * α - 2 * h) / 17)) 0 / 2 + Isel α s J (((9 * α - 2 * h) / 17) + h) := by
      have := Isel_nonneg α s J (((9 * α - 2 * h) / 17) + h) hα hJa (by linarith); linarith
    have hpath : (σ8 α h s J).path = (σ8 α h s J).outcomeAtPrice2 ((9 * α - 2 * h) / 17)
        (max (α - ((9 * α - 2 * h) / 17)) 0 / 2 + Isel α s J (((9 * α - 2 * h) / 17) + h)) (max (α - ((9 * α - 2 * h) / 17)) 0 / 2) := rfl
    refine ⟨by show 0 ≤ ((9 * α - 2 * h) / 17); linarith, fun w1 hw1 => ?_⟩
    have hc : 0 ≤ w1 + h := by linarith
    have hqs : 0 ≤ max (α - w1) 0 / 2 := by have := le_max_right (α - w1) 0; linarith
    have hIs := Isel_nonneg α s J (w1 + h) hα hJa hc
    have hout : (σ8 α h s J).outcomeAtOrder1 w1 = (σ8 α h s J).outcomeAtPrice2 w1
        (max (α - w1) 0 / 2 + Isel α s J (w1 + h)) (max (α - w1) 0 / 2) := rfl
    rw [hout, hpath, keyS _ _ _ hqs (by linarith), keyS _ _ _ hq0' hle']
    rw [Isel_star α s J h H', hmax]
    have e1 : max (α - w1) 0 / 2 + Isel α s J (w1 + h) - max (α - w1) 0 / 2 =
        Isel α s J (w1 + h) := by ring
    have e2 : (α - ((9 * α - 2 * h) / 17)) / 2 + (5 * (α - 4 * h) / 34) - (α - ((9 * α - 2 * h) / 17)) / 2 = (5 * (α - 4 * h) / 34) := by ring
    rw [e1, e2, Mf_A α s J (5 * (α - 4 * h) / 34) h8a.le hJ8.le]
    have hCL := (CL8 α s J h w1 (Isel α s J (w1 + h)) H' hw1 hIs
      (fun I' hI' => AM α s J (w1 + h) I' hα hJa hVA hc hI')).1
    unfold Fs at hCL
    have hfin : ((9 * α - 2 * h) / 17) * ((α - ((9 * α - 2 * h) / 17)) / 2 + (5 * (α - 4 * h) / 34)) + (α - 2 * (5 * (α - 4 * h) / 34)) ^ 2 / 8 =
        (9 * α - 2 * h) ^ 2 / 306 + 2 * h ^ 2 / 9 := by ring
    linarith

open StrategicInventory.Sequential in
theorem uniq (α s J h : ℝ) (H : Hyp8 α s J h) (σ : Profile) (hσ : IsSPE α h s σ) :
    σ.path = { w1 := (9 * α - 2 * h) / 17, Q1 := (13 * α - 18 * h) / 34,
               q1 := (4 * α + h) / 17, w2 := 2 * (3 * α + 5 * h) / 17,
               Q2 := (3 * α + 5 * h) / 17, q2 := (11 * α - 10 * h) / 34,
               qs := 0 } := by
  have H' := H
  obtain ⟨hα, hsl, hsu, hx0, hx2, hh, hh4, h68⟩ := H
  obtain ⟨hJs, hJa, hrel, hVA0⟩ := J8facts α s J h H'
  obtain ⟨hJ8, h80, h8a, hJc8⟩ := I8_facts α s J h H'
  have hs1 : 3 * α / 4 ≤ s := by linarith
  have hs1' : α / 2 < s := by linarith
  have hS : ∀ w1, 0 ≤ w1 → supplierPayoff α s (σ.outcomeAtOrder1 w1) =
      Fs α s J w1 ((σ.period1 w1).1 - (σ.period1 w1).2) := by
    intro w1 hw1
    obtain ⟨hq0, hqQ, -⟩ := hσ.2.2.2.1 w1 hw1
    have hb := buyer1 α h s J hα hs1 hsu hh hJs hx0 hrel hVA0 σ hσ w1 hw1
    have hv := price2_vals α h s J hα hs1 hsu hJs hx0 hrel hVA0 σ hσ w1 _ _ hw1 hq0 hqQ
    have hout : σ.outcomeAtOrder1 w1 =
        σ.outcomeAtPrice2 w1 (σ.period1 w1).1 (σ.period1 w1).2 := rfl
    rw [hout, hv.1]
    unfold Fs
    rw [← hb.1]; ring
  have hw8 : (0:ℝ) ≤ ((9 * α - 2 * h) / 17) := by linarith
  have hIs : (σ.period1 ((9 * α - 2 * h) / 17)).1 - (σ.period1 ((9 * α - 2 * h) / 17)).2 = (5 * (α - 4 * h) / 34) := by
    have hb := buyer1 α h s J hα hs1 hsu hh hJs hx0 hrel hVA0 σ hσ ((9 * α - 2 * h) / 17) hw8
    obtain ⟨hq0, hqQ, -⟩ := hσ.2.2.2.1 ((9 * α - 2 * h) / 17) hw8
    by_contra hne
    have h1 := AMstar8 α s J h _ H' (by linarith) hne
    have h2 := hb.2.1 (5 * (α - 4 * h) / 34) h80.le
    linarith
  have hstar : supplierPayoff α s (σ.outcomeAtOrder1 ((9 * α - 2 * h) / 17)) =
      (9 * α - 2 * h) ^ 2 / 306 + 2 * h ^ 2 / 9 := by
    rw [hS _ hw8, hIs]
    unfold Fs
    rw [Mf_A α s J (5 * (α - 4 * h) / 34) h8a.le hJ8.le, max_eq_left (show 0 ≤ α - ((9 * α - 2 * h) / 17) by linarith)]
    ring
  obtain ⟨hw0, hsup⟩ := hσ.2.2.2.2
  have hge := hsup ((9 * α - 2 * h) / 17) hw8
  rw [hstar] at hge
  have hpath : σ.path = σ.outcomeAtOrder1 σ.w1 := rfl
  rw [hpath, hS σ.w1 hw0] at hge
  have hb0 := buyer1 α h s J hα hs1 hsu hh hJs hx0 hrel hVA0 σ hσ σ.w1 hw0
  obtain ⟨hq00, hqQ0, -⟩ := hσ.2.2.2.1 σ.w1 hw0
  have hw1eq : σ.w1 = ((9 * α - 2 * h) / 17) :=
    (CL8 α s J h σ.w1 _ H' hw0 (by linarith) hb0.2.1).2 hge
  have hb := buyer1 α h s J hα hs1 hsu hh hJs hx0 hrel hVA0 σ hσ ((9 * α - 2 * h) / 17) hw8
  obtain ⟨hq0, hqQ, -⟩ := hσ.2.2.2.1 ((9 * α - 2 * h) / 17) hw8
  have hv := price2_vals α h s J hα hs1 hsu hJs hx0 hrel hVA0 σ hσ ((9 * α - 2 * h) / 17) _ _ hw8 hq0 hqQ
  have hp : σ.price2 ((9 * α - 2 * h) / 17) (σ.period1 ((9 * α - 2 * h) / 17)).1 (σ.period1 ((9 * α - 2 * h) / 17)).2 = α / 2 - (5 * (α - 4 * h) / 34) := by
    have := hv.2.2.2.2 (by rw [hIs]; exact hJ8) (by rw [hIs]; exact h8a)
    rw [hIs] at this; exact this
  have hpp : (0:ℝ) ≤ α / 2 - (5 * (α - 4 * h) / 34) := by linarith
  obtain ⟨hq2, hQ2⟩ := period2_pin α h s hα hs1' hsu σ hσ ((9 * α - 2 * h) / 17) _ _ (α / 2 - (5 * (α - 4 * h) / 34))
    hw8 hq0 hqQ hpp
  rw [hIs, q2s_A α s (5 * (α - 4 * h) / 34) hα hs1 hsu h80.le h8a] at hq2 hQ2
  have hQ2v : (σ.period2 ((9 * α - 2 * h) / 17) (σ.period1 ((9 * α - 2 * h) / 17)).1 (σ.period1 ((9 * α - 2 * h) / 17)).2 (α / 2 - (5 * (α - 4 * h) / 34))).1 = (α - 2 * (5 * (α - 4 * h) / 34)) / 4 := by
    rw [max_eq_left (by linarith)] at hQ2
    have hpos : (0:ℝ) < α / 2 - (5 * (α - 4 * h) / 34) := by linarith
    have := mul_left_cancel₀ hpos.ne' hQ2
    rw [this]; ring
  obtain ⟨hQ0', hq0', hqI', -⟩ := hσ.2.1 ((9 * α - 2 * h) / 17) _ _ (α / 2 - (5 * (α - 4 * h) / 34)) hw8 hq0 hqQ hpp
  have hd := direct_pin α h s σ hσ ((9 * α - 2 * h) / 17) _ _ (α / 2 - (5 * (α - 4 * h) / 34)) _ _ hw8 hq0 hqQ hpp hQ0' hq0' hqI'
  have hd0 : qsD α s ((α + 2 * (5 * (α - 4 * h) / 34)) / 4) = 0 := by
    unfold qsD; rw [max_eq_right (by linarith)]; ring
  have hq1v : (σ.period1 ((9 * α - 2 * h) / 17)).2 = (α - ((9 * α - 2 * h) / 17)) / 2 := by
    rw [hb.1, max_eq_left (by linarith)]
  have hQ1v : (σ.period1 ((9 * α - 2 * h) / 17)).1 = (5 * (α - 4 * h) / 34) + (α - ((9 * α - 2 * h) / 17)) / 2 := by
    linarith [hIs]
  rw [hpath, hw1eq]
  show (⟨((9 * α - 2 * h) / 17), (σ.period1 ((9 * α - 2 * h) / 17)).1, (σ.period1 ((9 * α - 2 * h) / 17)).2,
    σ.price2 ((9 * α - 2 * h) / 17) (σ.period1 ((9 * α - 2 * h) / 17)).1 (σ.period1 ((9 * α - 2 * h) / 17)).2,
    (σ.period2 ((9 * α - 2 * h) / 17) (σ.period1 ((9 * α - 2 * h) / 17)).1 (σ.period1 ((9 * α - 2 * h) / 17)).2
      (σ.price2 ((9 * α - 2 * h) / 17) (σ.period1 ((9 * α - 2 * h) / 17)).1 (σ.period1 ((9 * α - 2 * h) / 17)).2)).1,
    (σ.period2 ((9 * α - 2 * h) / 17) (σ.period1 ((9 * α - 2 * h) / 17)).1 (σ.period1 ((9 * α - 2 * h) / 17)).2
      (σ.price2 ((9 * α - 2 * h) / 17) (σ.period1 ((9 * α - 2 * h) / 17)).1 (σ.period1 ((9 * α - 2 * h) / 17)).2)).2,
    σ.direct ((9 * α - 2 * h) / 17) (σ.period1 ((9 * α - 2 * h) / 17)).1 (σ.period1 ((9 * α - 2 * h) / 17)).2
      (σ.price2 ((9 * α - 2 * h) / 17) (σ.period1 ((9 * α - 2 * h) / 17)).1 (σ.period1 ((9 * α - 2 * h) / 17)).2)
      (σ.period2 ((9 * α - 2 * h) / 17) (σ.period1 ((9 * α - 2 * h) / 17)).1 (σ.period1 ((9 * α - 2 * h) / 17)).2
        (σ.price2 ((9 * α - 2 * h) / 17) (σ.period1 ((9 * α - 2 * h) / 17)).1 (σ.period1 ((9 * α - 2 * h) / 17)).2)).1
      (σ.period2 ((9 * α - 2 * h) / 17) (σ.period1 ((9 * α - 2 * h) / 17)).1 (σ.period1 ((9 * α - 2 * h) / 17)).2
        (σ.price2 ((9 * α - 2 * h) / 17) (σ.period1 ((9 * α - 2 * h) / 17)).1 (σ.period1 ((9 * α - 2 * h) / 17)).2)).2⟩ :
      Outcome) = _
  rw [hp, hd, hq2, hd0, hQ2v, hq1v, hQ1v]
  congr 1 <;> ring

open StrategicInventory.Sequential in
theorem hyp_of (α h s : ℝ) (hα : 0 < α) (hh : 0 ≤ h) (hs : 0 ≤ s)
    (hreg : (h < h11 α s ∧ s3 α ≤ s ∧ s < 5 * α / 6) ∨
      (h < α / 4 ∧ 5 * α / 6 ≤ s ∧ s < α)) :
    Hyp8 α s (invStar α s) h := by
  have hsl : 77 * α / 100 ≤ s := by
    rcases hreg with ⟨-, hs3, -⟩ | ⟨-, hs5, -⟩
    · linarith [s3_gt α hα]
    · linarith
  have hsu : s < α := by
    rcases hreg with ⟨-, -, h1⟩ | ⟨-, -, h1⟩ <;> linarith
  obtain ⟨hx0, hx2⟩ := xRoot_facts α s hα (by linarith) (by linarith)
  have hJ : invStar α s = (2 * α - 3 * s + xRoot α s) / 2 := rfl
  have hxJ : 2 * invStar α s - 2 * α + 3 * s = xRoot α s := by rw [hJ]; ring
  rcases hreg with ⟨h11h, hs3, hs56⟩ | ⟨hh4, hs5, hs1⟩
  · have hJ0 := J_pos α s (xRoot α s) hα hsl hs56 hx0 hx2
    have hin : 3 * α ^ 2 + 6 * s ^ 2 - 8 * α * s + (4 * α - 6 * s) * xRoot α s =
        (2 * invStar α s) ^ 2 := by
      rw [hJ]; linear_combination (-1 : ℝ) * hx2
    unfold h11 at h11h
    rw [hin, Real.sqrt_sq (by rw [hJ]; linarith)] at h11h
    have hk0 : 0 < Real.sqrt 17 := Real.sqrt_pos.2 (by norm_num)
    have hk2 : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
    have hJp : 0 < invStar α s := by rw [hJ]; linarith
    have hpos : 0 < Real.sqrt 17 * (2 * invStar α s) := mul_pos hk0 (by linarith)
    have hlt : Real.sqrt 17 * (2 * invStar α s) < α - 4 * h := by linarith
    refine ⟨hα, hsl, hsu, by rw [hxJ]; exact hx0, by rw [hxJ]; exact hx2, hh, by linarith,
      fun _ => ?_⟩
    have h2 := pow_lt_pow_left₀ hlt hpos.le (by norm_num : (2:ℕ) ≠ 0)
    have e : (Real.sqrt 17 * (2 * invStar α s)) ^ 2 = 68 * invStar α s ^ 2 := by
      rw [mul_pow, hk2]; ring
    linarith
  · refine ⟨hα, hsl, hsu, by rw [hxJ]; exact hx0, by rw [hxJ]; exact hx2, hh, hh4,
      fun hJp => ?_⟩
    exfalso
    have := J_pos_s α s (invStar α s) hα hsl (by rw [hxJ]; exact hx0) (by rw [hxJ]; exact hx2) hJp
    linarith

end SI8

open StrategicInventory.Sequential in
theorem solution (α h s : ℝ) (hα : 0 < α) (hh : 0 ≤ h) (hs : 0 ≤ s)
    (hreg : (h < h11 α s ∧ s3 α ≤ s ∧ s < 5 * α / 6) ∨
      (h < α / 4 ∧ 5 * α / 6 ≤ s ∧ s < α)) :
    (∃ σ : Profile, IsSPE α h s σ) ∧
      ∀ σ : Profile, IsSPE α h s σ →
        σ.path = { w1 := (9 * α - 2 * h) / 17, Q1 := (13 * α - 18 * h) / 34,
                   q1 := (4 * α + h) / 17, w2 := 2 * (3 * α + 5 * h) / 17,
                   Q2 := (3 * α + 5 * h) / 17, q2 := (11 * α - 10 * h) / 34,
                   qs := 0 } := by
  have H := SI8.hyp_of α h s hα hh hs hreg
  exact ⟨⟨_, SI8.exists_spe α s _ h H⟩, fun σ hσ => SI8.uniq α s _ h H σ hσ⟩
