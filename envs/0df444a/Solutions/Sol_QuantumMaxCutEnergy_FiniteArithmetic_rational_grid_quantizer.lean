-- Prove2me | solution 1 for QuantumMaxCutEnergy.FiniteArithmetic.rational_grid_quantizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T16:15:50.039793+00:00
-- url     : https://prove2.me/submissions/5ae5cf53-644c-4ce9-810d-91bee24a6a04

import Definitions.Def_QuantumMaxCutFiniteNumericRuntime

/-!
An actual finite Boolean-machine rational grid quantizer. The approximation
contract assumes q >= -1, as holds for feasible Pauli moments. The machine is
total for all rational inputs; M=0 is allowed computationally but excluded
from the approximation theorem.
-/

noncomputable section

namespace QMCSDPConditioning
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

/-- Shift nonnegative, divide natural numerators, and shift back. -/
def gridRound (M : ℕ) (q : ℚ) : ℚ :=
  let u := q + 1
  (((u.num.natAbs * M / u.den : ℕ) : ℚ) / (M : ℚ)) - 1

@[fun_prop] theorem gridRound_poly : OAI.MetricKMedian.Binary.Automatic.Poly (fun x : ℕ × ℚ => gridRound x.1 x.2) :=
  by
  have hone : OAI.MetricKMedian.Binary.Automatic.Poly (fun _ : ℚ => (1 : ℚ)) :=
    OAI.MetricKMedian.Binary.Automatic.Poly.const (α := ℚ) (β := ℚ) (1 : ℚ)
  have hid : OAI.MetricKMedian.Binary.Automatic.Poly (id : ℚ → ℚ) := OAI.MetricKMedian.Binary.Automatic.Poly.identity
  have hp : OAI.MetricKMedian.Binary.Automatic.Poly (fun q : ℚ => (q, (1 : ℚ))) :=
    OAI.MetricKMedian.Binary.Automatic.Poly.pair (α := ℚ) (β := ℚ) (γ := ℚ) hid hone
  have hshift : OAI.MetricKMedian.Binary.Automatic.Poly (fun q : ℚ => q + 1) :=
    OAI.MetricKMedian.Binary.Automatic.Poly.comp (α := ℚ) (β := ℚ × ℚ) (γ := ℚ) OAI.MetricKMedian.Binary.Automatic.Poly.rat_add hp
  have hmag : OAI.MetricKMedian.Binary.Automatic.Poly (fun q : ℚ => q.num.natAbs) :=
    ⟨OAI.MetricKMedian.Binary.PolyProgram.ratNum.comp OAI.MetricKMedian.Binary.PolyProgram.intAbs⟩
  have hden : OAI.MetricKMedian.Binary.Automatic.Poly (Rat.den : ℚ → ℕ) := ⟨OAI.MetricKMedian.Binary.PolyProgram.ratDen⟩
  have hdiv : OAI.MetricKMedian.Binary.Automatic.Poly (fun x : ℕ × ℕ => x.1 / x.2) := ⟨OAI.MetricKMedian.Binary.PolyProgram.natDiv⟩
  have hu : OAI.MetricKMedian.Binary.Automatic.Poly (fun x : ℕ × ℚ => x.2 + 1) := OAI.MetricKMedian.Binary.Automatic.Poly.comp hshift OAI.MetricKMedian.Binary.Automatic.Poly.snd
  have ha : OAI.MetricKMedian.Binary.Automatic.Poly (fun x : ℕ × ℚ => (x.2 + 1).num.natAbs) := OAI.MetricKMedian.Binary.Automatic.Poly.comp (α := ℕ × ℚ) (β := ℚ) (γ := ℕ)
    (f := fun q : ℚ => q.num.natAbs) (g := fun x : ℕ × ℚ => x.2 + 1) hmag hu
  have hd : OAI.MetricKMedian.Binary.Automatic.Poly (fun x : ℕ × ℚ => (x.2 + 1).den) := OAI.MetricKMedian.Binary.Automatic.Poly.comp hden hu
  have ht : OAI.MetricKMedian.Binary.Automatic.Poly (fun x : ℕ × ℚ => (x.2 + 1).num.natAbs * x.1 / (x.2 + 1).den) :=
    OAI.MetricKMedian.Binary.Automatic.Poly.comp hdiv (OAI.MetricKMedian.Binary.Automatic.Poly.pair (OAI.MetricKMedian.Binary.Automatic.Poly.comp OAI.MetricKMedian.Binary.Automatic.Poly.nat_mul (OAI.MetricKMedian.Binary.Automatic.Poly.pair ha OAI.MetricKMedian.Binary.Automatic.Poly.fst)) hd)
  have hn : OAI.MetricKMedian.Binary.Automatic.Poly (fun x : ℕ × ℚ =>
      (((x.2 + 1).num.natAbs * x.1 / (x.2 + 1).den : ℕ) : ℚ)) := OAI.MetricKMedian.Binary.Automatic.Poly.comp OAI.MetricKMedian.Binary.Automatic.Poly.rat_ofNat ht
  have hm : OAI.MetricKMedian.Binary.Automatic.Poly (fun x : ℕ × ℚ => (x.1 : ℚ)) := OAI.MetricKMedian.Binary.Automatic.Poly.comp OAI.MetricKMedian.Binary.Automatic.Poly.rat_ofNat OAI.MetricKMedian.Binary.Automatic.Poly.fst
  have honeInput : OAI.MetricKMedian.Binary.Automatic.Poly (fun _ : ℕ × ℚ => (1 : ℚ)) :=
    OAI.MetricKMedian.Binary.Automatic.Poly.const (α := ℕ × ℚ) (β := ℚ) (1 : ℚ)
  exact OAI.MetricKMedian.Binary.Automatic.Poly.comp OAI.MetricKMedian.Binary.Automatic.Poly.rat_sub (OAI.MetricKMedian.Binary.Automatic.Poly.pair
    (OAI.MetricKMedian.Binary.Automatic.Poly.comp OAI.MetricKMedian.Binary.Automatic.Poly.rat_div (OAI.MetricKMedian.Binary.Automatic.Poly.pair hn hm)) honeInput)

def gridRoundProgram : PolyProgram (encodePair Nat.bits Ratio.encode) Ratio.encode
    (fun x : ℕ × ℚ => gridRound x.1 x.2) :=
  OAI.MetricKMedian.Binary.Automatic.Poly.program gridRound_poly

def gridRound_polynomialTime : Turing.TM2ComputableInPolyTime
    (encodePair Nat.bits Ratio.encode) Ratio.encode
    (fun x : ℕ × ℚ => gridRound x.1 x.2) := gridRoundProgram.stock

theorem gridRound_interval (M : ℕ) (hM : 0 < M) (q : ℚ) (hq : -1 ≤ q) :
    gridRound M q ≤ q ∧ q < gridRound M q + 1 / (M : ℚ) := by
  let u := q + 1
  let a := u.num.natAbs
  let d := u.den
  let t := a * M / d
  have hu : (0 : ℚ) ≤ u := by dsimp [u]; linarith only [hq]
  have hn : (0 : ℤ) ≤ u.num := Rat.num_nonneg.mpr hu
  have hdNat : 0 < d := Rat.den_pos u
  have hd : (0 : ℚ) < d := by exact_mod_cast hdNat
  have hm : (0 : ℚ) < M := by exact_mod_cast hM
  have hanum : (a : ℚ) = (u.num : ℚ) := by
    dsimp [a]
    have hh := congrArg (fun z : ℤ => (z : ℚ)) (Int.natAbs_of_nonneg hn)
    simpa only [Int.cast_natCast] using hh
  have ha : (a : ℚ) / (d : ℚ) = q + 1 := by
    rw [hanum]
    exact Rat.num_div_den u
  have ha' : (a : ℚ) = (q + 1) * (d : ℚ) := (div_eq_iff (ne_of_gt hd)).mp ha
  have hlo : (t : ℚ) * (d : ℚ) ≤ (a : ℚ) * (M : ℚ) := by
    exact_mod_cast Nat.div_mul_le_self (a * M) d
  have hhi : (a : ℚ) * (M : ℚ) < (t : ℚ) * (d : ℚ) + (d : ℚ) := by
    exact_mod_cast (Nat.lt_div_mul_add (a := a * M) hdNat)
  rw [ha'] at hlo hhi
  have hlow : (t : ℚ) ≤ (q + 1) * (M : ℚ) := by
    apply (mul_le_mul_iff_left₀ hd).mp
    nlinarith only [hlo]
  have hhigh : (q + 1) * (M : ℚ) < (t : ℚ) + 1 := by
    apply (mul_lt_mul_iff_left₀ hd).mp
    nlinarith only [hhi]
  have hlow' : (t : ℚ) / (M : ℚ) ≤ q + 1 := (div_le_iff₀ hm).mpr hlow
  have hhigh' : q + 1 < ((t : ℚ) + 1) / (M : ℚ) := (lt_div_iff₀ hm).mpr hhigh
  rw [add_div] at hhigh'
  change (t : ℚ) / (M : ℚ) - 1 ≤ q ∧
    q < (t : ℚ) / (M : ℚ) - 1 + 1 / (M : ℚ)
  constructor <;> linarith only [hlow', hhigh']

theorem gridRound_abs_error (M : ℕ) (hM : 0 < M) (q : ℚ) (hq : -1 ≤ q) :
    |gridRound M q - q| ≤ 1 / (M : ℚ) := by
  obtain ⟨hlo, hhi⟩ := gridRound_interval M hM q hq
  rw [abs_of_nonpos (sub_nonpos.mpr hlo)]
  linarith only [hhi]

theorem gridRound_preserves_box (M : ℕ) (hM : 0 < M) (q : ℚ)
    (hq0 : -1 ≤ q) (hq1 : q ≤ 1) : -1 ≤ gridRound M q ∧ gridRound M q ≤ 1 := by
  constructor
  · unfold gridRound
    have hh : (0 : ℚ) ≤
        ((((q + 1).num.natAbs * M / (q + 1).den : ℕ) : ℚ) / (M : ℚ)) := by
      positivity
    linarith only [hh]
  · exact (gridRound_interval M hM q hq0).1.trans hq1

theorem gridRound_one (M : ℕ) (hM : 0 < M) : gridRound M 1 = 1 := by
  have hm : (M : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hM
  unfold gridRound
  norm_num
  push_cast
  field_simp [hm]
  ring

end QMCSDPConditioning



theorem solution :
    ∃ f : ℕ × ℚ → ℚ,
      Nonempty (OAI.MetricKMedian.Binary.PolyProgram
        (OAI.MetricKMedian.Binary.encodePair Nat.bits OAI.MetricKMedian.Binary.Ratio.encode)
        OAI.MetricKMedian.Binary.Ratio.encode f) ∧
      ∀ M : ℕ, 0 < M → ∀ q : ℚ, -1 ≤ q →
        f (M, q) ≤ q ∧ q < f (M, q) + 1 / (M : ℚ) ∧
        |f (M, q) - q| ≤ 1 / (M : ℚ) ∧
        (q ≤ 1 → -1 ≤ f (M, q) ∧ f (M, q) ≤ 1) ∧
        f (M, 1) = 1  := by
  refine ⟨fun x => QMCSDPConditioning.gridRound x.1 x.2,
    ⟨QMCSDPConditioning.gridRoundProgram⟩, ?_⟩
  intro M hM q hq
  obtain ⟨hlo, hhi⟩ := QMCSDPConditioning.gridRound_interval M hM q hq
  exact ⟨hlo, hhi, QMCSDPConditioning.gridRound_abs_error M hM q hq,
    fun hq1 => QMCSDPConditioning.gridRound_preserves_box M hM q hq hq1,
    QMCSDPConditioning.gridRound_one M hM⟩

#print axioms solution
