-- Prove2me | solution 1 for UpperTheory.HF.vd_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:48:15.594737+00:00
-- url     : https://prove2.me/submissions/bfa4c4da-3df8-4483-bdcd-56483d2950b2

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_VdFormula
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_LayerBot
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_VdLe
import Theorems.Thm_Formalism_HC_Der_Rd_sum_totient_pow
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_UpperTheory_HF_layer_bot
import Theorems.Thm_UpperTheory_HF_vd_formula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
open UpperTheory.HF
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise
private theorem arith {l : ℕ} (hl : l.Prime) (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), (1 - ((l ^ j).totient : ℝ) / ((l ^ (k + 1)).totient : ℝ)) =
      ((k + 1 : ℕ) : ℝ) - 1 / ((l : ℝ) - 1) := by
  rw [Finset.sum_sub_distrib, ← Finset.sum_div]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hs : (∑ j ∈ Finset.range (k + 1), ((l ^ j).totient : ℝ)) = (l : ℝ) ^ k := by
    exact_mod_cast Formalism.HC.Der.Rd.sum_totient_pow hl k
  rw [hs, Nat.totient_prime_pow_succ hl]
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hl0 : (l : ℝ) - 1 ≠ 0 := by linarith
  have hp : (l : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by linarith)
  push_cast [Nat.cast_sub hl.one_le]
  congr 1
  rw [div_mul_eq_div_div, div_self hp]
private theorem intCast_mul_mul_mul_eq_of_mul_eq {l : ℕ} (hl : l.Prime) {j e c : ℕ} (hje : j ≤ e)
    (hd : c ∣ (l ^ e).totient / (l ^ j).totient) :
    1 - 1 / (c : ℝ) ≤ 1 - ((l ^ j).totient : ℝ) / ((l ^ e).totient : ℝ) := by
  have hjd : (l ^ j).totient ∣ (l ^ e).totient := Nat.totient_dvd_of_dvd (pow_dvd_pow l hje)
  have hj0 : 0 < (l ^ j).totient := Nat.totient_pos.2 (pow_pos hl.pos j)
  have he0 : 0 < (l ^ e).totient := Nat.totient_pos.2 (pow_pos hl.pos e)
  have hq0 : 0 < (l ^ e).totient / (l ^ j).totient := Nat.div_pos (Nat.le_of_dvd he0 hjd) hj0
  have hc0 : 0 < c := Nat.pos_of_dvd_of_pos hd hq0
  have hcle : c ≤ (l ^ e).totient / (l ^ j).totient := Nat.le_of_dvd hq0 hd
  have hq : (((l ^ e).totient / (l ^ j).totient : ℕ) : ℝ) =
      ((l ^ e).totient : ℝ) / ((l ^ j).totient : ℝ) :=
    Nat.cast_div hjd (by exact_mod_cast hj0.ne')
  have h1 : (1 : ℝ) / (((l ^ e).totient / (l ^ j).totient : ℕ) : ℝ) ≤ 1 / (c : ℝ) :=
    one_div_le_one_div_of_le (by exact_mod_cast hc0) (by exact_mod_cast hcle)
  rw [hq, one_div_div] at h1
  linarith
end

set_option autoImplicit false
open UpperTheory.HF
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise
namespace UpperTheory.HF
theorem _root_.solution :
    ∀ {φ : Frame} (H : HostAx φ) {l : ℕ}, l.Prime → H.vdH l ≤ (H.sl l : ℝ) - 1 / ((l : ℝ) - 1) ∧ H.vdH l ≤ (H.condE.factorization l : ℝ) := by
  intro φ H l hl
  have heN := (layer_bot H.toHostRaw hl (Nat.zero_le (H.condN.factorization l))).2.2
  simp only [UpperTheory.HF.Formalism.HC.HostRaw.sl]
  generalize hE : (UpperTheory.HF.Formalism.HC.HostRaw.condE H.toHostRaw).factorization l = e at heN ⊢
  have hcard : ∀ j ∈ Finset.range (H.condN.factorization l),
      (1 - 1 / (Nat.card (UpperTheory.HF.Formalism.HC.HostRaw.imgOne H.toHostRaw
        (H.condN / l ^ H.condN.factorization l * l ^ j)) : ℝ)) ≤
      if j < e then 1 - ((l ^ j).totient : ℝ) / ((l ^ e).totient : ℝ) else 0 := by
    intro j hj
    have hjN : j ≤ H.condN.factorization l := (Finset.mem_range.1 hj).le
    obtain ⟨hbot, hdvd, -⟩ := layer_bot H.toHostRaw hl hjN
    rw [hE] at hbot hdvd
    split_ifs with hje
    · exact intCast_mul_mul_mul_eq_of_mul_eq hl hje.le (hdvd hje.le)
    · push_neg at hje
      rw [hbot.2 hje, Subgroup.card_bot]
      simp
  have hsum := Finset.sum_le_sum hcard
  rw [← vd_formula H hl] at hsum
  have hS : ∑ j ∈ Finset.range (H.condN.factorization l),
      (if j < e then 1 - ((l ^ j).totient : ℝ) / ((l ^ e).totient : ℝ) else 0) =
      ∑ j ∈ Finset.range e, (1 - ((l ^ j).totient : ℝ) / ((l ^ e).totient : ℝ)) := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le heN
    rw [hm, Finset.sum_range_add]
    have h2 : ∑ x ∈ Finset.range m,
        (if e + x < e then 1 - ((l ^ (e + x)).totient : ℝ) / ((l ^ e).totient : ℝ) else 0) = 0 :=
      Finset.sum_eq_zero (fun x _ => if_neg (by omega))
    rw [h2, add_zero]
    exact Finset.sum_congr rfl (fun j hj => if_pos (Finset.mem_range.1 hj))
  rw [hS] at hsum
  have hle : ∑ j ∈ Finset.range e, (1 - ((l ^ j).totient : ℝ) / ((l ^ e).totient : ℝ)) ≤ (e : ℝ) := by
    calc _ ≤ ∑ j ∈ Finset.range e, (1 : ℝ) :=
          Finset.sum_le_sum (fun j _ => sub_le_self 1 (by positivity))
      _ = e := by simp
  refine ⟨?_, hsum.trans hle⟩
  rcases e with _ | k
  · have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
    have h1 : 1 / ((l : ℝ) - 1) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    simp only [Finset.range_zero, Finset.sum_empty] at hsum
    simp only [Nat.zero_eq, zero_le, max_eq_left, Nat.cast_one]
    linarith
  · rw [arith hl k] at hsum
    rw [max_eq_right (by omega)]
    exact hsum
end UpperTheory.HF
