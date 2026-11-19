-- Prove2me | solution 1 for QueueSignal.unique_crossing
-- status  : ACCEPTED   (prove)
-- author  : @shuffle
-- created : 2026-11-18T06:11:16.259681+00:00
-- url     : https://prove2.me/submissions/3e4ac9b3-dc24-48a1-bed3-8d93d861bb3a

import Definitions.Def_QueueSignal_QueueModel
import Theorems.Thm_QueueSignal_lamO_eq_and_strictMono
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open QueueSignal

theorem solution (P : Params) (hP : P.Valid) (d : ℝ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    ∃ lhat : ℝ, 0 < lhat ∧ lamO P lhat d = lamU P lhat d ∧
      (∀ lam : ℝ, 0 < lam → lamO P lam d = lamU P lam d → lam = lhat) ∧
      (∀ lam : ℝ, 0 < lam → lam < lhat → lamO P lam d < lamU P lam d) ∧
      (∀ lam : ℝ, lhat < lam → lamU P lam d < lamO P lam d) := by
  rcases hP with ⟨hμ, hθ, hVL, hVHL, hδ₀, hδ₁⟩
  have hV : P.θ / P.μ < P.Vbar d := by
    unfold Params.Vbar
    nlinarith [mul_nonneg hd0 (sub_nonneg.mpr hVHL.le)]
  have hV0 : 0 < P.Vbar d := (div_pos hθ hμ).trans hV
  have hθμ : P.θ < P.Vbar d * P.μ := (div_lt_iff₀ hμ).mp hV
  let a := P.Vbar d * P.μ / P.θ
  have ha : 1 < a := (lt_div_iff₀ hθ).mpr (by simpa using hθμ)
  let cap := P.μ - P.θ / P.Vbar d
  have hcap : 0 < cap := sub_pos.mpr ((div_lt_iff₀ hV0).mpr (by simpa [mul_comm] using hθμ))
  have hcapμ : cap < P.μ := sub_lt_self _ (div_pos hθ hV0)
  let n := (P.naorN d).toNat
  have hfloor : (1 : ℤ) ≤ ⌊a⌋ := Int.le_floor.mpr (by exact_mod_cast ha.le)
  have hn : (n : ℤ) = ⌊a⌋ - 1 := by
    change ((⌊a⌋ - (1 : ℤ)).toNat : ℤ) = ⌊a⌋ - 1
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hfloor)
  have hn_cast : (n : ℝ) = (⌊a⌋ : ℤ) - 1 := by exact_mod_cast hn
  have ha_n : a < (n : ℝ) + 2 := by linarith [Int.lt_floor_add_one a]
  let S : ℝ → ℝ := fun lam => ∑ i ∈ Finset.range (n + 2), (lam / P.μ) ^ i
  have hS (lam : ℝ) (hlam : 0 ≤ lam) : 0 < S lam := by
    have hnonneg (i : ℕ) : 0 ≤ (lam / P.μ) ^ i := pow_nonneg (div_nonneg hlam hμ.le) i
    have h := Finset.single_le_sum (f := fun i => (lam / P.μ) ^ i)
      (fun i _ => hnonneg i) (Finset.mem_range.mpr (show 0 < n + 2 by omega))
    simp only [pow_zero] at h
    exact zero_lt_one.trans_le h
  obtain ⟨hformula, hmono⟩ := lamO_eq_and_strictMono P
    ⟨hμ, hθ, hVL, hVHL, hδ₀, hδ₁⟩ d hd0 hd1
  have hless (lam : ℝ) (hlam : 0 < lam) : lamO P lam d < lam := by
    have ht : 0 < (lam / P.μ) ^ (n+1) / S lam :=
      div_pos (pow_pos (div_pos hlam hμ) _) (hS _ hlam.le)
    calc
      lamO P lam d = lam * (1 - (lam / P.μ) ^ (n+1) / S lam) := (hformula _ hlam).1
      _ < lam * 1 := mul_lt_mul_of_pos_left (sub_lt_self _ ht) hlam
      _ = lam := mul_one _
  have hbranch (lam : ℝ) : lamU P lam d = min lam cap := by
    by_cases h : lam < cap
    · exact (if_pos h).trans (min_eq_left h.le).symm
    · exact (if_neg h).trans (min_eq_right (le_of_not_gt h)).symm
  have htop : cap < lamO P P.μ d := by
    have hSn : S P.μ = (n : ℝ) + 2 := by simp [S, div_self hμ.ne']
    have hratio : P.μ / ((n : ℝ) + 2) < P.θ / P.Vbar d := by
      apply (div_lt_div_iff₀ (by positivity : 0 < (n : ℝ) + 2) hV0).mpr
      have h := (div_lt_iff₀ hθ).mp ha_n
      simpa only [mul_comm P.μ (P.Vbar d), mul_comm ((n : ℝ) + 2) P.θ] using h
    change P.μ - P.θ / P.Vbar d < _
    rw [(hformula _ hμ).2]
    change P.μ - P.θ / P.Vbar d < P.μ - P.μ / S P.μ
    rw [hSn]
    exact sub_lt_sub_left hratio _
  have hcts : ContinuousOn (fun lam => P.μ - P.μ / S lam) (Set.Icc cap P.μ) := by
    have hsum : Continuous S := by
      unfold S
      exact continuous_finsetSum _ (fun i _ => (continuous_id.div_const _).pow _)
    exact continuousOn_const.sub (continuousOn_const.div hsum.continuousOn fun x hx =>
      (hS x (hcap.le.trans hx.1)).ne')
  obtain ⟨lhat, hlhat, hval⟩ := intermediate_value_Icc hcapμ.le hcts
    (show cap ∈ Set.Icc (P.μ - P.μ / S cap) (P.μ - P.μ / S P.μ) from
      ⟨by
        change P.μ - P.μ / S cap ≤ cap
        have he : lamO P cap d = P.μ - P.μ / S cap := (hformula _ hcap).2
        rw [← he]
        exact (hless _ hcap).le,
       by
        have he : lamO P P.μ d = P.μ - P.μ / S P.μ := (hformula _ hμ).2
        rw [← he]
        exact htop.le⟩)
  have hpos : 0 < lhat := hcap.trans_le hlhat.1
  have heq : lamO P lhat d = cap := (hformula _ hpos).2.trans hval
  refine ⟨lhat, hpos, heq.trans ?_, ?_, ?_, ?_⟩
  · rw [hbranch, min_eq_right hlhat.1]
  · intro lam hlam he
    have hcl : cap < lam := by
      by_contra hn
      rw [hbranch, min_eq_left (le_of_not_gt hn)] at he
      exact (hless _ hlam).ne he
    rw [hbranch, min_eq_right hcl.le] at he
    exact hmono.injOn hlam hpos (he.trans heq.symm)
  · intro lam hlam hlt
    rw [hbranch]
    exact lt_min (hless _ hlam) ((hmono hlam hpos hlt).trans_eq heq)
  · intro lam hlt
    have hlam := hpos.trans hlt
    rw [hbranch, min_eq_right (hlhat.1.trans hlt.le)]
    exact heq.symm.trans_lt (hmono hpos hlam hlt)
