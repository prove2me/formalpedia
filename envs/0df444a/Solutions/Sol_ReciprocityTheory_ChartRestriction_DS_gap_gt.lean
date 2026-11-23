-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.gap_gt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:53:02.175651+00:00
-- url     : https://prove2.me/submissions/912aeac3-fc4c-455b-8ac8-bdafe326e315

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NumRho
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Numerics
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
section Num
variable {ε : Fin n → Bool}
private theorem pq_facts {a b : Fin n} (hε : ε a ≠ ε b) :
    1 ≤ (pOf ε : ℝ) ∧ 1 ≤ (qOf ε : ℝ) ∧ (pOf ε : ℝ) + (qOf ε : ℝ) = n := by
  have hsum : pOf ε + qOf ε = n := by
    unfold pOf qOf
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
      (fun a => ε a = true)
    simpa using this
  have hp : ∃ c, ε c = true := by
    cases ha : ε a
    · exact ⟨b, by cases hb : ε b <;> simp_all⟩
    · exact ⟨a, ha⟩
  have hq : ∃ c, ε c = false := by
    cases ha : ε a
    · exact ⟨a, ha⟩
    · exact ⟨b, by cases hb : ε b <;> simp_all⟩
  obtain ⟨c, hc⟩ := hp
  obtain ⟨d, hd⟩ := hq
  have h1 : 1 ≤ pOf ε := Finset.card_pos.mpr ⟨c, by simp [hc]⟩
  have h2 : 1 ≤ qOf ε := Finset.card_pos.mpr ⟨d, by simp [hd]⟩
  refine ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast hsum⟩
end Num
end ReciprocityTheory.ChartRestriction.DS
end
end

set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {ε : Fin n → Bool}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {a b : Fin n} (hε : ε a ≠ ε b) {h : ℝ}
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) :
    2 * (n : ℝ) - 3 < h ∧ (n : ℝ) - 1 < h := by
  obtain ⟨hp, hq, hn⟩ := pq_facts hε
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hm := mul_nonneg (sub_nonneg.2 hp) (sub_nonneg.2 hq)
  have key : (n : ℝ) * ((n : ℝ) - 1) ≤ (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) := by
    nlinarith [mul_nonneg hn0 hm]
  constructor
  · nlinarith [sq_nonneg ((n : ℝ) - 2)]
  · nlinarith [sq_nonneg ((n : ℝ) - 1)]
end ReciprocityTheory.ChartRestriction.DS
