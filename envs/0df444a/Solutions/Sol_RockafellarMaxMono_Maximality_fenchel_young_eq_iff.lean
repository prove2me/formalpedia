-- Prove2me | solution 1 for RockafellarMaxMono.Maximality.fenchel_young_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:28:30.887444+00:00
-- url     : https://prove2.me/submissions/53ba768c-5856-4743-ad96-316111382bf1

import Definitions.Def_RockafellarMaxMono_Shared_ProperConvex
import Definitions.Def_RockafellarMaxMono_Shared_Subdiff
import Definitions.Def_RockafellarMaxMono_Shared_Conj
import Mathlib.Tactic
open RockafellarMaxMono.Shared

private theorem ereal_shift (a b : ℝ) (z : EReal) :
    (a : EReal)+z=(b : EReal) ↔ z=((b-a : ℝ) : EReal) := by
  cases z using EReal.rec <;> simp [← EReal.coe_add,← EReal.coe_sub]
  constructor <;> intro h <;> linarith

private theorem ereal_shift_le (a b c : ℝ) (z : EReal) :
    (a : EReal)+((b-c : ℝ) : EReal) ≤ z ↔ (b : EReal)-z ≤ ((c-a : ℝ) : EReal) := by
  cases z using EReal.rec <;> simp [← EReal.coe_add,← EReal.coe_sub]
  constructor <;> intro h <;> linarith

theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] (f : V → EReal) (hf : ProperConvex f) (hlsc : LowerSemicontinuous f) :
    ∀ (x : V) (x' : StrongDual ℝ V),
      ((x' x : ℝ) : EReal) ≤ f x + conj f x' ∧
        (f x + conj f x' = ((x' x : ℝ) : EReal) ↔ x' ∈ subdiff f x) := by
  intro x x'
  obtain ⟨y,hy⟩ := hf.2.1
  have hyc : ((f y).toReal : EReal)=f y := EReal.coe_toReal hy (hf.1 y)
  have hc : conj f x' ≠ ⊥ := by
    have hh : ((x' y-(f y).toReal : ℝ) : EReal) ≤ conj f x' := by
      rw [EReal.coe_sub,hyc]
      exact le_iSup (fun z => (x' z : EReal)-f z) y
    exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hh
  by_cases hx : f x=⊤
  · have hs : x' ∉ subdiff f x := by
      intro hh
      have hh' := hh y
      rw [hx,EReal.top_add_coe] at hh'
      exact hy (top_le_iff.mp hh')
    simp [hx,EReal.top_add_of_ne_bot hc,hs]
  · let a := (f x).toReal
    have ha : (a : EReal)=f x := EReal.coe_toReal hx (hf.1 x)
    have hlow : ((x' x-a : ℝ) : EReal) ≤ conj f x' := by
      rw [EReal.coe_sub,ha]
      exact le_iSup (fun z => (x' z : EReal)-f z) x
    have hsub : x' ∈ subdiff f x ↔ conj f x' ≤ ((x' x-a : ℝ) : EReal) := by
      simp only [subdiff,Set.mem_setOf_eq,conj,iSup_le_iff,← ha,map_sub]
      exact forall_congr' (fun z => ereal_shift_le a (x' z) (x' x) (f z))
    rw [← ha]
    refine ⟨?_,?_⟩
    · have hh := (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot a))
        (Or.inl (EReal.coe_ne_top a))).mp (by simpa only [EReal.coe_sub] using hlow)
      simpa only [add_comm] using hh
    · rw [ereal_shift,hsub]
      exact ⟨fun h => h.le,fun h => le_antisymm h hlow⟩

