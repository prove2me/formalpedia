-- Prove2me | solution 1 for PersistClust.Count.mult_finite_at_bars
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-14T09:44:38.464143+00:00
-- url     : https://prove2.me/submissions/2c98c31a-3e09-454f-9d20-801ed3f21554

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

theorem t2_qtame {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) (s t : ℝ) :
    rankFn stage J s t ≠ ⊤ := by
  obtain ⟨hcomp, -, -⟩ := hTame
  have hsub : ((fun x => {y | J t x y}) '' stage s) ⊆
      insert (∅ : Set ι) ((fun x => {y | J t x y}) '' stage t) := by
    rintro S ⟨x, hx, rfl⟩
    by_cases hxt : x ∈ stage t
    · exact Or.inr ⟨x, hxt, rfl⟩
    · exact Or.inl (Set.eq_empty_iff_forall_notMem.mpr
        (fun y hy => absurd (hLaw.mem hy).1 hxt))
  have hfin : ((fun x => {y | J t x y}) '' stage s).Finite :=
    Set.Finite.subset (Set.Finite.insert ∅ (hcomp t)) hsub
  unfold rankFn
  exact ne_of_lt (Set.Finite.encard_lt_top hfin)

theorem solution {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) (p : EReal × EReal)
    (hp : p.2 = ⊥ ∨ p.2 < p.1) : mult (rankFn stage J) p ≠ ⊤ := by
  have hexcl : ∀ x y : ℕ∞, x ≤ y → y ≠ ⊤ → x ≠ ⊤ := by
    intro x y hle hy htop
    rw [htop] at hle
    exact hy (top_le_iff.mp hle)
  by_cases h1 : p.1 ≠ ⊥ ∧ p.1 ≠ ⊤
  · by_cases h2 : p.2 = ⊥
    · rw [mult, if_pos h1, if_pos h2]
      refine hexcl _ _ ?_ (t2_qtame hLaw hTame (p.1.toReal - 1) (p.1.toReal - 1))
      calc (⨅ (ε : ℝ) (_ : 0 < ε), ⨅ (t : ℝ) (_ : t ≤ p.1.toReal - ε),
            rankFn stage J (p.1.toReal - ε) t - rankFn stage J (p.1.toReal + ε) t)
          ≤ ⨅ (t : ℝ) (_ : t ≤ p.1.toReal - 1),
            rankFn stage J (p.1.toReal - 1) t - rankFn stage J (p.1.toReal + 1) t :=
            iInf₂_le (1 : ℝ) one_pos
        _ ≤ rankFn stage J (p.1.toReal - 1) (p.1.toReal - 1)
              - rankFn stage J (p.1.toReal + 1) (p.1.toReal - 1) :=
            iInf₂_le (p.1.toReal - 1) (by exact le_refl _)
        _ ≤ rankFn stage J (p.1.toReal - 1) (p.1.toReal - 1) := tsub_le_self
    · have h3' : p.2 < p.1 := hp.resolve_left h2
      have h2top : p.2 ≠ ⊤ := by
        intro h
        rw [h] at h3'
        exact absurd (h3'.trans_le le_top) (lt_irrefl ⊤)
      have hdbd : p.2.toReal < p.1.toReal := by
        have hd : p.2 = (p.2.toReal : EReal) := (EReal.coe_toReal h2top h2).symm
        have hb : p.1 = (p.1.toReal : EReal) := (EReal.coe_toReal h1.2 h1.1).symm
        exact EReal.coe_lt_coe_iff.mp (by rw [← hd, ← hb]; exact h3')
      rw [mult, if_pos h1, if_neg h2, if_pos h3']
      refine hexcl _ _ ?_ (t2_qtame hLaw hTame
        (p.1.toReal - (p.1.toReal - p.2.toReal) / 4)
        (p.2.toReal + (p.1.toReal - p.2.toReal) / 4))
      calc (⨅ (ε : ℝ) (_ : ε ∈ Set.Ioo (0 : ℝ) ((p.1.toReal - p.2.toReal) / 2)),
            ((rankFn stage J (p.1.toReal - ε) (p.2.toReal + ε)
                - rankFn stage J (p.1.toReal + ε) (p.2.toReal + ε))
              - (rankFn stage J (p.1.toReal - ε) (p.2.toReal - ε)
                - rankFn stage J (p.1.toReal + ε) (p.2.toReal - ε))))
          ≤ ((rankFn stage J (p.1.toReal - (p.1.toReal - p.2.toReal) / 4)
                  (p.2.toReal + (p.1.toReal - p.2.toReal) / 4)
                - rankFn stage J (p.1.toReal + (p.1.toReal - p.2.toReal) / 4)
                  (p.2.toReal + (p.1.toReal - p.2.toReal) / 4))
              - (rankFn stage J (p.1.toReal - (p.1.toReal - p.2.toReal) / 4)
                  (p.2.toReal - (p.1.toReal - p.2.toReal) / 4)
                - rankFn stage J (p.1.toReal + (p.1.toReal - p.2.toReal) / 4)
                  (p.2.toReal - (p.1.toReal - p.2.toReal) / 4))) :=
            iInf₂_le ((p.1.toReal - p.2.toReal) / 4) ⟨by linarith, by linarith⟩
        _ ≤ rankFn stage J (p.1.toReal - (p.1.toReal - p.2.toReal) / 4)
              (p.2.toReal + (p.1.toReal - p.2.toReal) / 4) :=
            tsub_le_self.trans tsub_le_self
  · rw [mult, if_neg h1]
    exact ENat.coe_ne_top 0
