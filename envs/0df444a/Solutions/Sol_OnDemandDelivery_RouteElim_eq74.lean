-- Prove2me | solution 1 for OnDemandDelivery.RouteElim.eq74
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-19T04:41:10.027489+00:00
-- url     : https://prove2.me/submissions/063903b8-bc34-4c70-98b7-025a79d1866f

import Mathlib
import Definitions.Def_OnDemandDelivery_RouteElim_Setting

open Finset OnDemandDelivery.RouteElim
set_option maxHeartbeats 1000000

lemma route_remove {R I P : Type} [Fintype R] [Fintype I] [Fintype P]
    (D : Data R I P) (hD : D.Standing) (r : R) (θ : R → ℝ)
    (hθ : D.SF1Feasible θ) (hr : θ r = 1) :
    ∃ θ', D.SF1rFeasible r θ' ∧ D.cost θ' = D.cost θ - D.c r := by
  classical
  let θ' : R → ℝ := fun s => if s = r then 0 else θ s
  have hbin : ∀ s, θ' s = 0 ∨ θ' s = 1 := by
    intro s
    by_cases hs : s = r
    · simp [θ', hs]
    · simpa [θ', hs] using hθ.2.2.2 s
  have hn : ∀ s, 0 ≤ θ' s := by
    intro s
    rcases hbin s with h | h <;> simp [h]
  have hsum (f : R → ℝ) : (∑ s, f s * θ' s) = (∑ s, f s * θ s) - f r := by
    calc
      _ = ∑ s, (f s * θ s - if s = r then f r else 0) := by
        apply sum_congr rfl
        intro s _
        by_cases hs : s = r
        · simp [θ', hs, hr]
        · simp [θ', hs]
      _ = _ := by rw [sum_sub_distrib]; simp
  have hsupport : ∀ s, ¬ D.InRr r s → θ' s = 0 := by
    intro s hns
    by_contra hne
    have hs1 : θ' s = 1 := (hbin s).resolve_left hne
    obtain ⟨i, hi⟩ := not_forall.mp hns
    have hi' : D.α i s ≠ 0 ∧ D.α i r ≠ 0 := by simpa only [_root_.not_imp] using hi
    have has : D.α i s = 1 := (hD.1 i s).resolve_left hi'.1
    have har : D.α i r = 1 := (hD.1 i r).resolve_left hi'.2
    have hz : (∑ t, D.α i t * θ' t) = 0 := by rw [hsum, hθ.2.2.1 i, har]; norm_num
    have ht : D.α i s * θ' s ≤ ∑ t, D.α i t * θ' t := by
      apply Finset.single_le_sum (s := univ) (f := fun t => D.α i t * θ' t)
      · intro t _
        have hα : 0 ≤ D.α i t := by rcases hD.1 i t with h | h <;> simp [h]
        exact mul_nonneg hα (hn t)
      · exact mem_univ _
    rw [hz, has, hs1] at ht
    norm_num at ht
  refine ⟨θ', ⟨hsupport, ?_, ?_, ?_, hbin⟩, ?_⟩
  · intro p
    rw [hsum]
    exact sub_le_sub_right (hθ.1 p) _
  · have hh := hsum (fun _ => 1)
    simp only [one_mul] at hh
    rw [hh]
    linarith [hθ.2.1]
  · intro i hi
    rw [hsum, hθ.2.2.1 i, hi, sub_zero]
  · simpa only [Data.cost, mul_comm] using hsum D.c

lemma route_eq74 {R I P : Type} [Fintype R] [Fintype I] [Fintype P]
    (D : Data R I P) (hD : D.Standing)
    (ub : ℝ) (hub : ∀ θ, D.SF1Optimal θ → D.cost θ ≤ ub)
    (r : R) (h74 : (ub : EReal) < (D.c r : EReal) + D.phiSF1r r) :
    ∀ θ, D.SF1Optimal θ → θ r = 0 := by
  intro θ hθ
  rcases hθ.1.2.2.2 r with hr | hr
  · exact hr
  obtain ⟨θ', hf, hc⟩ := route_remove D hD r θ hθ.1 hr
  have hphi : D.phiSF1r r ≤ (D.cost θ' : EReal) := sInf_le ⟨θ', hf, rfl⟩
  have hlt := h74.trans_le (add_le_add le_rfl hphi)
  have heq : (D.c r : EReal) + (D.cost θ' : EReal) = (D.cost θ : EReal) := by
    rw [← EReal.coe_add]
    congr 1
    linarith
  rw [heq] at hlt
  have hle : (D.cost θ : EReal) ≤ (ub : EReal) := by exact_mod_cast hub θ hθ
  exact False.elim ((not_lt_of_ge hle) hlt)

theorem solution {R I P : Type} [Fintype R] [Fintype I] [Fintype P]
    (D : Data R I P) (hD : D.Standing)
    (ub : ℝ) (hub : ∀ θ, D.SF1Optimal θ → D.cost θ ≤ ub)
    (r : R) (h74 : (ub : EReal) < (D.c r : EReal) + D.phiSF1r r) :
    ∀ θ, D.SF1Optimal θ → θ r = 0 := by
  exact route_eq74 D hD ub hub r h74
