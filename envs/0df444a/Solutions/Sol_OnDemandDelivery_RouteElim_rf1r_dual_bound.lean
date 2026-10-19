-- Prove2me | solution 1 for OnDemandDelivery.RouteElim.rf1r_dual_bound
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-19T04:41:11.614081+00:00
-- url     : https://prove2.me/submissions/de556b81-7a6d-4577-b113-bd8ccc98de70

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

lemma route_restrict_dual {R I P : Type} [Fintype R] [Fintype I] [Fintype P]
    (D : Data R I P) (μ : P → ℝ) (μn : ℝ) (ν : I → ℝ)
    (hdual : D.DualFeasible μ μn ν) (r : R) : D.RF1rDualFeasible r μ μn ν := by
  classical
  refine ⟨hdual.1, hdual.2.1, ?_⟩
  intro s hs
  have heq : (∑ i ∈ univ.filter (fun i => D.α i r = 0), D.α i s * ν i) = ∑ i, D.α i s * ν i := by
    rw [sum_filter]
    apply sum_congr rfl
    intro i _
    by_cases hi : D.α i r = 0
    · simp [hi]
    · have hiz : D.α i s = 0 := by by_contra h; exact hi (hs i h)
      simp [hi, hiz]
  rw [heq]
  exact hdual.2.2.2 s

lemma route_sum_identity {R I P : Type} [Fintype R] [Fintype I] [Fintype P]
    (D : Data R I P) (S : Finset I) (μ : P → ℝ) (μn : ℝ) (ν : I → ℝ) (θ : R → ℝ) :
    (∑ s, θ s * ((∑ i ∈ S, D.α i s * ν i) + (∑ p, D.β p s * μ p) + μn)) =
      (∑ i ∈ S, ν i * (∑ s, D.α i s * θ s)) +
      (∑ p, μ p * (∑ s, D.β p s * θ s)) + μn * ∑ s, θ s := by
  simp_rw [mul_add, sum_add_distrib]
  congr 1
  · congr 1
    · simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro s _
      ring
    · simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro p _
      apply sum_congr rfl
      intro s _
      ring
  · rw [mul_sum]
    apply sum_congr rfl
    intro s _
    ring

lemma route_restricted_weak {R I P : Type} [Fintype R] [Fintype I] [Fintype P]
    (D : Data R I P) (r : R) (μ : P → ℝ) (μn : ℝ) (ν : I → ℝ)
    (hd : D.RF1rDualFeasible r μ μn ν) (θ : R → ℝ) (hθ : D.RF1rFeasible r θ) :
    D.rf1rBound r μ μn ν ≤ D.cost θ := by
  classical
  let S := univ.filter (fun i => D.α i r = 0)
  have hcost : (∑ s, θ s * ((∑ i ∈ S, D.α i s * ν i) + (∑ p, D.β p s * μ p) + μn)) ≤ D.cost θ := by
    apply sum_le_sum
    intro s _
    by_cases hs : D.InRr r s
    · exact mul_le_mul_of_nonneg_left (hd.2.2 s hs) (hθ.2.2.2.2 s)
    · simp [hθ.1 s hs]
  rw [route_sum_identity] at hcost
  have hcov : (∑ i ∈ S, ν i * (∑ s, D.α i s * θ s)) = ∑ i ∈ S, ν i := by
    apply sum_congr rfl
    intro i hi
    rw [hθ.2.2.2.1 i (mem_filter.mp hi).2, mul_one]
  rw [hcov] at hcost
  have hp : (∑ p, μ p * (D.b p - D.β p r)) ≤ ∑ p, μ p * (∑ s, D.β p s * θ s) := by
    apply sum_le_sum
    intro p _
    exact mul_le_mul_of_nonpos_left (hθ.2.1 p) (hd.1 p)
  have hn := mul_le_mul_of_nonpos_left hθ.2.2.1 hd.2.1
  have hid : (∑ p, μ p * (D.b p - D.β p r)) = (∑ p, μ p * D.b p) - ∑ p, D.β p r * μ p := by
    simp_rw [mul_sub]
    rw [sum_sub_distrib]
    congr 1
    apply sum_congr rfl
    intro p _
    ring
  rw [hid] at hp
  dsimp [Data.rf1rBound]
  dsimp [S] at hcost
  linarith

lemma route_dual_bound {R I P : Type} [Fintype R] [Fintype I] [Fintype P]
    (D : Data R I P) (hD : D.Standing)
    (μ : P → ℝ) (μn : ℝ) (ν : I → ℝ) (hdual : D.DualFeasible μ μn ν) (r : R) :
    D.RF1rDualFeasible r μ μn ν ∧
      (∀ θ', D.RF1rFeasible r θ' → D.rf1rBound r μ μn ν ≤ D.cost θ') ∧
      ((D.rf1rBound r μ μn ν : ℝ) : EReal) ≤ D.phiSF1r r := by
  have hd := route_restrict_dual D μ μn ν hdual r
  refine ⟨hd, route_restricted_weak D r μ μn ν hd, ?_⟩
  apply le_sInf
  rintro v ⟨θ, hθ, rfl⟩
  have hf : D.RF1rFeasible r θ := by
    refine ⟨hθ.1, hθ.2.1, hθ.2.2.1, hθ.2.2.2.1, ?_⟩
    intro s
    rcases hθ.2.2.2.2 s with h | h <;> simp [h]
  change (D.rf1rBound r μ μn ν : EReal) ≤ (D.cost θ : EReal)
  exact_mod_cast route_restricted_weak D r μ μn ν hd θ hf

theorem solution {R I P : Type} [Fintype R] [Fintype I] [Fintype P]
    (D : Data R I P) (hD : D.Standing)
    (μ : P → ℝ) (μn : ℝ) (ν : I → ℝ) (hdual : D.DualFeasible μ μn ν) (r : R) :
    D.RF1rDualFeasible r μ μn ν ∧
      (∀ θ', D.RF1rFeasible r θ' → D.rf1rBound r μ μn ν ≤ D.cost θ') ∧
      ((D.rf1rBound r μ μn ν : ℝ) : EReal) ≤ D.phiSF1r r := by
  exact route_dual_bound D hD μ μn ν hdual r
