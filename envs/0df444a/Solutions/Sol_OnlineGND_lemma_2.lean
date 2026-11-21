-- Prove2me | solution 1 for OnlineGND.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T20:57:22.522044+00:00
-- url     : https://prove2.me/submissions/54a77db2-01f8-444a-8e45-eca6e85b49d6

import Definitions.Def_OnlineGND_Relaxation

namespace Aux_OnlineGND_lemma_2

open OnlineGND

theorem fracLoad_nonneg {E : Type*} [Fintype E] [DecidableEq E] {N : ℕ}
    (reqs : Fin N → Request E) (hw : ∀ i e, 0 ≤ (reqs i).w e) (x : Fin N → Finset E → ℝ)
    (hx : IsPrimalFeasible reqs x) (e : E) : 0 ≤ fracLoad reqs x e := by
  unfold fracLoad
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (hw i e)
  apply Finset.sum_nonneg
  intro p hp
  exact hx.1 i p (Finset.mem_filter.mp hp).1

theorem edge_bound (c α z l : ℝ) (hc : 0 ≤ c) (hα : 1 ≤ α) (hz : 0 ≤ z) (hl : 0 ≤ l)
    (hz1 : α = 1 → z ≤ 1) :
    c * α * z * l ≤ c * l ^ α + (if α ≠ 1 then c * α / (α / (α - 1)) * z ^ (α / (α - 1)) else 0) := by
  by_cases h1 : α = 1
  · have hz' := hz1 h1
    rw [if_neg (not_not.mpr h1), h1, Real.rpow_one, add_zero]
    nlinarith [mul_nonneg (mul_nonneg hc hl) (sub_nonneg.mpr hz')]
  · have hlt : 1 < α := lt_of_le_of_ne hα (Ne.symm h1)
    have hα0 : α ≠ 0 := by linarith
    rw [if_pos (show α ≠ 1 from h1)]
    have hpq : (α / (α - 1)).HolderConjugate α :=
      ((Real.holderConjugate_iff_eq_conjExponent hlt).2 rfl).symm
    have Y := Real.young_inequality_of_nonneg hz hl hpq
    have hca : 0 ≤ c * α := mul_nonneg hc (by linarith)
    calc c * α * z * l = (c * α) * (z * l) := by ring
      _ ≤ (c * α) * (z ^ (α / (α - 1)) / (α / (α - 1)) + l ^ α / α) :=
          mul_le_mul_of_nonneg_left Y hca
      _ = c * l ^ α * (α * α⁻¹) + c * α / (α / (α - 1)) * z ^ (α / (α - 1)) := by ring
      _ = c * l ^ α + c * α / (α / (α - 1)) * z ^ (α / (α - 1)) := by
          rw [mul_inv_cancel₀ hα0, mul_one]

end Aux_OnlineGND_lemma_2

open OnlineGND in
theorem solution {E : Type*} [Fintype E] [DecidableEq E] {N : ℕ} (c α : E → ℝ)
    (hc : ∀ e, 0 ≤ c e) (hα : ∀ e, 1 ≤ α e) (reqs : Fin N → Request E)
    (hw : ∀ i e, 0 ≤ (reqs i).w e) (x : Fin N → Finset E → ℝ) (hx : IsPrimalFeasible reqs x)
    (y : Fin N → ℝ) (z : E → ℝ) (hyz : IsDualFeasible c α reqs y z) :
    dualObj c α y z ≤ primalObj c α reqs x := by
  -- Step A: sum of y bounded by the "linearised" cost
  have hkey : ∀ i, (∑ p ∈ (reqs i).replies, x i p * ∑ e ∈ p, (reqs i).w e * c e * α e * z e) =
      ∑ e, ∑ p ∈ (reqs i).replies,
        (if e ∈ p then x i p * ((reqs i).w e * c e * α e * z e) else 0) := by
    intro i
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
  have hRHS : ∀ e, c e * α e * z e * fracLoad reqs x e =
      ∑ i, ∑ p ∈ (reqs i).replies,
        (if e ∈ p then x i p * ((reqs i).w e * c e * α e * z e) else 0) := by
    intro e
    unfold fracLoad
    simp_rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> ring
  have hA : ∑ i, y i ≤ ∑ e, c e * α e * z e * fracLoad reqs x e := by
    calc ∑ i, y i
        ≤ ∑ i, ∑ p ∈ (reqs i).replies, x i p * ∑ e ∈ p, (reqs i).w e * c e * α e * z e := by
          apply Finset.sum_le_sum
          intro i _
          have hS := hx.2 i
          have hy := hyz.2.2.1 i
          calc y i ≤ y i * ∑ p ∈ (reqs i).replies, x i p := le_mul_of_one_le_right hy hS
            _ = ∑ p ∈ (reqs i).replies, y i * x i p := by rw [Finset.mul_sum]
            _ ≤ ∑ p ∈ (reqs i).replies, x i p * ∑ e ∈ p, (reqs i).w e * c e * α e * z e := by
                apply Finset.sum_le_sum
                intro p hp
                rw [mul_comm]
                exact mul_le_mul_of_nonneg_left (hyz.1 i p hp) (hx.1 i p hp)
      _ = ∑ i, ∑ e, ∑ p ∈ (reqs i).replies,
            (if e ∈ p then x i p * ((reqs i).w e * c e * α e * z e) else 0) :=
          Finset.sum_congr rfl (fun i _ => hkey i)
      _ = ∑ e, ∑ i, ∑ p ∈ (reqs i).replies,
            (if e ∈ p then x i p * ((reqs i).w e * c e * α e * z e) else 0) := Finset.sum_comm
      _ = ∑ e, c e * α e * z e * fracLoad reqs x e :=
          Finset.sum_congr rfl (fun e _ => (hRHS e).symm)
  -- Step B: per-edge Young inequality
  have hB : ∑ e, c e * α e * z e * fracLoad reqs x e ≤
      ∑ e, (c e * fracLoad reqs x e ^ α e +
        (if α e ≠ 1 then c e * α e / conjExp α e * z e ^ conjExp α e else 0)) := by
    apply Finset.sum_le_sum
    intro e _
    unfold conjExp
    exact Aux_OnlineGND_lemma_2.edge_bound (c e) (α e) (z e) (fracLoad reqs x e) (hc e) (hα e)
      (hyz.2.2.2 e) (Aux_OnlineGND_lemma_2.fracLoad_nonneg reqs hw x hx e) (hyz.2.1 e)
  rw [Finset.sum_add_distrib] at hB
  unfold dualObj primalObj
  rw [Finset.sum_filter]
  linarith
