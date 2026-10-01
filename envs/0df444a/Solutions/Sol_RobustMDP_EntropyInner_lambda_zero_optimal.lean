-- Prove2me | solution 1 for RobustMDP.EntropyInner.lambda_zero_optimal
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T12:00:38.022844+00:00
-- url     : https://prove2.me/submissions/3ba69a37-c456-4ba0-a895-418641ee95eb

import Theorems.Thm_RobustMDP_EntropyInner_kl_ball_inner_problem_dual
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import Definitions.Def_RobustMDP_EntropyInner_dualFunction
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic
open RobustMDP.EntropyInner
namespace CEntropy

theorem positive_dim {n : ℕ} (q : Fin n → ℝ) (hq : q∈stdSimplex ℝ (Fin n)) : 0 < n := by
  by_contra h
  have hn : n=0 := by omega
  subst n
  simpa using hq.2

theorem partition_pos {n : ℕ} (q v : Fin n → ℝ) (hq : q∈stdSimplex ℝ (Fin n))
    (hqpos : ∀ j, 0 < q j) (lam : ℝ) : 0 < ∑ j, q j*Real.exp (v j/lam) := by
  haveI : Nonempty (Fin n) := ⟨⟨0,positive_dim q hq⟩⟩
  exact Finset.sum_pos (fun j _ => mul_pos (hqpos j) (Real.exp_pos _)) Finset.univ_nonempty

theorem partition_shift {n : ℕ} (q v : Fin n → ℝ) (lam mu : ℝ) :
    (∑ j, q j*Real.exp ((v j-mu)/lam-1))=
      (∑ j, q j*Real.exp (v j/lam))*Real.exp (-mu/lam-1) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [show (v j-mu)/lam-1=v j/lam+(-mu/lam-1) by ring,Real.exp_add]
  ring
end CEntropy

open Filter Topology Asymptotics
namespace CEntropy

theorem max_mass_pos {n : ℕ} (q v : Fin n → ℝ) (hq : q∈stdSimplex ℝ (Fin n))
    (hqpos : ∀ j, 0 < q j) : 0 < maxMass q v := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0,positive_dim q hq⟩⟩
  obtain ⟨j,hj⟩ := exists_eq_ciSup_of_finite (f := v)
  apply Finset.sum_pos'
  · intro i _
    exact (hqpos i).le
  · exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ j,hj⟩,hqpos j⟩

theorem shifted_limit {n : ℕ} (q v : Fin n → ℝ) (hq : q∈stdSimplex ℝ (Fin n))
    (hqpos : ∀ j, 0 < q j) :
    Tendsto (fun lam => ∑ j, q j*Real.exp ((v j-vmax v)/lam)) (𝓝[>] 0) (𝓝 (maxMass q v)) := by
  classical
  have hterm : ∀ j, Tendsto (fun lam => q j*Real.exp ((v j-vmax v)/lam)) (𝓝[>] 0)
      (𝓝 (if v j=vmax v then q j else 0)) := by
    intro j
    by_cases hj : v j=vmax v
    · simpa [hj] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => q j) (𝓝[>] 0) (𝓝 (q j)))
    have hneg : v j-vmax v < 0 := by
      have hb := le_ciSup (Set.finite_range v).bddAbove j
      change v j ≤ vmax v at hb
      exact sub_neg.mpr (lt_of_le_of_ne hb hj)
    have ht := Real.tendsto_exp_atBot.comp (tendsto_inv_nhdsGT_zero.const_mul_atTop_of_neg hneg)
    simpa [div_eq_mul_inv,hj] using ht.const_mul (q j)
  have hh := tendsto_finset_sum Finset.univ (fun j _ => hterm j)
  simpa only [maxMass,Finset.sum_filter] using hh

theorem shifted_identity {n : ℕ} (q v : Fin n → ℝ) (hq : q∈stdSimplex ℝ (Fin n))
    (hqpos : ∀ j, 0 < q j) (β lam : ℝ) (hlam : 0 < lam) :
    dualFn q v β lam=vmax v+lam*(β+Real.log (∑ j, q j*Real.exp ((v j-vmax v)/lam))) := by
  have hS : 0 < ∑ j, q j*Real.exp ((v j-vmax v)/lam) :=
    partition_pos q (fun j => v j-vmax v) hq hqpos lam
  have hfac : (∑ j, q j*Real.exp (v j/lam))=
      Real.exp (vmax v/lam)*(∑ j, q j*Real.exp ((v j-vmax v)/lam)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [show v j/lam=vmax v/lam+(v j-vmax v)/lam by ring,Real.exp_add]
    ring
  unfold dualFn
  rw [hfac,Real.log_mul (Real.exp_ne_zero _) hS.ne',Real.log_exp]
  field_simp
  <;> ring
end CEntropy

private theorem zero_asymptotic {n : ℕ} (q v : Fin n → ℝ) (β : ℝ)
    (hq : q∈stdSimplex ℝ (Fin n)) (hq_pos : ∀ j, 0 < q j) (hβ : 0 < β) :
    Tendsto (fun lam => dualFn q v β lam) (𝓝[>] 0) (𝓝 (vmax v)) ∧
    (fun lam => dualFn q v β lam-vmax v-(β+Real.log (maxMass q v))*lam)
      =o[𝓝[>] 0] (fun lam : ℝ => lam) := by
  have hQ := CEntropy.max_mass_pos q v hq hq_pos
  have hlog := (Real.continuousAt_log hQ.ne').tendsto.comp (CEntropy.shifted_limit q v hq hq_pos)
  have heq : ∀ᶠ lam : ℝ in 𝓝[>] 0, dualFn q v β lam=vmax v+lam*(β+
      Real.log (∑ j, q j*Real.exp ((v j-vmax v)/lam))) := by
    filter_upwards [self_mem_nhdsWithin] with lam hlam
    exact CEntropy.shifted_identity q v hq hq_pos β lam hlam
  constructor
  · have hh' : Tendsto (fun lam => vmax v+lam*(β+Real.log (∑ j, q j*Real.exp ((v j-vmax v)/lam))))
        (𝓝[>] 0) (𝓝 (vmax v)) := by
      convert! tendsto_const_nhds.add ((show Tendsto (fun lam : ℝ => lam) (𝓝[>] 0) (𝓝 0) from nhdsWithin_le_nhds).mul (hlog.const_add β)) using 1 <;> simp
    exact hh'.congr' (heq.mono (fun _ h => h.symm))
  · apply (isLittleO_iff_tendsto' (by
      filter_upwards [self_mem_nhdsWithin] with lam hlam
      exact fun hz => (ne_of_gt hlam hz).elim)).mpr
    have hh := hlog.sub_const (Real.log (maxMass q v))
    apply Tendsto.congr' _ (by simpa using hh)
    filter_upwards [heq,self_mem_nhdsWithin] with lam he hlam
    rw [he]
    have hl0 : lam ≠ 0 := ne_of_gt hlam
    field_simp [hl0]
    <;> ring

theorem solution {n : ℕ} (q v : Fin n → ℝ) (β : ℝ)
    (hq : q∈stdSimplex ℝ (Fin n)) (hq_pos : ∀ j, 0 < q j) (hβ : 0 < β)
    (hβQ : -Real.log (maxMass q v) ≤ β) :
    IsGLB ((fun lam => dualFn q v β lam) '' Set.Ioi 0) (vmax v) ∧
    IsGreatest ((fun p : Fin n → ℝ => ∑ j, p j*v j) '' klBall q β) (vmax v) := by
  classical
  have hQ := CEntropy.max_mass_pos q v hq hq_pos
  have hS : ∀ lam : ℝ, maxMass q v ≤ ∑ j, q j*Real.exp ((v j-vmax v)/lam) := by
    intro lam
    unfold maxMass
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro j _
    split_ifs with hj
    · simp [hj]
    · exact mul_nonneg (hq_pos j).le (Real.exp_pos _).le
  have hlower : ∀ lam : ℝ, 0 < lam → vmax v ≤ dualFn q v β lam := by
    intro lam hlam
    rw [CEntropy.shifted_identity q v hq hq_pos β lam hlam]
    have hh := Real.log_le_log hQ (hS lam)
    have hlog : 0 ≤ β+Real.log (∑ j, q j*Real.exp ((v j-vmax v)/lam)) := by linarith
    exact le_add_of_nonneg_right (mul_nonneg hlam.le hlog)
  obtain ⟨s,hgreat,hglb⟩ := kl_ball_inner_problem_dual q v β hq hq_pos hβ
  have hms : vmax v ≤ s := hglb.2 (by
    rintro z ⟨lam,hlam,rfl⟩
    exact hlower lam hlam)
  have hsm : s ≤ vmax v := by
    apply ge_of_tendsto (zero_asymptotic q v β hq hq_pos hβ).1
    filter_upwards [self_mem_nhdsWithin] with lam hlam
    exact hglb.1 ⟨lam,hlam,rfl⟩
  have heq : s=vmax v := le_antisymm hsm hms
  exact heq ▸ ⟨hglb,hgreat⟩

