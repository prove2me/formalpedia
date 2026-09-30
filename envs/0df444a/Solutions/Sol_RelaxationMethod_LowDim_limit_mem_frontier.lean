-- Prove2me | solution 1 for RelaxationMethod.LowDim.limit_mem_frontier
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:35:14.425047+00:00
-- url     : https://prove2.me/submissions/5c11b85e-a346-4694-a25e-077a99a38940

import Definitions.Def_RelaxationMethod_LowDim_RelaxStep
import Definitions.Def_RelaxationMethod_FullDim_RelaxStep
import Definitions.Def_RelaxationMethod_FullDim_FejerMonotone
import Mathlib.Tactic
set_option autoImplicit false
open RelaxationMethod.FullDim Filter
open scoped Topology

private theorem half_closed {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) (b : ℝ) : IsClosed (halfSpace u b) :=
  isClosed_le continuous_const ((continuous_const.inner continuous_id).add continuous_const)

private theorem limit_feasible {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (hA : (polytope a b).Nonempty) (lam : ℝ) (hlam0 : 0 < lam)
    (p : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsRelaxRun a b lam p)
    (hinf : ∀ ν : ℕ, p ν ∉ polytope a b) (l : EuclideanSpace ℝ (Fin n))
    (hl : Tendsto p atTop (𝓝 l)) : l ∈ polytope a b ∧ l ∈ frontier (polytope a b) := by
  have hlA : l ∈ polytope a b := by
    apply Set.mem_iInter.mpr
    intro i
    have hs (ν : ℕ) : lam * Metric.infDist (p ν) (halfSpace (a i) (b i)) ≤ dist (p ν) (p (ν+1)) := by
      obtain ⟨j,hfar,q,hq,hpq,hnext⟩ := hrun ν (hinf ν)
      rw [hnext]
      have he : dist (p ν) (p ν+lam • (q-p ν)) = lam*dist (p ν) q := by
        have hv : p ν-(p ν+lam • (q-p ν)) = lam • (p ν-q) := by module
        simp only [dist_eq_norm]
        rw [hv,norm_smul,Real.norm_eq_abs,abs_of_pos hlam0]
      rw [he,hpq]
      exact mul_le_mul_of_nonneg_left (hfar i) hlam0.le
    have hshift : Tendsto (fun ν : ℕ => p (ν+1)) atTop (𝓝 l) := hl.comp (tendsto_add_atTop_nat 1)
    have hstep : Tendsto (fun ν => dist (p ν) (p (ν+1))) atTop (𝓝 0) := by simpa using hl.dist hshift
    have hdist : Tendsto (fun ν => lam * Metric.infDist (p ν) (halfSpace (a i) (b i))) atTop
        (𝓝 (lam * Metric.infDist l (halfSpace (a i) (b i)))) :=
      tendsto_const_nhds.mul ((Metric.continuous_infDist_pt _).tendsto l |>.comp hl)
    have hle := le_of_tendsto_of_tendsto hdist hstep (Filter.Eventually.of_forall hs)
    have hne : (halfSpace (a i) (b i)).Nonempty := by
      obtain ⟨x,hx⟩ := hA
      exact ⟨x,Set.mem_iInter.mp hx i⟩
    by_contra hnot
    have hpos := (half_closed (a i) (b i)).notMem_iff_infDist_pos hne |>.mp hnot
    have hmul := mul_pos hlam0 hpos
    linarith
  refine ⟨hlA,?_⟩
  rw [frontier_eq_closure_inter_closure]
  refine ⟨subset_closure hlA,?_⟩
  exact isClosed_closure.mem_of_tendsto hl (Filter.Eventually.of_forall (fun ν => subset_closure (hinf ν)))

theorem solution {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (hA : (RelaxationMethod.LowDim.polytope a b).Nonempty) (lam : ℝ) (hlam0 : 0 < lam) (hlam2 : lam ≤ 2)
    (p : ℕ → EuclideanSpace ℝ (Fin n))
    (hrun : ∀ ν, p ν ∉ RelaxationMethod.LowDim.polytope a b → RelaxationMethod.LowDim.IsRelaxStep a b lam (p ν) (p (ν + 1)))
    (hinf : ∀ ν, p ν ∉ RelaxationMethod.LowDim.polytope a b) (l : EuclideanSpace ℝ (Fin n))
    (hl : Tendsto p atTop (𝓝 l)) :
    l ∈ RelaxationMethod.LowDim.polytope a b ∧ l ∈ frontier (RelaxationMethod.LowDim.polytope a b) :=
  limit_feasible a b hA lam hlam0 p hrun hinf l hl
