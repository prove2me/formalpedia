-- Prove2me | solution 1 for Rudin.ch08_trig_approximation
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T20:03:10.144184+00:00
-- url     : https://prove2.me/submissions/0429ce88-23c5-480b-966e-b1199a5c40d0

import Mathlib
import Definitions.Def_Rudin_ch08_fourier
set_option autoImplicit false
open Filter Topology Rudin
theorem solution (f : ℝ → ℂ) (hcont : Continuous f) (hper : HasPeriodTwoPi f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ P : ℝ → ℂ, IsTrigPolynomial P ∧ ∀ x : ℝ, ‖P x - f x‖ < ε := by
  classical
  let T : ℝ := 2 * Real.pi
  letI : Fact (0 < T) := ⟨mul_pos (by norm_num) Real.pi_pos⟩
  have hp : Function.Periodic f T := hper
  let F : C(AddCircle T, ℂ) := ⟨hp.lift, continuous_coinduced_dom.mpr hcont⟩
  have hcl : F ∈ closure ((Submodule.span ℂ (Set.range (@fourier T))) :
      Set C(AddCircle T, ℂ)) := by
    rw [← Submodule.topologicalClosure_coe, span_fourier_closure_eq_top]
    trivial
  obtain ⟨q, hq, hnear⟩ := Metric.mem_closure_iff.mp hcl ε hε
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hq
  let N : ℕ := c.support.sup Int.natAbs
  have hsupport : c.support ⊆ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro n hn
    have habs : n.natAbs ≤ N := Finset.le_sup (f := Int.natAbs) hn
    have hcast : (n.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast habs
    have hpos := Int.le_natAbs (a := n)
    have hneg : -n ≤ (n.natAbs : ℤ) := by simpa using Int.le_natAbs (a := -n)
    exact Finset.mem_Icc.mpr ⟨by omega, hpos.trans hcast⟩
  have hfourier (n : ℤ) (x : ℝ) : fourier n (x : AddCircle T) =
      Complex.exp ((n : ℂ) * Complex.I * (x : ℂ)) := by
    rw [fourier_coe_apply]
    congr 1
    dsimp [T]
    push_cast
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
    <;> ring
  let Q : C(AddCircle T, ℂ) := c.sum (fun n a => a • fourier n)
  refine ⟨fun x => Q (x : AddCircle T), ⟨N, (c : ℤ → ℂ), ?_⟩, ?_⟩
  · intro x
    change (c.sum (fun n a => a • fourier n)) (x : AddCircle T) = _
    simp only [Finsupp.sum, ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul,
      hfourier]
    exact Finset.sum_subset hsupport (fun n hn hnot => by
      rw [Finsupp.notMem_support_iff.mp hnot, zero_mul])
  · intro x
    have hn : ‖Q - F‖ < ε := by simpa [Q, dist_eq_norm, norm_sub_rev] using hnear
    have hh := (ContinuousMap.norm_coe_le_norm (Q - F) (x : AddCircle T)).trans_lt hn
    simpa [F, Function.Periodic.lift_coe] using hh
#print axioms solution
