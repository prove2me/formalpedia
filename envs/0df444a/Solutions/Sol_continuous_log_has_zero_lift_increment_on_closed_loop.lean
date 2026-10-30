-- Prove2me | solution 1 for continuous_log_has_zero_lift_increment_on_closed_loop
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T02:14:34.525644+00:00
-- url     : https://prove2.me/submissions/683102bd-acca-470e-8260-67f312d53462

import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Separation.Lemmas
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

open Set

lemma complex_exp_one_fiber_countable : {z : ℂ | Complex.exp z = 1}.Countable := by
  apply (Set.countable_range (fun n : ℤ => (n : ℂ) * (2 * Real.pi * Complex.I))).mono
  intro z hz
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hz
  exact ⟨n, hn.symm⟩

lemma exp_lifts_diff_constant_on_preconnected {X : Type} [TopologicalSpace X]
    (W : Set X) (f g : X → ℂ) (hW : IsPreconnected W)
    (hf : ContinuousOn f W) (hg : ContinuousOn g W)
    (heq : EqOn (fun x => Complex.exp (f x)) (fun x => Complex.exp (g x)) W)
    (p : X) (hp : p ∈ W) :
    ∀ x ∈ W, f x - g x = f p - g p := by
  let H : X → ℂ := fun x => f x - g x
  have hH : ContinuousOn H W := hf.sub hg
  have hconnected : IsPreconnected (H '' W) := hW.image H hH
  have hsubset : H '' W ⊆ {z : ℂ | Complex.exp z = 1} := by
    rintro z ⟨x, hx, rfl⟩
    change Complex.exp (f x - g x) = 1
    exact Complex.exp_eq_exp_iff_exp_sub_eq_one.mp (heq hx)
  have hsub : (H '' W).Subsingleton :=
    complex_exp_one_fiber_countable.isTotallyDisconnected _ hsubset hconnected
  intro x hx
  exact hsub ⟨x, hx, rfl⟩ ⟨p, hp, rfl⟩

/-- A map admitting a continuous logarithm has zero lift increment on any
closed loop in its domain. -/
theorem solution
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (W : Set X) (hW : IsPreconnected W) (S : Set Y)
    (u v : X) (hu : u ∈ W) (hv : v ∈ W)
    (q : X → Y) (F f : Y → ℂ) (h : X → ℂ)
    (hq : ContinuousOn q W) (hqS : MapsTo q W S)
    (hf : ContinuousOn f S) (hh : ContinuousOn h W)
    (hfe : EqOn (fun z => Complex.exp (f z)) F S)
    (hqh : EqOn (fun x => Complex.exp (h x)) (fun x => F (q x)) W)
    (hloop : q u = q v) : h u = h v := by
  have hfc : ContinuousOn (fun x => f (q x)) W := hf.comp hq hqS
  have he : EqOn (fun x => Complex.exp (f (q x)))
      (fun x => Complex.exp (h x)) W := by
    intro x hx
    exact (hfe (hqS hx)).trans (hqh hx).symm
  have hc := exp_lifts_diff_constant_on_preconnected W (fun x => f (q x)) h hW hfc hh he u hu v hv
  rw [hloop] at hc
  exact sub_right_inj.mp hc.symm

#print axioms solution
