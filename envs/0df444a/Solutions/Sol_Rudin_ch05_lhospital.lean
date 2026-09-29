-- Prove2me | solution 1 for Rudin.ch05_lhospital
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:39:23.296818+00:00
-- url     : https://prove2.me/submissions/c1d63439-07b0-483c-88fe-a23c41123779

import Mathlib
set_option autoImplicit false
open Filter Topology
theorem solution (a b : ℝ) (hab : a < b) (f g : ℝ → ℝ) (A : ℝ)
    (hfd : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ f x)
    (hgd : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ g x)
    (hg' : ∀ x ∈ Set.Ioo a b, deriv g x ≠ 0)
    (hratio : Tendsto (fun x => deriv f x / deriv g x) (𝓝[>] a) (𝓝 A))
    (hf0 : Tendsto f (𝓝[>] a) (𝓝 0)) (hg0 : Tendsto g (𝓝[>] a) (𝓝 0)) :
    Tendsto (fun x => f x / g x) (𝓝[>] a) (𝓝 A) := by
  apply deriv.lhopital_zero_nhdsGT _ _ hf0 hg0 hratio
  · filter_upwards [Ioo_mem_nhdsGT hab] with x hx using hfd x hx
  · filter_upwards [Ioo_mem_nhdsGT hab] with x hx using hg' x hx
#print axioms solution
