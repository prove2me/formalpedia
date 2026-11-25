-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.U3.scale_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:08:19.570469+00:00
-- url     : https://prove2.me/submissions/3f2c98ee-78bd-48e2-a9e1-c3318a8bbe9c

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_VIntCastLtOneOfDvd
import Definitions.Def_ReciprocityTheory_DualLattices_SumLambdaWeight
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_IsTeich_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.U3
open ReciprocityTheory.PGsh.L2
variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal}
  {R : Type} [CommRing R] [Algebra R C]
variable (hv : v.Integers R)
include hv
omit hv
namespace ReciprocityTheory.PGsh.Up.U3
theorem _root_.solution (AA : HopfOrder (C := C) R (ZMod p)) {f : ZMod p → C} (hf : f ∈ AA.carrier)
    (b : ZMod p) : (fun t => f (b * t)) ∈ AA.carrier := by
  have key : ∀ α β : ZMod p → ZMod p,
      (∀ g ∈ AA.carrier, (fun t => g (α t)) ∈ AA.carrier) →
      (∀ g ∈ AA.carrier, (fun t => g (β t)) ∈ AA.carrier) →
      ∀ F ∈ tensorSpan R AA.carrier, (fun t => F (α t, β t)) ∈ AA.carrier := by
    intro α β hα hβ F hF
    induction hF using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, k, hk, rfl⟩ := hx
      exact AA.mul_mem _ _ (hα g hg) (hβ k hk)
    | zero => exact AA.carrier.zero_mem
    | add x y _ _ hx hy => exact AA.carrier.add_mem hx hy
    | smul a x _ hx => exact AA.carrier.smul_mem a hx
  have hn : ∀ n : ℕ, ∀ g ∈ AA.carrier, (fun t => g ((n : ZMod p) * t)) ∈ AA.carrier := by
    intro n
    induction n with
    | zero =>
      intro g hg
      have e : (fun t => g (((0 : ℕ) : ZMod p) * t)) =
          fun t => (addPull R (ZMod p) g) (t, -t) := by
        funext t
        simp [addPull]
      rw [e]
      exact key (fun t => t) (fun t => -t) (fun g hg => hg) (fun g hg => AA.antipode g hg) _
        (AA.comul g hg)
    | succ n ih =>
      intro g hg
      have e : (fun t => g (((n + 1 : ℕ) : ZMod p) * t)) =
          fun t => (addPull R (ZMod p) g) ((n : ZMod p) * t, t) := by
        funext t
        simp [addPull, add_mul]
      rw [e]
      exact key (fun t => (n : ZMod p) * t) (fun t => t) ih (fun g hg => hg) _ (AA.comul g hg)
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have h := hn b.val f hf
  simpa [ZMod.natCast_zmod_val] using h
end ReciprocityTheory.PGsh.Up.U3
