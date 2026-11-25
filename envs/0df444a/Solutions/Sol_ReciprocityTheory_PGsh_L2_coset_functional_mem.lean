-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.coset_functional_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:35:46.496586+00:00
-- url     : https://prove2.me/submissions/0f2a3cd9-f945-44f7-88f1-0f438c9e25db

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitDetOfSpanEq
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetLeOneOfEntriesIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution (AA : HopfOrder (C := C) R N) (K : AddSubgroup N) [DecidablePred (· ∈ K)] (φ : (K → C) →ₗ[C] C)
    (hφ : ∀ h ∈ AA.carrier.map (resK (R := R) K), ∃ r : R, algebraMap R C r = φ h)
    {f : N → C} (hf : f ∈ AA.carrier) :
    (fun x => φ (fun k : K => f (x + k))) ∈ AA.carrier := by
  let φR := φ.restrictScalars R
  let Ψ : (N × N → C) →ₗ[R] (N → C) :=
    (φR.compLeft N) ∘ₗ (LinearEquiv.curry R C N K).toLinearMap ∘ₗ
      LinearMap.funLeft R C (fun p : N × K => (p.1, (p.2 : N)))
  have key : tensorSpan R AA.carrier ≤ AA.carrier.comap Ψ := by
    refine Submodule.span_le.mpr ?_
    rintro F ⟨g, hg, h, hh, rfl⟩
    obtain ⟨r, hr⟩ := hφ (resK (R := R) K h) (Submodule.mem_map_of_mem hh)
    rw [SetLike.mem_coe, Submodule.mem_comap]
    have e : Ψ (fun p : N × N => g p.1 * h p.2) = r • g := by
      ext x
      have : (fun k : K => g x * h k) = g x • resK (R := R) K h := by
        ext k; simp [resK]
      simp only [Ψ, φR, LinearMap.coe_comp, Function.comp_apply, LinearMap.compLeft_apply,
        LinearEquiv.coe_coe, LinearMap.restrictScalars_apply]
      show φ (fun k : K => g x * h k) = (r • g) x
      rw [this, φ.map_smul, ← hr]
      simp [Algebra.smul_def, mul_comm]
    rw [e]; exact AA.carrier.smul_mem r hg
  exact key (AA.comul f hf)
end ReciprocityTheory.PGsh.L2
