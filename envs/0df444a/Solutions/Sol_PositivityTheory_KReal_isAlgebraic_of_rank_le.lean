-- Prove2me | solution 1 for PositivityTheory.KReal.isAlgebraic_of_rank_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:21:38.455033+00:00
-- url     : https://prove2.me/submissions/493fe8ce-5bb2-4f64-a452-ae6bc5881c46

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_TensorIrr
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Algebraic.LinearIndependent
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Cardinality
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SpectrumNonemptyOfCountableRank
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_Tensor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.KReal
namespace PositivityTheory.KReal
theorem _root_.solution {D : Type} [DivisionRing D] [Algebra ℂ D]
    (h : Module.rank ℂ D ≤ Cardinal.aleph0) (x : D) : IsAlgebraic ℂ x := by
  let S : Subalgebra ℂ D := Subalgebra.centralizer ℂ (Subalgebra.centralizer ℂ {x} : Set D)
  have hS : ∀ a : D, a ∈ S ↔ ∀ g : D, x * g = g * x → g * a = a * g := by
    intro a
    simp only [S, Subalgebra.mem_centralizer_iff, SetLike.mem_coe, Set.mem_singleton_iff, forall_eq]
  have hx : x ∈ S := (hS x).2 fun g hg => hg.symm
  have hF : IsField S :=
    { exists_pair_ne := ⟨0, 1, zero_ne_one⟩
      mul_comm := fun a b => Subtype.ext ((hS b).1 b.2 a ((hS a).1 a.2 x rfl))
      mul_inv_cancel := fun {a} ha => by
        have ha' : (a : D) ≠ 0 := fun h0 => ha (Subtype.ext h0)
        refine ⟨⟨(a : D)⁻¹, (hS _).2 fun g hg => ?_⟩, Subtype.ext (mul_inv_cancel₀ ha')⟩
        exact (Commute.inv_right₀ ((hS a).1 a.2 g hg : Commute g a)).eq }
  letI : Field S := hF.toField
  have hx' : IsAlgebraic ℂ (⟨x, hx⟩ : S) := by
    by_contra ht
    have h1 := (Transcendental.linearIndependent_sub_inv (F := ℂ) (E := S) ht).cardinal_le_rank
    have h2 : Module.rank ℂ S ≤ Module.rank ℂ D :=
      LinearMap.rank_le_of_injective S.val.toLinearMap Subtype.val_injective
    rw [Cardinal.mk_complex] at h1
    exact absurd (h1.trans (h2.trans h)) (not_le.2 Cardinal.aleph0_lt_continuum)
  exact hx'.algHom S.val
end PositivityTheory.KReal
