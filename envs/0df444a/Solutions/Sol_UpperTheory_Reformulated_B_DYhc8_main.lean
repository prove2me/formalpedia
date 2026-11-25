-- Prove2me | solution 1 for UpperTheory.Reformulated.B.DYhc8.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:58:03.951803+00:00
-- url     : https://prove2.me/submissions/33671b29-77a5-4b58-bf99-9b4ef3d6a162

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ConjInvariantCharacterTransport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private theorem continuous_glEmbMat (k : Type) [Field k] [TopologicalSpace k] (n : ℕ) :
    Continuous (UpperTheory.Reformulated.B.DYhc8.glEmbMat k n) := by
  refine continuous_matrix ?_
  intro i j
  simp only [UpperTheory.Reformulated.B.DYhc8.glEmbMat]
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simpa using continuous_const
    | cast j => simpa using continuous_const
  | cast i =>
    induction j using Fin.lastCases with
    | last => simpa using continuous_const
    | cast j => simpa using continuous_id.matrix_elem i j
private theorem continuous_levi (k : Type) [Field k] [TopologicalSpace k] (n : ℕ) :
    Continuous (UpperTheory.Reformulated.B.DYhc8.levi k n) := by
  have h : Continuous (UpperTheory.Reformulated.B.DYhc8.glEmb k n) :=
    Continuous.units_map (UpperTheory.Reformulated.B.DYhc8.glEmbHom k n) (continuous_glEmbMat k n)
  exact h.subtype_mk _
private theorem isOpen_fixed {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup W] [_root_.Module ℂ W] (ρ : Representation ℂ G W) (x : W) (U : Set G)
    (hU : IsOpen U) (h1 : (1 : G) ∈ U) (hsub : ∀ g ∈ U, ρ g x = x) :
    IsOpen {g : G | ρ g x = x} := by
  let S : Subgroup G :=
    { carrier := {g : G | ρ g x = x}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  exact S.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset (hU.mem_nhds h1) hsub)
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.DYhc8
theorem _root_.solution :
    ∀ (k : Type) [inst : Field k] [inst_1 : ValuativeRel k] [inst_2 : TopologicalSpace k]
      [inst_3 : IsNonarchimedeanLocalField k], UpperTheory.Reformulated.B.DYhc8.SmPsiMinus k := by
  intro k _ _ _ _ n V _ _ τ hτ x
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine isOpen_fixed (UpperTheory.Reformulated.B.DYhc8.psiMinus k τ) _
    (UpperTheory.Reformulated.B.DYhc8.levi k n ⁻¹' {g | τ g v = v})
    ((hτ v).preimage (continuous_levi k n)) (by simp) ?_
  intro g hg
  have hg' : τ (UpperTheory.Reformulated.B.DYhc8.levi k n g) v = v := hg
  change Submodule.Quotient.mk (τ (UpperTheory.Reformulated.B.DYhc8.levi k n g) v) = _
  rw [hg']
end UpperTheory.Reformulated.B.DYhc8
