-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Gwa2.isSmooth_twAct
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:25:01.550571+00:00
-- url     : https://prove2.me/submissions/5b6af5ca-a159-4f4a-b702-aa07baef0558

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsSmoothTwAct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private theorem UpperTheory.Reformulated.B.Gwa2.isOpen_fixer {M W : Type} [Group M] [AddCommGroup W] [_root_.Module ℂ W]
    [TopologicalSpace M] [IsTopologicalGroup M] (τ : Representation ℂ M W) (x : W)
    (h : {m : M | τ m x = x} ∈ nhds (1 : M)) : IsOpen {m : M | τ m x = x} := by
  let H : Subgroup M :=
    { carrier := {m : M | τ m x = x}
      one_mem' := by simp
      mul_mem' := fun {a b} (ha : τ a x = x) (hb : τ b x = x) ↦ show τ (a * b) x = x by
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a} (ha : τ a x = x) ↦ show τ a⁻¹ x = x by
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  exact H.isOpen_of_mem_nhds h
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Gwa2
theorem _root_.solution :
    ∀ {G M V : Type} [inst : Group G] [inst_1 : Group M] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module ℂ V]
      [inst_4 : TopologicalSpace G] [inst_5 : TopologicalSpace M] [IsTopologicalGroup M] (ρ : Representation ℂ G V)
      (N : Subgroup G) (θ : ↥N →* ℂˣ) (s : M →* G)
      (hs :
        ∀ (m : M) (n : ↥N),
          ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
            (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n),
      Continuous (⇑s : M → G) → UpperTheory.Reformulated.B.Gwa2.IsSmooth ρ → UpperTheory.Reformulated.B.Gwa2.IsSmooth (UpperTheory.Reformulated.B.Gwa2.twAct ρ N θ s hs) := by
  intro G M V _ _ _ _ _ _ _ ρ N θ s hs hc hρ x
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine UpperTheory.Reformulated.B.Gwa2.isOpen_fixer _ _ ?_
  have hU : IsOpen {m : M | ρ (s m) v = v} := (hρ v).preimage hc
  refine Filter.mem_of_superset (hU.mem_nhds (by simp)) fun m (hm : ρ (s m) v = v) ↦ ?_
  change Submodule.Quotient.mk (ρ (s m) v) = Submodule.Quotient.mk v
  rw [hm]
end UpperTheory.Reformulated.B.Gwa2
