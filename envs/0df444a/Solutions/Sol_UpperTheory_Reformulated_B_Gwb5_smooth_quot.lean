-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Gwb5.smooth_quot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:44:10.272495+00:00
-- url     : https://prove2.me/submissions/ad17f117-94a8-4130-91ce-077cb838d9d9

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothQuot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Gwb5
theorem _root_.solution :
    ∀ {G : Type} [inst : Group G] {U : Type} [inst_1 : AddCommGroup U] [inst_2 : _root_.Module ℂ U]
      [inst_3 : TopologicalSpace G] [IsTopologicalGroup G] {ρ : Representation ℂ G U},
      UpperTheory.Reformulated.B.Gwb5.IsSmooth ρ →
        ∀ (T : Submodule ℂ U) (hst : ∀ (g : G), T ≤ Submodule.comap ((ρ : G → U →ₗ[ℂ] U) g) T),
          UpperTheory.Reformulated.B.Gwb5.IsSmooth (ρ.quotient T hst) := by
  intro G _ U _ _ _ _ ρ h T hst v
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective T v
  let H : Subgroup G :=
    { carrier := {g : G | ρ.quotient T hst g (Submodule.Quotient.mk u) = Submodule.Quotient.mk u}
      one_mem' := by
        show ρ.quotient T hst 1 _ = _
        rw [map_one]
        rfl
      mul_mem' := by
        intro a b ha hb
        have ha' : ρ.quotient T hst a (Submodule.Quotient.mk u) = Submodule.Quotient.mk u := ha
        have hb' : ρ.quotient T hst b (Submodule.Quotient.mk u) = Submodule.Quotient.mk u := hb
        show ρ.quotient T hst (a * b) _ = _
        rw [map_mul, Module.End.mul_apply, hb', ha']
      inv_mem' := by
        intro a ha
        have ha' : ρ.quotient T hst a (Submodule.Quotient.mk u) = Submodule.Quotient.mk u := ha
        show ρ.quotient T hst a⁻¹ _ = _
        conv_lhs => rw [← ha']
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl }
  refine H.isOpen_of_mem_nhds (g := 1) ?_
  have h1 : {g : G | ρ g u = u} ∈ nhds (1 : G) :=
    (h u).mem_nhds (by
      show ρ 1 u = u
      rw [map_one]
      rfl)
  refine Filter.mem_of_superset h1 ?_
  intro g hg
  have hg' : ρ g u = u := hg
  show ρ.quotient T hst g (Submodule.Quotient.mk u) = Submodule.Quotient.mk u
  have e : ρ.quotient T hst g (Submodule.Quotient.mk u) = Submodule.Quotient.mk (ρ g u) := rfl
  rw [e, hg']
end UpperTheory.Reformulated.B.Gwb5
