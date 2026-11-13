-- Prove2me | solution 1 for OddOrder.Peterfalvi.S11.uActionHom_range_comm
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T12:27:29.018729+00:00
-- url     : https://prove2.me/submissions/dab4f92c-0255-47b7-a1a4-94123eb8ac19

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S11_ImprimitiveUBound.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_ThetaCountAssembly
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SemilinearImprimitiveBound
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_AInvariantSubrep
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RepresentationTheory.Subrepresentation

-- ===== OddOrder/Peterfalvi/S11_ImprimitiveUBound.lean =====
namespace OddOrder.Peterfalvi.S11

open OddOrder.RepresentationTheory OddOrder.GroupTheory OddOrder.Isaacs.Ch03

open OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk')

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- **The `U`-action image `Ū = (uActionHom).range` is abelian.**  A commutator `⁅a, b⁆ ∈ [U, U]`
centralizes `H` (Peterfalvi (8.5.b), `typeP_commutator_U_centralizes_H`), so acts trivially on `H̄`,
i.e. `uActionHom ⁅a, b⁆ = 1`; hence the images `uActionHom a`, `uActionHom b` commute. -/
theorem _root_.solution [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    (chief : ChiefFactorData data) (s t : ↥(MonoidHom.range (uActionHom data chief))) :
    s * t = t * s := by
  have : chief.N.Normal := chief.N_normal
  set act := typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant with hact
  -- `uActionHom = act.φ.comp act.U.subtype` definitionally; work through `φU` to match its domain.
  set φU := act.φ.comp act.U.subtype with hφU
  have hcentral_triv : ∀ g : ↥(data.typeP.U ⊔ data.typeP.W1),
      (g : G) ∈ Subgroup.centralizer (data.typeP.H : Set G) → act.φ g = 1 := by
    intro g hg
    have hfix : ∀ x : ↥data.typeP.H, (typeP_conjAction data.typeP g) x = x := by
      intro x
      apply Subtype.ext
      rw [typeP_conjAction_apply]
      have hcom : (x : G) * (g : G) = (g : G) * (x : G) :=
        (Subgroup.mem_centralizer_iff.mp hg) (x : G) x.2
      rw [← hcom, mul_assoc, mul_inv_cancel, mul_one]
    ext y
    refine QuotientGroup.induction_on y ?_
    intro x
    change (act.φ g) (QuotientGroup.mk' chief.N x) = QuotientGroup.mk' chief.N x
    have hstep : (act.φ g) (QuotientGroup.mk' chief.N x)
        = QuotientGroup.mk' chief.N ((typeP_conjAction data.typeP g) x) := rfl
    rw [hstep, hfix x]
  have hComm : ∀ a b : ↥act.U, Commute (φU a) (φU b) := by
    intro a b
    refine commutatorElement_eq_one_iff_commute.mp ?_
    rw [← map_commutatorElement φU a b]
    change act.φ (act.U.subtype ⁅a, b⁆) = 1
    apply hcentral_triv
    change ((data.typeP.U ⊔ data.typeP.W1).subtype.comp act.U.subtype) ⁅a, b⁆
        ∈ Subgroup.centralizer (data.typeP.H : Set G)
    rw [map_commutatorElement]
    exact typeP_commutator_U_centralizes_H data.typeP
      (Subgroup.commutator_mem_commutator
        (Subgroup.mem_subgroupOf.mp a.2) (Subgroup.mem_subgroupOf.mp b.2))
  obtain ⟨_, a, rfl⟩ := s
  obtain ⟨_, b, rfl⟩ := t
  exact Subtype.ext (hComm a b)

end OddOrder.Peterfalvi.S11
