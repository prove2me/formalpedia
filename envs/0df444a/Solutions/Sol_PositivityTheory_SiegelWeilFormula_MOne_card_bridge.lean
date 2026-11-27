-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.MOne.card_bridge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:21:18.026124+00:00
-- url     : https://prove2.me/submissions/3a37a3d2-d9e6-4fb7-a9fa-17c71df6c8b1

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_MassOneCounts_SolCountOneOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.MOne
open PositivityTheory.PfSWUS.Loc
namespace PositivityTheory.SiegelWeilFormula.MOne
theorem _root_.solution {W A R : Type} [CommRing R] (ϖ : R) (a : W → A) (ha : Function.Surjective a) (φ : W → R)
    (hφ : Function.Surjective φ) (hker : ∀ w w', a w = a w' ↔ φ w - φ w' ∈ lev ϖ 1) (PA : A → Prop) (PR : R → Prop)
    (hP : ∀ w, PA (a w) ↔ PR (φ w)) :
    Nat.card {y // PA y} = Nat.card (Ideal.Quotient.mk (lev ϖ 1) '' {x | PR x}) := by
  classical
  choose s hs using ha
  let e : A → R ⧸ lev ϖ 1 := fun y => Ideal.Quotient.mk (lev ϖ 1) (φ (s y))
  have hinj : Function.Injective e := by
    intro y y' h
    have h' := Ideal.Quotient.eq.mp h
    rw [← hs y, ← hs y']
    exact (hker _ _).mpr h'
  have himg : e '' {y | PA y} = Ideal.Quotient.mk (lev ϖ 1) '' {x | PR x} := by
    ext c
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨φ (s y), ?_, rfl⟩
      have hy' : PA (a (s y)) := by
        rw [hs y]
        exact hy
      exact (hP _).mp hy'
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨w, rfl⟩ := hφ x
      refine ⟨a w, (hP w).mpr hx, ?_⟩
      exact Ideal.Quotient.eq.mpr ((hker _ _).mp (hs (a w)))
  rw [← himg, Nat.card_image_of_injective hinj]
  rfl
end PositivityTheory.SiegelWeilFormula.MOne
