-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.MOne.solCount_one_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:21:20.345862+00:00
-- url     : https://prove2.me/submissions/477896e4-7643-4657-8be4-7f8ea3f9bad7

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
theorem _root_.solution {R : Type} [CommRing R] (σ : R →+* R) (ϖ : R) (j t : R) :
    solCount σ ϖ (Matrix.of fun _ _ => j : Matrix (Fin 1) (Fin 1) R) (Matrix.of fun _ _ => t : Matrix (Fin 1) (Fin 1) R) 1 =
      Nat.card (Ideal.Quotient.mk (lev ϖ 1) '' {x : R | Ideal.Quotient.mk (lev ϖ 1) (σ x * j * x) =
        Ideal.Quotient.mk (lev ϖ 1) t}) := by
  classical
  unfold solCount
  have hinj : Function.Injective (fun y : Matrix (Fin 1) (Fin 1) (R ⧸ lev ϖ 1) => y 0 0) := by
    intro y y' h
    ext a b
    obtain rfl : a = 0 := Subsingleton.elim _ _
    obtain rfl : b = 0 := Subsingleton.elim _ _
    exact h
  rw [← Nat.card_image_of_injective hinj, Set.image_image]
  refine congrArg (fun s : Set (R ⧸ lev ϖ 1) => Nat.card s) ?_
  ext c
  constructor
  · rintro ⟨X, hX, rfl⟩
    refine ⟨X 0 0, ?_, rfl⟩
    have h00 := congrFun (congrFun hX 0) 0
    simpa [red, cT, Matrix.mul_apply] using h00
  · rintro ⟨x, hx, rfl⟩
    refine ⟨Matrix.of fun _ _ => x, ?_, rfl⟩
    simp only [Set.mem_ofPred_eq]
    ext a b
    obtain rfl : a = 0 := Subsingleton.elim _ _
    obtain rfl : b = 0 := Subsingleton.elim _ _
    simpa [red, cT, Matrix.mul_apply] using hx
end PositivityTheory.SiegelWeilFormula.MOne
