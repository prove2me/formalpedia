-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.PSect.fc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:55:14.225599+00:00
-- url     : https://prove2.me/submissions/ce232083-0702-487f-a2ba-5557a7dfcd75

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_MemPw
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_mem_Pw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Piece PositivityTheory.RgUd.TP.Desc.Piece.PSect
open Module
variable {k : Type*} [Field k]
namespace PositivityTheory.RgUd.TP.Desc.Piece.PSect
theorem _root_.solution {B : Type*} [CommRing B] [Algebra k B] [FiniteDimensional k B] [IsReduced B]
    (p c : ℕ) [Fact p.Prime] [CharP k p] [FiniteDimensional k (Tw k p c)]
    (hroot : ∀ a : k, ∃ w : B, w ^ (p ^ c) = algebraMap k B a) :
    finrank k B = finrank k (Tw k p c) * finrank k (Pw k B (p ^ c)) := by
  classical
  letI iT : Module (Tw k p c) (Pw k B (p ^ c)) := inferInstanceAs (Module k (Pw k B (p ^ c)))
  have hadd : ∀ x y : B, (x + y) ^ (p ^ c) = x ^ (p ^ c) + y ^ (p ^ c) := by
    intro x y
    rcases subsingleton_or_nontrivial B with hB | hB
    · exact Subsingleton.elim _ _
    · haveI := charP_of_injective_algebraMap (algebraMap k B).injective p
      exact add_pow_char_pow x y p c
  have hmem : ∀ x : B, x ^ (p ^ c) ∈ Pw k B (p ^ c) := fun x =>
    Algebra.subset_adjoin ⟨x, rfl⟩
  let f : B →ₗ[k] RestrictScalars k (Tw k p c) (Pw k B (p ^ c)) :=
    { toFun := fun x => (⟨x ^ (p ^ c), hmem x⟩ : Pw k B (p ^ c))
      map_add' := fun x y => by
        apply Subtype.ext
        exact hadd x y
      map_smul' := fun a x => by
        apply Subtype.ext
        show (a • x) ^ (p ^ c) = ((algebraMap k (Tw k p c) a) • (⟨x ^ (p ^ c), hmem x⟩ : Pw k B (p ^ c)) : Pw k B (p ^ c)).1
        rw [smul_pow]
        rfl }
  have hinj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun x hx => ?_
    have h0 : x ^ (p ^ c) = 0 := congrArg (fun z : Pw k B (p ^ c) => (z : B)) hx
    exact IsReduced.eq_zero x ⟨_, h0⟩
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨w, hw⟩ := (mem_Pw p c hroot).1 (show (Pw k B (p ^ c)) from y).2
    exact ⟨w, Subtype.ext hw⟩
  letI : Module (Tw k p c) (RestrictScalars k (Tw k p c) (Pw k B (p ^ c))) :=
    RestrictScalars.moduleOrig k (Tw k p c) (Pw k B (p ^ c))
  haveI : Module.Free (Tw k p c) (RestrictScalars k (Tw k p c) (Pw k B (p ^ c))) :=
    show Module.Free k (Pw k B (p ^ c)) from inferInstance
  let e := LinearEquiv.ofBijective f ⟨hinj, hsurj⟩
  rw [e.finrank_eq, ← Module.finrank_mul_finrank k (Tw k p c)
    (RestrictScalars k (Tw k p c) (Pw k B (p ^ c)))]
  rfl
end PositivityTheory.RgUd.TP.Desc.Piece.PSect
