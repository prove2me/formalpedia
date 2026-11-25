-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.TrOrb.orbHom_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:10:15.353802+00:00
-- url     : https://prove2.me/submissions/c00437f0-5e77-4f4a-9d28-87807e93dce6

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_TrOrbA
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_TrOrb_exists_equiv_of_finrank
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_TrOrb_finrank_piece_rep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Module
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Piece PositivityTheory.RgUd.TP.Desc.Piece.TrOrb
universe u
namespace PositivityTheory.RgUd.TP.Desc.Piece.TrOrb
theorem _root_.solution (k : Type*) [Field k] (N : ℕ) (A : Type*) [CommRing A] [Algebra k A] [FiniteDimensional k A]
    (hA : IsReduced A) (ρ ρ' : A →ₐ[k] Matrix (Fin N) (Fin N) k)
    (h : ∀ e : A, IsIdempotentElem e → (ρ e).rank = (ρ' e).rank) :
    ∃ g : GL (Fin N) k, ∀ a, ρ' a = g.val * ρ a * g⁻¹.val := by
  obtain ⟨F⟩ := exists_equiv_of_finrank (k := k) (A := A) (Rep ρ) (Rep ρ') fun e he => by
    rw [finrank_piece_rep, finrank_piece_rep, h e he]
  let f : (Fin N → k) ≃ₗ[k] (Fin N → k) := F.restrictScalars k
  have hf : ∀ a v, f (ρ a *ᵥ v) = ρ' a *ᵥ f v := fun a v => F.map_smul a v
  let g : GL (Fin N) k := ⟨LinearMap.toMatrix' f.toLinearMap, LinearMap.toMatrix' f.symm.toLinearMap, by
      rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]; congr 1; ext v; simp, by
      rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]; congr 1; ext v; simp⟩
  refine ⟨g, fun a => ?_⟩
  have hc : ρ' a * g.val = g.val * ρ a := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
    show Matrix.toLin' (ρ' a) ∘ₗ Matrix.toLin' (LinearMap.toMatrix' f.toLinearMap) =
      Matrix.toLin' (LinearMap.toMatrix' f.toLinearMap) ∘ₗ Matrix.toLin' (ρ a)
    rw [Matrix.toLin'_toMatrix']
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply]
    exact (hf a v).symm
  calc ρ' a = ρ' a * (g.val * g⁻¹.val) := by rw [Units.mul_inv, mul_one]
    _ = g.val * ρ a * g⁻¹.val := by rw [← mul_assoc, hc]
end PositivityTheory.RgUd.TP.Desc.Piece.TrOrb
