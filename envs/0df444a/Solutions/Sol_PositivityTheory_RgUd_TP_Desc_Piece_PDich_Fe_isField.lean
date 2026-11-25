-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.PDich.Fe_isField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:54:49.007253+00:00
-- url     : https://prove2.me/submissions/bcf48fdb-3f1b-46fa-80ce-edb024a06a97

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_ToMatrixMulVec
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FeIsField
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_of_val
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_val_of
import Theorems.Thm_GroundTheory_Brauer_tensorCSA_carrier
import Theorems.Thm_GroundTheory_Brauer_tensorCentralizerAlgEquiv_tmul
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PDich_Pe_surj
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PDich_mat_ext
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Brauer.SkolemNoether.Twist.of_val
attribute [local simp] GroundTheory.Brauer.SkolemNoether.Twist.val_of
attribute [local simp] GroundTheory.Brauer.tensorCSA_carrier
attribute [local simp] GroundTheory.Brauer.tensorCentralizerAlgEquiv_tmul



set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Piece PositivityTheory.RgUd.TP.Desc.Piece.PDich
variable {k : Type} [Field k] {N : ℕ} {A : Subalgebra k (Matrix (Fin N) (Fin N) k)} {e : Matrix (Fin N) (Fin N) k}
variable (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (he : e ∈ A)
namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich
theorem _root_.solution (hne : e ≠ 0)
    (hf : ∀ a ∈ A, e * a = 0 ∨ ∃ b ∈ A, e * a * b = e) : IsField (Fe hA he) := by
  have hW : ∃ v : Fin N → k, e *ᵥ v ≠ 0 := by
    by_contra h; push Not at h; exact hne (mat_ext fun v => by simp [h v])
  obtain ⟨v₀, hv₀⟩ := hW
  refine ⟨⟨0, 1, fun h => ?_⟩, ?_, ?_⟩
  · have := congrArg (fun x : Fe hA he => ((x.1 (Pe e v₀) : Wd e) : Fin N → k)) h
    change 0 = e *ᵥ v₀ at this
    exact hv₀ this.symm
  · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    apply Subtype.ext
    show rho hA he a * rho hA he b = rho hA he b * rho hA he a
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hA _ a.2 _ b.2)
  · rintro ⟨_, a, rfl⟩ hx
    have hea : e * a.1 ≠ 0 := by
      intro h0; apply hx; apply Subtype.ext
      ext w : 1; apply Subtype.ext
      obtain ⟨v, rfl⟩ := Pe_surj e w
      show a.1 *ᵥ (e *ᵥ v) = 0
      rw [Matrix.mulVec_mulVec, hA _ a.2 _ he, h0, Matrix.zero_mulVec]
    rcases hf a.1 a.2 with h0 | ⟨b, hb, hab⟩
    · exact absurd h0 hea
    refine ⟨⟨rho hA he ⟨b, hb⟩, ⟨b, hb⟩, rfl⟩, ?_⟩
    apply Subtype.ext
    ext w : 1; apply Subtype.ext
    obtain ⟨v, rfl⟩ := Pe_surj e w
    show a.1 *ᵥ (b *ᵥ (e *ᵥ v)) = e *ᵥ v
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc, hA _ hb _ he, ← mul_assoc,
      hA _ a.2 _ he, hab]
end PositivityTheory.RgUd.TP.Desc.Piece.PDich
