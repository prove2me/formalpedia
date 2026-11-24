-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.PullbackHopfOrder.exists_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:47:21.105442+00:00
-- url     : https://prove2.me/submissions/cef55a77-7e7f-4149-ba92-428a78bd06db

import Definitions.Def_ReciprocityTheory_DualLattices_MemDualLat
import Definitions.Def_ReciprocityTheory_DualLattices_MapTensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsMatOfEquiv
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.PullbackHopfOrder
open ReciprocityTheory.PGsh.L2
variable {S : Type} [CommRing S] {n k : Type} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
namespace ReciprocityTheory.PGsh.Up.PullbackHopfOrder
theorem _root_.solution (e : Matrix n n S) (he : e * e = e) (B : Matrix n k S)
    (hr : LinearMap.range B.mulVecLin = LinearMap.range e.mulVecLin)
    (hk : LinearMap.ker B.mulVecLin = ⊥) : ∃ L : Matrix k n S, L * B = 1 ∧ B * L = e := by
  have hcol : ∀ j : n, ∃ c : k → S, B *ᵥ c = e *ᵥ Pi.single j 1 := by
    intro j
    have hmem : e *ᵥ Pi.single j 1 ∈ LinearMap.range B.mulVecLin := by
      rw [hr]
      exact ⟨_, rfl⟩
    obtain ⟨c, hc⟩ := hmem
    exact ⟨c, hc⟩
  choose c hc using hcol
  let L : Matrix k n S := Matrix.of fun i j => c j i
  have hBL : B * L = e := by
    ext i j
    have h1 := congrFun (hc j) i
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at h1
    rw [← h1]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, L]
  have heB : e * B = B := by
    ext i j
    have hmem : B *ᵥ Pi.single j 1 ∈ LinearMap.range e.mulVecLin := by
      rw [← hr]
      exact ⟨_, rfl⟩
    obtain ⟨w, hw⟩ := hmem
    have h2 : e *ᵥ (B *ᵥ Pi.single j 1) = B *ᵥ Pi.single j 1 := by
      rw [← hw]
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, he]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h2
    simpa [Matrix.col_apply] using congrFun h2 i
  have hinj : Function.Injective B.mulVecLin := LinearMap.ker_eq_bot.1 hk
  refine ⟨L, ?_, hBL⟩
  ext i j
  have h3 : B *ᵥ ((L * B) *ᵥ Pi.single j 1) = B *ᵥ Pi.single j 1 := by
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hBL, heB]
  have h4 : (L * B) *ᵥ Pi.single j 1 = Pi.single j 1 := hinj h3
  rw [Matrix.mulVec_single_one] at h4
  have h5 := congrFun h4 i
  simp only [Matrix.col_apply] at h5
  rw [h5, Matrix.one_apply, Pi.single_apply]
end ReciprocityTheory.PGsh.Up.PullbackHopfOrder
