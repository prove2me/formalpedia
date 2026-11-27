-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_blockAddData_joinPt_mem_39f128ebc895
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:10:06.315747+00:00
-- url     : https://prove2.me/submissions/4c1a8024-a191-4388-bc8a-a9d7c2cd0189

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_blockSubst_eq_zero_584f1638d3d0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (n : ι → ℕ) (k₀ : ι)
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (z : Cone n ℂ) (hz : BlockNonzero z) :
    (blockAddData n k₀).joinPt z (z k₀) ∈ (blockAddData n k₀).extPoints := by
  refine ⟨fun o ↦ ?_, fun f hf ↦ ?_⟩
  · cases o with
    | none => exact hz k₀
    | some k => exact hz k
  · let ev : MvPolynomial (Option ι) (MvPolynomial (Coord n) ℤ) →+* ℂ :=
      eval₂Hom (eval₂Hom (Int.castRingHom ℂ) fun v ↦ z v.1 v.2) fun _ ↦ 1
    have hev : (eval₂Hom (Int.castRingHom ℂ) fun v : Coord (blockAddData n k₀).extSizes ↦
        (blockAddData n k₀).joinPt z (z k₀) v.1 v.2) = ev.comp (blockSubst n k₀) := by
      refine MvPolynomial.ringHom_ext (fun r ↦ by simp [ev, blockSubst]) (fun v ↦ ?_)
      rcases v with ⟨_ | k, i⟩ <;> simp [ev, blockSubst, blockVal, AddBlockData.joinPt]
    change (eval₂Hom (Int.castRingHom ℂ) fun v : Coord (blockAddData n k₀).extSizes ↦
        (blockAddData n k₀).joinPt z (z k₀) v.1 v.2) f = 0
    rw [hev, RingHom.comp_apply, blockSubst_eq_zero n k₀ hf, map_zero]
end GroundTheory.Heights₂.Heights
