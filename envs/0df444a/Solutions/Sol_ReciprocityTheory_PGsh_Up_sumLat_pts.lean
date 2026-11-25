-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.sumLat_pts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:18:53.938829+00:00
-- url     : https://prove2.me/submissions/5342146b-eea3-4892-9a42-21f001952085

import Definitions.Def_ReciprocityTheory_DualLattices_DiscriminantColengthStatement
import Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqBlockVandermonde
import Theorems.Thm_ReciprocityTheory_PGsh_Up_sumLat_mulVec

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
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {v : Valuation C NNReal}
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {n s : ℕ} (Mτ : Fin n → Lat v (Fin s)) : (sumLat Mτ).pts = sumPts Mτ := by
  ext w
  constructor
  · rintro ⟨c, hc, rfl⟩ τ
    refine ⟨fun j => c (τ, j), fun j => hc (τ, j), ?_⟩
    funext i
    exact sumLat_mulVec Mτ c τ i
  · intro hw
    choose c hc hwc using hw
    refine ⟨fun y => c y.1 y.2, fun y => hc y.1 y.2, ?_⟩
    funext ⟨τ, i⟩
    rw [sumLat_mulVec]
    exact congrFun (hwc τ) i
end ReciprocityTheory.PGsh.Up
