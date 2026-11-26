-- Prove2me | solution 1 for P2M_ReciprocityTheory_PGsh_DualPair_p__comp_i__dfbf9aefdac4
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:41:58.247889+00:00
-- url     : https://prove2.me/submissions/1da135a8-381a-424c-b52a-645231791295

import Definitions.Def_ReciprocityTheory_DualLattices_IsFibreSq
import Definitions.Def_ReciprocityTheory_DualLattices_ModuliPointsState


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
open ReciprocityTheory.PGsh.DualPair
variable {R : LAlg R₀} (Dp : DualPair R)
theorem _root_.solution : Dp.p₂L.comp Dp.i₁L = Dp.σ.comp Dp.π := by
  first
    | (intros; rfl)
    | exact Iff.rfl
    | decide
    | (intros; omega)
    | (intros; simp)
    | (intros; simp_all)
    | (intros; norm_num)
    | (intros; positivity)
    | (intros; aesop)
    | (intros; nlinarith)
    | (intros; field_simp; ring)
    | (intros; ext; simp)
    | (intros; constructor <;> intro h <;> simpa using h)
    | (intros; exact?)
  trace "HIT_51_8"



end 
