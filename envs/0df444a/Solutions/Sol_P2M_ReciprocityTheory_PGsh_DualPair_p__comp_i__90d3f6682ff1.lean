-- Prove2me | solution 1 for P2M_ReciprocityTheory_PGsh_DualPair_p__comp_i__90d3f6682ff1
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:41:56.341874+00:00
-- url     : https://prove2.me/submissions/428b5a82-6717-43ca-9ced-0ec765268440

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
theorem _root_.solution : Dp.p₁L.comp Dp.i₁L = LHom.id Dp.D := by
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
  trace "HIT_51_7"



end 
