-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.dmin_line_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:50:25.880818+00:00
-- url     : https://prove2.me/submissions/45ea00e7-6963-43c3-b3dc-44473443a9a1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DetSubMapConj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_LeviFinsetSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_Gz_herm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_dmin_line


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates ReciprocityTheory.AnForm Filter Topology
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
variable (x0 b : Frame X.Ψ r) (z u : V (nd X))
variable {X x0 b z u}
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
theorem _root_.solution (hb : b ∈ Bor X.Ψ r) (hgram : ∀ τ, gram τ.1 X.Gm (mat (rmul (cpt X x0 z) b) τ) =
      diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) (v : Fin 1 → ℂ) (τ : X.Ψ) (k : Fin (r + 1)) :
    ‖dmin X.Gm (cpt X x0 (z + (v 0) • u)) τ k‖ =
      ‖((mat b τ)⁻¹.submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt))
        (Fin.castLE (Nat.le_of_lt_succ k.isLt))).det‖ ^ 2 * |fk X b z u τ k v| := by
  rw [dmin_line X x0 b hb z u τ (hgram τ) (v 0) k, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
  have hg : (Gz (Nat.le_of_lt_succ k.isLt) (Dsg X) (Yd X b z u τ) (v 0)).det.im = 0 := by
    have h := congrArg Matrix.det (Gz_herm (Nat.le_of_lt_succ k.isLt) (Dsg X) (Yd X b z u τ) (v 0))
    rw [Matrix.det_conjTranspose] at h
    exact Complex.conj_eq_iff_im.1 h
  have hn : ‖(Gz (Nat.le_of_lt_succ k.isLt) (Dsg X) (Yd X b z u τ) (v 0)).det‖ = |fk X b z u τ k v| := by
    unfold fk fY
    exact (Complex.abs_re_eq_norm.2 hg).symm
  rw [hn]
  ring
end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
