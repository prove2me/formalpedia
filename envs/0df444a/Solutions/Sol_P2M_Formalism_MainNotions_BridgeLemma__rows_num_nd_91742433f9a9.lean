-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__rows_num_nd_91742433f9a9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:18.604268+00:00
-- url     : https://prove2.me/submissions/5d32719e-8166-4079-bb06-a9ad9401f02d

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_RowsNum
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_RowsRpowPow
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__rows_num_Q_8db4989c427f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
open Formalism.HermitianLatticeCounting
namespace Formalism.MainNotions.BridgeLemma₂
theorem _root_.solution {k m f s r : ℕ} {b g v Γ c C pe E1 cr δ rD XiP : ℝ} {Xi : ℕ → ℝ}
    (hb : 2 ≤ b) (hg : 0 < g) (hv : 0 < v) (hΓ : 0 ≤ Γ) (hc : 0 ≤ c) (hcC : c ≤ C) (hC : 1 ≤ C)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1) (hrD : 0 ≤ rD) (hXiP : 0 ≤ XiP) (hXi : XiP ≤ Xi s)
    (hexp : 1 + 12 * (f : ℝ) * ((r : ℝ) + 1) ^ 2 + pe * (2 * E1 + 2 * cr + 6 * ((r : ℝ) + 1) ^ 2) ≤
      C * (m : ℝ) ^ 2 * f * (C * ((s : ℝ) + m) * (m : ℝ) ^ 2)) :
    (2 / g) ^ ((s - 1) * k * f) * ((k : ℝ) * v / (Real.exp 1 * Real.pi)) ^ (k * f) *
        (XiP * (((b ^ pe) ^ E1) ^ 2 * ((b ^ pe) ^ cr) ^ 2 * (c * s * f) ^ (6 * s * f) * Γ)) * ((1 + δ) * rD) *
        ((41 ^ f * (b ^ pe) ^ 3) ^ ((r + 1) ^ 2)) ^ 2 ≤
      LatticeSumBounds.ndRow C k m f s b g v Γ Xi * rD := by
  have hb0 : 0 < b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hC0 : 0 < C := by linarith
  have hXis : 0 ≤ Xi s := hXiP.trans hXi
  have hH : b ^ (1 + 12 * (f : ℝ) * ((r : ℝ) + 1) ^ 2 + pe * (2 * E1 + 2 * cr + 6 * ((r : ℝ) + 1) ^ 2)) ≤
      Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) := by
    unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH
    rw [← Real.rpow_mul hb0.le]
    first
      | exact Real.rpow_le_rpow_of_exponent_le hb1 hexp
      | exact (Real.rpow_le_rpow_left_iff (by linarith)).2 hexp
  have hB := (rows_num_Q (f := f) (r := r) (pe := pe) (E1 := E1) (cr := cr) hb hδ0 hδ).trans hH
  have hep : 1 ≤ Real.exp 1 * Real.pi := by
    have h1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h2 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    nlinarith
  have hkv : 0 ≤ (k : ℝ) * v := by positivity
  have hq : (k : ℝ) * v / (Real.exp 1 * Real.pi) ≤ (k : ℝ) * v * C := by
    have hd : (k : ℝ) * v / (Real.exp 1 * Real.pi) ≤ (k : ℝ) * v := by
      first
        | exact div_le_self hkv hep
        | (rw [div_le_iff₀ (by positivity)]; nlinarith)
    nlinarith
  have hK : ((k : ℝ) * v / (Real.exp 1 * Real.pi)) ^ (k * f) ≤ ((k : ℝ) * v) ^ (k * f) * C ^ (k * f) := by
    rw [← mul_pow]
    gcongr
  calc _ = ((2 / g) ^ ((s - 1) * k * f) * ((k : ℝ) * v / (Real.exp 1 * Real.pi)) ^ (k * f) * XiP *
          (c * s * f) ^ (6 * s * f) * Γ * rD) *
        ((1 + δ) * (((b ^ pe) ^ E1) ^ 2 * ((b ^ pe) ^ cr) ^ 2) * ((41 ^ f * (b ^ pe) ^ 3) ^ ((r + 1) ^ 2)) ^ 2) := by
        ring
    _ ≤ ((2 / g) ^ ((s - 1) * k * f) * (((k : ℝ) * v) ^ (k * f) * C ^ (k * f)) * Xi s *
          (C * s * f) ^ (6 * s * f) * Γ * rD) *
        Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) := by
        gcongr
        all_goals first | assumption | positivity
    _ = Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C k m f s b g v Γ Xi * rD := by
        unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow
        ring
end Formalism.MainNotions.BridgeLemma₂
