-- Prove2me | solution 1 for P2M_Formalism_DworkPowerSeriesWeights_OneGauss_eval__frameJetOne_ed424e11227c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:13:46.51839+00:00
-- url     : https://prove2.me/submissions/3d3af93a-e78a-4f13-b820-344c42e5d1c8

import Definitions.Def_Formalism_GaussJetBounds_StatementU
import Definitions.Def_Formalism_GaussJetBounds_OneLetterRadius
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Labels
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneGauss
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_OneGauss_map_thetaOne
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_OneGauss_subst_thetaOne
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_OneGauss_sum_frA_row
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jet_pair_linearity
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_map_minorProd
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_ringMap_minorProd
import Theorems.Thm_P2M_Formalism_DworkPowerSeriesWeights_eval__jetPairPoly_5113198bcf9c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
open Formalism.DworkPowerSeriesWeights.OneGauss
namespace Formalism.DworkPowerSeriesWeights.OneGauss
theorem _root_.solution {F K : Type} [NormedField F] [CharZero F] [NormedField K] [CharZero K]
    (φ : F →+* K) {N0 N1 C : ℕ} (g : Fin N0 × Fin N1 → MvPowerSeries (Fin N0 × Fin N1) F)
    (hg : ∀ y, MvPowerSeries.constantCoeff (g y) = 0)
    (U : MvPowerSeries (Fin N0 × Fin N1) F) (sgn ep : F) (be : MvPowerSeries (ZMod 2) F)
    (hbe : MvPowerSeries.constantCoeff be = 0)
    (p : Fin C → ℕ) (hp : ∀ c, p c ≤ N0) (I : ∀ c, Fin (p c) → Fin N1)
    (Y : Fin N0 × Fin N0 → K) :
    MvPolynomial.eval₂ φ Y (frameJetOne p hp I (thetaOne g U sgn ep be)) =
      jetPair (minorProd (fun (i : Fin N0) (b : Fin N1) =>
          (MvPolynomial.X (i, b) : MvPolynomial (Fin N0 × Fin N1) K)) p hp I)
        (MvPowerSeries.subst
            (fun x : Fin N0 × Fin N1 => (∑ i : Fin N0 × Fin N1,
              MvPowerSeries.C (frA Y i x) * MvPowerSeries.X i :
                MvPowerSeries (Fin N0 × Fin N1) K))
            (MvPowerSeries.subst (fun y => MvPowerSeries.map φ (g y)) (MvPowerSeries.map φ U)) *
          _root_.Formalism.DworkPowerSeriesWeights.mvExp (expo (fun x : Fin N0 × Fin N1 => (∑ i : Fin N0 × Fin N1,
              MvPowerSeries.C (frA Y i x) * MvPowerSeries.X i :
                MvPowerSeries (Fin N0 × Fin N1) K)) (φ sgn) (φ ep) (MvPowerSeries.map φ be))) := by
  have hlin : MvPowerSeries.HasSubst (fun x : Fin N0 × Fin N1 =>
      (∑ i : Fin N0 × Fin N1, MvPowerSeries.C (frA Y i x) * MvPowerSeries.X i :
        MvPowerSeries (Fin N0 × Fin N1) K)) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro x
    simp
  have hbe' : MvPowerSeries.constantCoeff (MvPowerSeries.map φ be) = 0 := by
    simp [hbe]
  rw [← subst_thetaOne hlin _ _ _ _ _ hbe', ← map_thetaOne φ g hg U sgn ep be hbe,
    jet_pair_linearity K (Fin N0 × Fin N1) (Fin N0 × Fin N1) (frA Y)]
  unfold frameJetOne
  rw [eval₂_jetPairPoly, ringMap_minorProd, map_minorProd]
  congr 2
  funext i b
  rw [MvPolynomial.aeval_X, sum_frA_row]
  simp
end Formalism.DworkPowerSeriesWeights.OneGauss
