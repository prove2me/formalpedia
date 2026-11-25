-- Prove2me | solution 1 for P2M_CompanionTheory_RgExh_Hk_iso_sub__48260da7f134
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:56:46.953908+00:00
-- url     : https://prove2.me/submissions/35615068-fbfa-4a7d-bf4d-57981d832a0e

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_TensorReflections_PiIsoTensVd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.RgExh CompanionTheory.RgExh.Hk
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
variable {n : ℕ}
namespace CompanionTheory.RgExh.Hk
theorem _root_.solution {X X' : GMod n} (φ : X.V ≃ₗ[ℂ] X'.V) (hφ : ∀ a b x, φ (X.E a b x) = X'.E a b (φ x))
    (S : Submodule ℂ X.V) (S' : Submodule ℂ X'.V) (hS : S.map (φ : X.V →ₗ[ℂ] X'.V) = S')
    (h : ∀ a b, ∀ x ∈ S, X.E a b x ∈ S) (h' : ∀ a b, ∀ x ∈ S', X'.E a b x ∈ S') :
    Iso (X.sub S h) (X'.sub S' h') :=
  ⟨φ.ofSubmodules S S' hS, fun a b x => Subtype.ext (hφ a b x.1)⟩
end CompanionTheory.RgExh.Hk
