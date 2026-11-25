-- Prove2me | solution 1 for PI.FoldDCUnfold.W.foldDCUnfold_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:48:46.174814+00:00
-- url     : https://prove2.me/submissions/fae2aa79-6472-44a2-8031-7cbe385a7d83

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FoldDCUnfold
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FoldUnfold
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FoldingUnfolding_TransExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FoldingUnfolding_FoldDCUnfoldOf
import Theorems.Thm_PI_FoldDCUnfold_W_pointwise_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal
open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable
open PI PI.FoldDCUnfold PI.FoldDCUnfold.W
universe u
namespace PI.FoldDCUnfold.W
theorem _root_.solution (h0 : TransExists.{u}) (h1 : TransIndep.{u}) (h2 : TransProd.{u})
    (h3 : DCTrans.{u}) (hU : PI.FoldUnfold.FoldUnfold.{u}) : PI.FoldDCUnfold.FoldDCUnfold.{u} := by
  intro G _ _ _ μ _ Γ S S' _ hS hS' D D' hD hD' R hR Fs hFs FΓ hFΓ g h hgm hhm hg hh
  have hΓc : (Γ : Set G).Countable := Set.countable_coe_iff.mp (inferInstanceAs (Countable Γ))
  have hstabS : ∀ r : G, stab S S' r ≤ S := fun r => inf_le_left
  choose E hE using fun r : G => h0 G S (stab S S' r) (hstabS r)
  have hTP := fun r : G => h2 G Γ S (stab S S' r) (E r) D (hstabS r) hS (hE r) hD
  have hpt : ∀ x : G, (∑' δ : D, g ((δ : G) * x)) * (∑' δ' : D', h ((δ' : G) * x)) =
      ∑' r : R, ∑' η : Set.range (fun p : E (r : G) × D => (p.1 : G) * (p.2 : G)),
        g ((η : G) * x) * h ((r : G)⁻¹ * ((η : G) * x)) := by
    intro x
    rw [pointwise_of h1 h3 Γ S S' hS hS' D D' hD hD' R hR E (fun r _ => hE r) g h hg hh x]
    refine tsum_congr fun r => ?_
    have h2' : ∑' η : Set.range (fun p : E (r : G) × D => (p.1 : G) * (p.2 : G)),
        g ((η : G) * x) * h ((r : G)⁻¹ * ((η : G) * x)) =
        ∑' p : E (r : G) × D,
          g ((p.1 : G) * (p.2 : G) * x) * h ((r : G)⁻¹ * ((p.1 : G) * (p.2 : G) * x)) :=
      tsum_range (fun η : G => g (η * x) * h ((r : G)⁻¹ * (η * x))) (hTP (r : G)).1
    rw [h2']
  have hFm : ∀ r : G, Measurable (fun y : G => g y * h (r⁻¹ * y)) := fun r =>
    hgm.mul (hhm.comp (measurable_const_mul r⁻¹))
  have hinv : ∀ r : G, ∀ s ∈ stab S S' r, ∀ y : G,
      g (s * y) * h (r⁻¹ * (s * y)) = g y * h (r⁻¹ * y) := by
    intro r s hs y
    have hs2 := Subgroup.mem_inf.mp
      (show s ∈ S ⊓ S'.comap (MulAut.conj r⁻¹).toMonoidHom from hs)
    have hs' : r⁻¹ * s * r ∈ S' := by
      simpa [MulAut.conj_apply] using Subgroup.mem_comap.mp hs2.2
    rw [hg s hs2.1 y]
    congr 1
    calc h (r⁻¹ * (s * y)) = h ((r⁻¹ * s * r) * (r⁻¹ * y)) := by congr 1; group
      _ = h (r⁻¹ * y) := hh _ hs' _
  haveI : Countable R := (hΓc.mono hR.1).to_subtype
  simp_rw [hpt]
  rw [lintegral_tsum (fun r => ?_)]
  · refine tsum_congr fun r => ?_
    exact hU G μ Γ (stab S S' r) ((hstabS r).trans hS) (Fs r) (hFs r r.2) FΓ hFΓ _
      (hTP (r : G)).2 (fun y : G => g y * h ((r : G)⁻¹ * y)) (hFm r) (hinv r)
  · haveI : Countable (Set.range (fun p : E (r : G) × D => (p.1 : G) * (p.2 : G))) :=
      (hΓc.mono (hTP (r : G)).2.1).to_subtype
    exact (Measurable.ennreal_tsum fun η : Set.range (fun p : E (r : G) × D => (p.1 : G) * (p.2 : G)) =>
      (hFm (r : G)).comp (measurable_const_mul (η : G))).aemeasurable
end PI.FoldDCUnfold.W
