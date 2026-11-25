-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FourierCubeIntegral.cube_int_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:54:00.378505+00:00
-- url     : https://prove2.me/submissions/5322d70f-1a8b-4e37-9e82-9006b39e80cf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCubeVolume
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCubeIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCubeIntegral
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume
  MeasureTheory Set Filter
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.FD.FourierCubeIntegral
theorem _root_.solution {N : ℕ} (φ : (Fin N → ℝ) → ℂ) (hφ : Continuous φ)
    (hp : ∀ (n : Fin N → ℤ) t, φ (t + fun i => (n i : ℝ)) = φ t) (s : Fin N → ℝ) :
    ∫ t in cube N, φ (t + s) = ∫ t in cube N, φ t := by
  classical
  have hcube : cube N = Set.univ.pi fun _ : Fin N => Set.Icc (0 : ℝ) 1 := rfl
  let b := Pi.basisFun ℝ (Fin N)
  let L := (Submodule.span ℤ (Set.range b)).toAddSubgroup
  have hF : IsAddFundamentalDomain L (ZSpan.fundamentalDomain b) volume :=
    ZSpan.isAddFundamentalDomain b volume
  have key : ∀ g : L, ∃ n : Fin N → ℤ, (g : Fin N → ℝ) = fun i => (n i : ℝ) := fun g => by
    have hg := (b.mem_span_iff_repr_mem ℤ (g : Fin N → ℝ)).1 g.2
    choose n hn using hg
    exact ⟨n, funext fun i => by simpa [b] using (hn i).symm⟩
  haveI : Countable L := by
    choose f hf using key
    exact Function.Injective.countable (f := f) fun g₁ g₂ h => Subtype.ext (by rw [hf g₁, hf g₂, h])
  have hinv : ∀ g : L, ∀ x, φ (g +ᵥ x) = φ x := by
    intro g x
    obtain ⟨n, hgn⟩ := key g
    show φ ((g : Fin N → ℝ) + x) = φ x
    rw [hgn, add_comm]
    exact hp n x
  have hFs : IsAddFundamentalDomain L ((fun t => t - s) ⁻¹' ZSpan.fundamentalDomain b) volume :=
    hF.preimage_of_equiv (measurePreserving_sub_right volume s).quasiMeasurePreserving
      (e := id) Function.bijective_id fun g x => by
        show ((g : Fin N → ℝ) + x) - s = (g : Fin N → ℝ) + (x - s)
        exact add_sub_assoc _ _ _
  have hae : ZSpan.fundamentalDomain b =ᵐ[volume] cube N := by
    rw [ZSpan.fundamentalDomain_pi_basisFun, hcube, volume_pi]
    exact Measure.ae_eq_set_pi fun _ _ => Ico_ae_eq_Icc
  have hpre : (fun t => t + s) ⁻¹' ((fun t => t - s) ⁻¹' ZSpan.fundamentalDomain b) =
      ZSpan.fundamentalDomain b := by
    ext t
    simp
  calc ∫ t in cube N, φ (t + s) = ∫ t in ZSpan.fundamentalDomain b, φ (t + s) :=
        setIntegral_congr_set hae.symm
    _ = ∫ t in (fun t => t + s) ⁻¹' ((fun t => t - s) ⁻¹' ZSpan.fundamentalDomain b), φ (t + s) := by
        rw [hpre]
    _ = ∫ u in (fun t => t - s) ⁻¹' ZSpan.fundamentalDomain b, φ u :=
        (measurePreserving_add_right volume s).setIntegral_preimage_emb
          (MeasurableEquiv.addRight s).measurableEmbedding _ _
    _ = ∫ u in ZSpan.fundamentalDomain b, φ u := hFs.setIntegral_eq hF hinv
    _ = ∫ t in cube N, φ t := setIntegral_congr_set hae
end ReciprocityTheory.ChartRestriction.G.FD.FourierCubeIntegral
