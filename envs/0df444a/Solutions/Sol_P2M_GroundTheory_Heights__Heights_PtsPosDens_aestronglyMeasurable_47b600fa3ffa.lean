-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PtsPosDens_aestronglyMeasurable_47b600fa3ffa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:10:36.088282+00:00
-- url     : https://prove2.me/submissions/e85aa711-ac4e-4bc5-9219-e2c7422d7740

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsPosDensIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PtsSumMeasurableA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PtsPosDensMeasurable
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosDens_logNorm_ofWeight_one_3fa329d3fc08
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosDens_isSmoothHerm_ofWeight_2ba0524d484e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosDens_isSectionOn_ofWeight_one_21016dfaea94
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsDegZeroSmooth_mul_ac2f2d59f4e1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSumMeasurable_exists_lift_family_379c11db70cc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSumMeasurable_measurable_maDensity_55cc86a52e7c
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fibreFinite
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_sheetIndep


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo InnerProductSpace Laplacian
open GroundTheory.Heights₂.Heights.PtsPosDens
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.PtsPosDens
theorem _root_.solution {P : Ideal (MRing ι)} {e : ℕ}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {L : Fin e → HermLine ι}
    {g : ((Σ k, ι k) → ℂ) → ℝ} (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ)
    (hL : ∀ j, IsSmoothHerm (L j)) (hg : IsDegZeroSmooth g) :
    AEStronglyMeasurable (ptsPosDens P Ψ (pot L) g) := by
  classical
  have hfin := fibreFinite K ι P e Ψ hP hΨ
  obtain ⟨B, γ, hBo, hlift, hcov⟩ := PtsSumMeasurable.exists_lift_family (P := P) (Ψ := Ψ) hfin
  have hind := sheetIndep K ι P e Ψ L _ 1 hP hΨ hL (isSmoothHerm_ofWeight hg) (isSectionOn_ofWeight_one hP hg)
  rw [logNorm_ofWeight_one hg] at hind
  have hsheet : ∀ m, ∀ y ∈ B m, IsSheet P Ψ y (segre (γ m y)) (γ m) := fun m y hy =>
    ⟨rfl, Filter.eventually_of_mem ((hBo m).mem_nhds hy) fun y' hy' => hlift m y' hy'⟩
  have hγc : ∀ m, ContinuousOn (γ m) (B m) := fun m y hy =>
    (hlift m y hy).1.continuousAt.continuousWithinAt
  have hO : ∀ m, Set.MapsTo (γ m) (B m) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := fun m y hy =>
    (hlift m y hy).2.1.1
  have hseg : Continuous (segre : ((Σ k, ι k) → ℂ) → ((k : K) → ι k) → ℂ) :=
    continuous_pi fun i => continuous_finsetProd _ fun k _ => continuous_apply _
  set σ : ℕ → (Fin e → ℂ) → ((k : K) → ι k) → ℂ := fun m =>
    (B m).piecewise (fun y => segre (γ m y)) 0 with hσdef
  have hσB : ∀ m, ∀ y ∈ B m, σ m y = segre (γ m y) := fun m y hy =>
    Set.piecewise_eq_of_mem _ _ _ hy
  have hσm : ∀ m, Measurable (σ m) := fun m =>
    (hseg.comp_continuousOn (hγc m)).measurable_piecewise continuousOn_const (hBo m).measurableSet
  set a : ℕ → (Fin e → ℂ) → ℝ := fun m => (B m).piecewise (fun y => g (γ m y)) 0 with hadef
  have ham : ∀ m, Measurable (a m) := fun m =>
    (hg.1.continuousOn.comp (hγc m) (hO m)).measurable_piecewise continuousOn_const (hBo m).measurableSet
  set dens : ℕ → (Fin e → ℂ) → ℝ := fun m y =>
    max (a m y * maDensity (fun j y' => pot L j (γ m y')) y) 0 with hddef
  have hdm : ∀ m, Measurable (dens m) := fun m =>
    ((ham m).mul (PtsSumMeasurable.measurable_maDensity _)).max measurable_const
  have hdens : ∀ m, ∀ y ∈ B m,
      dens m y = max (g (γ m y) * maDensity (fun j y' => pot L j (γ m y')) y) 0 := by
    intro m y hy
    simp only [hddef, hadef, Set.piecewise_eq_of_mem _ _ _ hy]
  set S : ℕ → Set (Fin e → ℂ) := fun m =>
    {y | y ∈ B m ∧ ∀ m' < m, ¬ (y ∈ B m' ∧ σ m' y = σ m y)} with hSdef
  have hSm : ∀ m, MeasurableSet (S m) := by
    intro m
    have : S m = B m ∩ ⋂ m' ∈ Finset.range m, (B m' ∩ {y | σ m' y = σ m y})ᶜ := by
      ext y
      simp [hSdef]
    rw [this]
    exact (hBo m).measurableSet.inter (Finset.measurableSet_biInter _ fun m' _ =>
      ((hBo m').measurableSet.inter (measurableSet_eq_fun (hσm m') (hσm m))).compl)
  set f : ℕ → (Fin e → ℂ) → ℝ := fun m => (S m).indicator (dens m) with hfdef
  have hfm : ∀ m, Measurable (f m) := fun m => (hdm m).indicator (hSm m)
  have hpp : ptsPosDens P Ψ (pot L) g =
      fun y => ∑ᶠ w ∈ fibre P Ψ y, max (sheetDensity P Ψ (pot L) g y w) 0 := rfl
  rw [hpp]
  refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun N y => ∑ m ∈ Finset.range N, f m y)
    (fun N => (Finset.measurable_sum _ fun m _ => hfm m).aestronglyMeasurable) ?_
  filter_upwards [hind] with y hy
  have hterm : ∀ m, y ∈ S m → f m y = max (sheetDensity P Ψ (pot L) g y (σ m y)) 0 := by
    intro m hm
    have hsh := hsheet m y hm.1
    rw [← hσB m y hm.1] at hsh
    have hex : ∃ γ', IsSheet P Ψ y (σ m y) γ' := ⟨_, hsh⟩
    rw [hfdef]
    simp only
    rw [Set.indicator_of_mem hm, hdens m y hm.1]
    unfold sheetDensity
    rw [dif_pos hex]
    rw [hy _ _ _ hex.choose_spec hsh]
  have hmemF : ∀ m, y ∈ S m → σ m y ∈ (hfin y).toFinset := by
    intro m hm
    rw [Set.Finite.mem_toFinset, hσB m y hm.1]
    exact ⟨γ m y, (hlift m y hm.1).2.1, rfl, (hlift m y hm.1).2.2⟩
  have hfy : ∀ m, (∑ w ∈ (hfin y).toFinset, if σ m y = w then f m y else 0) = f m y := by
    intro m
    rw [Finset.sum_ite_eq]
    by_cases hm : y ∈ S m
    · rw [if_pos (hmemF m hm)]
    · split_ifs
      · rfl
      · rw [hfdef]
        simp only
        rw [Set.indicator_of_notMem hm]
  have hev : ∀ w ∈ (hfin y).toFinset, ∀ᶠ N in atTop,
      max (sheetDensity P Ψ (pot L) g y w) 0 =
        ∑ m ∈ Finset.range N, if σ m y = w then f m y else 0 := by
    intro w _
    by_cases hex : ∃ γ', IsSheet P Ψ y w γ'
    · obtain ⟨γ', hγ'⟩ := hex
      have hP' : ∃ m, y ∈ B m ∧ σ m y = w := by
        obtain ⟨m, hm, hmw⟩ := hcov y w γ' hγ'
        exact ⟨m, hm, (hσB m y hm).trans hmw⟩
      obtain ⟨hm1B, hm1w⟩ := Nat.find_spec hP'
      have hm1S : y ∈ S (Nat.find hP') :=
        ⟨hm1B, fun m' hm' h => Nat.find_min hP' hm' ⟨h.1, h.2.trans hm1w⟩⟩
      filter_upwards [eventually_gt_atTop (Nat.find hP')] with N hN
      rw [Finset.sum_eq_single_of_mem (Nat.find hP') (Finset.mem_range.2 hN), if_pos hm1w,
        hterm _ hm1S, hm1w]
      intro m _ hne
      split_ifs with hmw
      · by_cases hmS : y ∈ S m
        · exfalso
          have hle : Nat.find hP' ≤ m := Nat.find_min' hP' ⟨hmS.1, hmw⟩
          exact hmS.2 _ (lt_of_le_of_ne hle (Ne.symm hne)) ⟨hm1B, hm1w.trans hmw.symm⟩
        · rw [hfdef]
          simp only
          rw [Set.indicator_of_notMem hmS]
      · rfl
    · have h0 : sheetDensity P Ψ (pot L) g y w = 0 := by
        unfold sheetDensity
        rw [dif_neg hex]
      refine Eventually.of_forall fun N => ?_
      rw [h0, max_self]
      refine (Finset.sum_eq_zero fun m _ => ?_).symm
      split_ifs with hmw
      · by_cases hmS : y ∈ S m
        · have hsh := hsheet m y hmS.1
          rw [← hσB m y hmS.1, hmw] at hsh
          exact absurd ⟨_, hsh⟩ hex
        · rw [hfdef]
          simp only
          rw [Set.indicator_of_notMem hmS]
      · rfl
  have hsum : ∑ᶠ w ∈ fibre P Ψ y, max (sheetDensity P Ψ (pot L) g y w) 0 =
      ∑ w ∈ (hfin y).toFinset, max (sheetDensity P Ψ (pot L) g y w) 0 :=
    finsum_mem_eq_finite_toFinset_sum _ (hfin y)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [(eventually_all_finset _).2 hev] with N hN
  rw [hsum, Finset.sum_congr rfl hN, Finset.sum_comm]
  exact Finset.sum_congr rfl fun m _ => hfy m
end GroundTheory.Heights₂.Heights.PtsPosDens
