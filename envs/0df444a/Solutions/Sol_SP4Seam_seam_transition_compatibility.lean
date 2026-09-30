-- Prove2me | solution 1 for SP4Seam.seam_transition_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-07T07:01:35.11384+00:00
-- url     : https://prove2.me/submissions/2b91fd22-183e-47fc-9a34-e69f6e312122

import Mathlib
import Definitions.Def_SPC4DiskCharts
import Definitions.Def_SP4Gluing
import Definitions.Def_SP4PullbackCharts
import Definitions.Def_SP4SeamPullbackGroupoid
import Definitions.Def_SP4SeamDisk
import Definitions.Def_SP4SeamHemispherePart1
import Definitions.Def_SP4SeamHemispherePart2
import Definitions.Def_SP4SeamHemispherePart3


set_option autoImplicit false
namespace SP4Seam
open SP4Gluing SPC4Disk
open _root_.Homeomorph

section

open Set ChartedSpace

open scoped Manifold Topology

variable {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {N : Type*} [TopologicalSpace N]

namespace Homeomorph

@[simp, mfld_simps]
theorem pullbackChartedSpace_chartAt (e : N ≃ₜ M) (x : N) :
    @chartAt H _ N _ e.sp4MissionPullbackChartedSpace x =
      e.transOpenPartialHomeomorph (chartAt H (e x)) :=
  rfl

end Homeomorph

end

end SP4Seam


set_option autoImplicit false
namespace SP4Seam
open SP4Gluing SPC4Disk
open _root_.Homeomorph
open SP4Seam.Homeomorph

open Set Metric

open scoped ContDiff Manifold

section Hemisphere

variable {m : ℕ}

local instance seamFactFinrank :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

lemma contDiffOn_seamRadius {k : ℕ∞ω} :
    ContDiffOn ℝ k (fun w : EuclideanSpace ℝ (Fin (m + 1)) => 2 * (1 - ‖w‖))
      { w : EuclideanSpace ℝ (Fin (m + 1)) | w ≠ 0 } := by
  intro x hx
  have h1 : ContDiffAt ℝ k (norm : EuclideanSpace ℝ (Fin (m + 1)) → ℝ) x :=
    contDiffAt_norm (𝕜 := ℝ) hx
  have h2 : ContDiff ℝ k (fun r : ℝ => 2 * (1 - r)) :=
    contDiff_const.mul (contDiff_const.sub contDiff_id)
  exact (h2.contDiffAt.comp x h1).contDiffWithinAt

lemma regionChart_source_subset
    {φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1}
    {S : Set (TwistedSphere φ)} (hS : IsOpen S)
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) S] (x : S) :
    (regionChart hS x).source ⊆ S := by
  letI : Nonempty S := ⟨x⟩
  intro z hz
  rw [regionChart, OpenPartialHomeomorph.trans_source] at hz
  have h1 := hz.1
  simp only [OpenPartialHomeomorph.symm_source,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target] at h1
  rwa [Subtype.range_coe] at h1

lemma regionChart_interiorFst_apply
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (y z : interiorFst φ) :
    (regionChart (isOpen_interiorFst φ) y) (z : TwistedSphere φ) =
      (((interiorFstHomeo φ).symm z).val.val) := by
  let _ : Nonempty (interiorFst φ) := ⟨y⟩
  rw [regionChart, OpenPartialHomeomorph.trans_apply,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]
  rfl

lemma regionChart_interiorSnd_apply
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (y z : interiorSnd φ) :
    (regionChart (isOpen_interiorSnd φ) y) (z : TwistedSphere φ) =
      (((interiorSndHomeo φ).symm z).val.val) := by
  let _ : Nonempty (interiorSnd φ) := ⟨y⟩
  rw [regionChart, OpenPartialHomeomorph.trans_apply,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]
  rfl

lemma regionChart_symm_apply
    {φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1}
    {S : Set (TwistedSphere φ)} (hS : IsOpen S)
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) S] (x : S)
    (v : EuclideanSpace ℝ (Fin (m + 1))) :
    (regionChart hS x).symm v =
      (((chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).symm v : S) :
        TwistedSphere φ) := rfl

lemma seam_interiorFst_trans_apply
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (x : openSeam φ) (y : interiorFst φ)
    (v : EuclideanSpace ℝ (Fin (m + 1)))
    (h : (((chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).symm v : openSeam φ) :
      TwistedSphere φ) ∈ interiorFst φ) :
    ((regionChart (isOpen_openSeam φ) x).symm.trans
        (regionChart (isOpen_interiorFst φ) y)) v =
      (((interiorFstHomeo φ).symm ⟨_, h⟩).val.val) := by
  rw [OpenPartialHomeomorph.trans_apply, regionChart_symm_apply]
  exact regionChart_interiorFst_apply φ y ⟨_, h⟩

lemma seam_interiorSnd_trans_apply
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (x : openSeam φ) (y : interiorSnd φ)
    (v : EuclideanSpace ℝ (Fin (m + 1)))
    (h : (((chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).symm v : openSeam φ) :
      TwistedSphere φ) ∈ interiorSnd φ) :
    ((regionChart (isOpen_openSeam φ) x).symm.trans
        (regionChart (isOpen_interiorSnd φ) y)) v =
      (((interiorSndHomeo φ).symm ⟨_, h⟩).val.val) := by
  rw [OpenPartialHomeomorph.trans_apply, regionChart_symm_apply]
  exact regionChart_interiorSnd_apply φ y ⟨_, h⟩

lemma interiorFstHomeo_symm_val
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    {w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1}
    (h : (Quot.mk (GlueRel φ) (Sum.inl w) : TwistedSphere φ) ∈ interiorFst φ) :
    ((interiorFstHomeo φ).symm ⟨Quot.mk (GlueRel φ) (Sum.inl w), h⟩).val.val
      = w.val := by
  have hw : ‖w.val‖ < 1 := (mem_interiorFst_inl φ w).mp h
  have h2 : (interiorFstHomeo φ)
      (⟨w, hw⟩ : { w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 //
        ‖w.val‖ < 1 }) = ⟨Quot.mk (GlueRel φ) (Sum.inl w), h⟩ := Subtype.ext rfl
  rw [← h2, Homeomorph.symm_apply_apply]

lemma interiorSndHomeo_symm_val
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    {w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1}
    (h : (Quot.mk (GlueRel φ) (Sum.inr w) : TwistedSphere φ) ∈ interiorSnd φ) :
    ((interiorSndHomeo φ).symm ⟨Quot.mk (GlueRel φ) (Sum.inr w), h⟩).val.val
      = w.val := by
  have hw : ‖w.val‖ < 1 := (mem_interiorSnd_inr φ w).mp h
  have h2 : (interiorSndHomeo φ)
      (⟨w, hw⟩ : { w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 //
        ‖w.val‖ < 1 }) = ⟨Quot.mk (GlueRel φ) (Sum.inr w), h⟩ := Subtype.ext rfl
  rw [← h2, Homeomorph.symm_apply_apply]

lemma seam_interiorFst_trans_polar
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (x : openSeam φ) (y : interiorFst φ)
    (v : EuclideanSpace ℝ (Fin (m + 1)))
    (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × Set.Icc (-1 : ℝ) 1)
    (hp : 0 ≤ p.2.val)
    (hseam : (((chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).symm v : openSeam φ) :
      TwistedSphere φ) = Quot.mk (GlueRel φ) (Sum.inl (seamBallFst p)))
    (h : (((chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).symm v : openSeam φ) :
      TwistedSphere φ) ∈ interiorFst φ) :
    ((regionChart (isOpen_openSeam φ) x).symm.trans
        (regionChart (isOpen_interiorFst φ) y)) v =
      (1 - p.2.val / 2) • p.1.val := by
  rw [seam_interiorFst_trans_apply φ x y v h]
  have hmin : min 1 (1 - p.2.val / 2) = 1 - p.2.val / 2 :=
    min_eq_right (by have := p.2.2.2; linarith)
  have hval : ((interiorFstHomeo φ).symm
      ⟨(((chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).symm v : openSeam φ) :
        TwistedSphere φ), h⟩).val.val = (seamBallFst p).val := by
    have h' : (Quot.mk (GlueRel φ) (Sum.inl (seamBallFst p)) : TwistedSphere φ) ∈
        interiorFst φ := by rw [← hseam]; exact h
    have hpt : (⟨(((chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).symm v : openSeam φ) :
        TwistedSphere φ), h⟩ : interiorFst φ) =
        ⟨Quot.mk (GlueRel φ) (Sum.inl (seamBallFst p)), h'⟩ := Subtype.ext hseam
    rw [hpt]
    exact interiorFstHomeo_symm_val φ h' 
  rw [hval]
  show min 1 (1 - p.2.val / 2) • p.1.val = _
  rw [hmin]

lemma openSeam_val_eq_seamMap
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (q : openSeam φ) :
    (q : TwistedSphere φ) =
      seamMap φ (((seamHomeoIoo φ).symm q).1,
        ⟨((((seamHomeoIoo φ).symm q).2 : Set.Ioo (-1 : ℝ) 1) : ℝ),
          ⟨le_of_lt (((seamHomeoIoo φ).symm q).2).2.1,
            le_of_lt (((seamHomeoIoo φ).symm q).2).2.2⟩⟩) := by
  conv_lhs => rw [← (seamHomeoIoo φ).apply_symm_apply q]
  rfl

lemma openSeam_val_eq_inl
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (q : openSeam φ)
    (hq : 0 ≤ ((((seamHomeoIoo φ).symm q).2 : Set.Ioo (-1 : ℝ) 1) : ℝ)) :
    (q : TwistedSphere φ) =
      Quot.mk (GlueRel φ) (Sum.inl (seamBallFst
        (((seamHomeoIoo φ).symm q).1,
          ⟨((((seamHomeoIoo φ).symm q).2 : Set.Ioo (-1 : ℝ) 1) : ℝ),
            ⟨le_of_lt (((seamHomeoIoo φ).symm q).2).2.1,
              le_of_lt (((seamHomeoIoo φ).symm q).2).2.2⟩⟩))) := by
  rw [openSeam_val_eq_seamMap φ q,
    seamMap_of_nonneg φ (((seamHomeoIoo φ).symm q).1,
      ⟨((((seamHomeoIoo φ).symm q).2 : Set.Ioo (-1 : ℝ) 1) : ℝ),
        ⟨le_of_lt (((seamHomeoIoo φ).symm q).2).2.1,
          le_of_lt (((seamHomeoIoo φ).symm q).2).2.2⟩⟩) hq]

lemma openSeam_val_eq_inr
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (q : openSeam φ)
    (hq : ¬ (0 ≤ ((((seamHomeoIoo φ).symm q).2 : Set.Ioo (-1 : ℝ) 1) : ℝ))) :
    (q : TwistedSphere φ) =
      Quot.mk (GlueRel φ) (Sum.inr (seamBallSnd φ
        (((seamHomeoIoo φ).symm q).1,
          ⟨((((seamHomeoIoo φ).symm q).2 : Set.Ioo (-1 : ℝ) 1) : ℝ),
            ⟨le_of_lt (((seamHomeoIoo φ).symm q).2).2.1,
              le_of_lt (((seamHomeoIoo φ).symm q).2).2.2⟩⟩))) := by
  rw [openSeam_val_eq_seamMap φ q,
    seamMap_of_neg φ (((seamHomeoIoo φ).symm q).1,
      ⟨((((seamHomeoIoo φ).symm q).2 : Set.Ioo (-1 : ℝ) 1) : ℝ),
        ⟨le_of_lt (((seamHomeoIoo φ).symm q).2).2.1,
          le_of_lt (((seamHomeoIoo φ).symm q).2).2.2⟩⟩) hq]

lemma seam_interiorSnd_trans_polar
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (x : openSeam φ) (y : interiorSnd φ)
    (v : EuclideanSpace ℝ (Fin (m + 1)))
    (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × Set.Icc (-1 : ℝ) 1)
    (hp : p.2.val ≤ 0)
    (hseam : (((chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).symm v : openSeam φ) :
      TwistedSphere φ) = Quot.mk (GlueRel φ) (Sum.inr (seamBallSnd φ p)))
    (h : (((chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).symm v : openSeam φ) :
      TwistedSphere φ) ∈ interiorSnd φ) :
    ((regionChart (isOpen_openSeam φ) x).symm.trans
        (regionChart (isOpen_interiorSnd φ) y)) v =
      (1 + p.2.val / 2) • (φ p.1).val := by
  rw [seam_interiorSnd_trans_apply φ x y v h]
  have hmin : min 1 (1 + p.2.val / 2) = 1 + p.2.val / 2 :=
    min_eq_right (by linarith)
  have hval : ((interiorSndHomeo φ).symm
      ⟨(((chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).symm v : openSeam φ) :
        TwistedSphere φ), h⟩).val.val = (seamBallSnd φ p).val := by
    have h' : (Quot.mk (GlueRel φ) (Sum.inr (seamBallSnd φ p)) : TwistedSphere φ) ∈
        interiorSnd φ := by rw [← hseam]; exact h
    have hpt : (⟨(((chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).symm v : openSeam φ) :
        TwistedSphere φ), h⟩ : interiorSnd φ) =
        ⟨Quot.mk (GlueRel φ) (Sum.inr (seamBallSnd φ p)), h'⟩ := Subtype.ext hseam
    rw [hpt]
    exact interiorSndHomeo_symm_val φ h'
  rw [hval]
  show min 1 (1 + p.2.val / 2) • (φ p.1).val = _
  rw [hmin]

lemma contDiffOn_sphereChartSymm_val
    (u₀ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    ContDiffOn ℝ ∞ (fun a : EuclideanSpace ℝ (Fin m) =>
      (((chartAt (EuclideanSpace ℝ (Fin m)) u₀).symm a :
        sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1))))
      (chartAt (EuclideanSpace ℝ (Fin m)) u₀).target := by
  have h1 : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (𝓡 m) ∞
      (chartAt (EuclideanSpace ℝ (Fin m)) u₀).symm
      (chartAt (EuclideanSpace ℝ (Fin m)) u₀).target := contMDiffOn_chart_symm
  have h2 : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞
      (fun a => (((chartAt (EuclideanSpace ℝ (Fin m)) u₀).symm a :
        sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1))))
      (chartAt (EuclideanSpace ℝ (Fin m)) u₀).target :=
    contMDiff_coe_sphere.comp_contMDiffOn h1
  rwa [contMDiffOn_iff_contDiffOn] at h2

lemma contDiffOn_seamTransitionCoord
    (u₀ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    ContDiffOn ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (m + 1)) =>
      (1 - (((seamModelEquiv m).symm v).2) / 2) •
        (((chartAt (EuclideanSpace ℝ (Fin m)) u₀).symm
            (((seamModelEquiv m).symm v).1) :
          sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
            EuclideanSpace ℝ (Fin (m + 1))))
      ((fun v : EuclideanSpace ℝ (Fin (m + 1)) => ((seamModelEquiv m).symm v).1) ⁻¹'
        (chartAt (EuclideanSpace ℝ (Fin m)) u₀).target) := by
  have hlin : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (m + 1)) =>
      (seamModelEquiv m).symm v) := (seamModelEquiv m).symm.contDiff
  have hfst : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (m + 1)) =>
      ((seamModelEquiv m).symm v).1) := contDiff_fst.comp hlin
  have hsnd : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (m + 1)) =>
      ((seamModelEquiv m).symm v).2) := contDiff_snd.comp hlin
  have hscalar : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (m + 1)) =>
      1 - ((seamModelEquiv m).symm v).2 / 2) :=
    contDiff_const.sub (hsnd.div_const 2)
  exact hscalar.contDiffOn.smul
    ((contDiffOn_sphereChartSymm_val u₀).comp hfst.contDiffOn (fun v hv => hv))

lemma seamChart_symm_fst
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (x : openSeam φ) (v : EuclideanSpace ℝ (Fin (m + 1))) :
    ((seamHomeoIoo φ).symm
        ((chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).symm v)).1 =
      (chartAt (EuclideanSpace ℝ (Fin m)) ((seamHomeoIoo φ).symm x).1).symm
        (((seamModelEquiv m).symm v).1) := by
  have h : (seamHomeoIoo φ).symm
      ((chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).symm v) =
      (chartAt (EuclideanSpace ℝ (Fin (m + 1)))
        ((seamHomeoIoo φ).symm x)).symm v :=
    (seamHomeoIoo φ).symm_apply_apply _
  rw [h]
  rfl

lemma seamChart_symm_snd
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (x : openSeam φ) (v : EuclideanSpace ℝ (Fin (m + 1)))
    (hv : ((seamModelEquiv m).symm v).2 ∈ Set.Ioo (-1 : ℝ) 1) :
    (((((seamHomeoIoo φ).symm
        ((chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).symm v)).2 :
          Set.Ioo (-1 : ℝ) 1) : ℝ)) = ((seamModelEquiv m).symm v).2 := by
  have h : (seamHomeoIoo φ).symm
      ((chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).symm v) =
      (chartAt (EuclideanSpace ℝ (Fin (m + 1)))
        ((seamHomeoIoo φ).symm x)).symm v :=
    (seamHomeoIoo φ).symm_apply_apply _
  rw [h]
  exact Topology.IsOpenEmbedding.toOpenPartialHomeomorph_right_inv _
    isOpen_Ioo.isOpenEmbedding_subtypeVal (by rw [Subtype.range_coe]; exact hv)

lemma seam_interiorFst_trans_coord
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (x : openSeam φ) (y : interiorFst φ)
    (v : EuclideanSpace ℝ (Fin (m + 1)))
    (hv : ((seamModelEquiv m).symm v).2 ∈ Set.Ioo (-1 : ℝ) 1)
    (hq : 0 ≤ ((seamModelEquiv m).symm v).2)
    (h : (((chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).symm v : openSeam φ) :
      TwistedSphere φ) ∈ interiorFst φ) :
    ((regionChart (isOpen_openSeam φ) x).symm.trans
        (regionChart (isOpen_interiorFst φ) y)) v =
      (1 - ((seamModelEquiv m).symm v).2 / 2) •
        (((chartAt (EuclideanSpace ℝ (Fin m)) ((seamHomeoIoo φ).symm x).1).symm
            (((seamModelEquiv m).symm v).1) :
          sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
            EuclideanSpace ℝ (Fin (m + 1))) := by
  have hsnd : ((((seamHomeoIoo φ).symm
      ((chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).symm v)).2 :
        Set.Ioo (-1 : ℝ) 1) : ℝ) = ((seamModelEquiv m).symm v).2 :=
    seamChart_symm_snd φ x v hv
  have hfst : ((seamHomeoIoo φ).symm
      ((chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).symm v)).1 =
      (chartAt (EuclideanSpace ℝ (Fin m)) ((seamHomeoIoo φ).symm x).1).symm
        (((seamModelEquiv m).symm v).1) := seamChart_symm_fst φ x v
  have hq0 : 0 ≤ ((((seamHomeoIoo φ).symm
      ((chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).symm v)).2 :
        Set.Ioo (-1 : ℝ) 1) : ℝ) := by rw [hsnd]; exact hq
  have hinl := openSeam_val_eq_inl φ
    ((chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).symm v : openSeam φ) hq0
  have hfst' : ((((seamHomeo φ).symm
      ((chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).symm v)).val).1) =
      (chartAt (EuclideanSpace ℝ (Fin m)) ((seamHomeoIoo φ).symm x).1).symm
        (((seamModelEquiv m).symm v).1) := hfst
  have hsnd' : (((((seamHomeo φ).symm
      ((chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).symm v)).val).2 :
        Set.Icc (-1 : ℝ) 1) : ℝ) = ((seamModelEquiv m).symm v).2 := hsnd
  rw [seam_interiorFst_trans_polar φ x y v _ hq0 hinl h]
  congr 1
  · exact congrArg (fun r : ℝ => 1 - r / 2) hsnd
  · exact congrArg Subtype.val hfst'

lemma seam_nonneg_of_mem_interiorFst
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (q : openSeam φ) (h : (q : TwistedSphere φ) ∈ interiorFst φ) :
    0 ≤ ((((seamHomeoIoo φ).symm q).2 : Set.Ioo (-1 : ℝ) 1) : ℝ) := by
  by_contra hneg
  have hq := openSeam_val_eq_inr φ q hneg
  rw [hq] at h
  exact (mem_interiorFst_inr φ _).mp h

lemma seam_nonpos_of_mem_interiorSnd
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (q : openSeam φ) (h : (q : TwistedSphere φ) ∈ interiorSnd φ) :
    ¬ (0 < ((((seamHomeoIoo φ).symm q).2 : Set.Ioo (-1 : ℝ) 1) : ℝ)) := by
  intro hpos
  have hq := openSeam_val_eq_inl φ q (le_of_lt hpos)
  rw [hq] at h
  exact (mem_interiorSnd_inl φ _).mp h

lemma seam_interiorFst_trans_coord'
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (x : openSeam φ) (y : interiorFst φ)
    (v : EuclideanSpace ℝ (Fin (m + 1)))
    (hv : ((seamModelEquiv m).symm v).2 ∈ Set.Ioo (-1 : ℝ) 1)
    (h : (((chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).symm v : openSeam φ) :
      TwistedSphere φ) ∈ interiorFst φ) :
    ((regionChart (isOpen_openSeam φ) x).symm.trans
        (regionChart (isOpen_interiorFst φ) y)) v =
      (1 - ((seamModelEquiv m).symm v).2 / 2) •
        (((chartAt (EuclideanSpace ℝ (Fin m)) ((seamHomeoIoo φ).symm x).1).symm
            (((seamModelEquiv m).symm v).1) :
          sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
            EuclideanSpace ℝ (Fin (m + 1))) := by
  have hq : 0 ≤ ((seamModelEquiv m).symm v).2 := by
    have hnn := seam_nonneg_of_mem_interiorFst φ
      ((chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).symm v : openSeam φ) h
    rwa [seamChart_symm_snd φ x v hv] at hnn
  exact seam_interiorFst_trans_coord φ x y v hv hq h

lemma seamChartAt_apply
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (x q : openSeam φ) :
    (chartAt (EuclideanSpace ℝ (Fin (m + 1))) x) q =
      seamModelEquiv m
        ((chartAt (EuclideanSpace ℝ (Fin m)) ((seamHomeoIoo φ).symm x).1)
            (((seamHomeoIoo φ).symm q).1),
          ((((seamHomeoIoo φ).symm q).2 : Set.Ioo (-1 : ℝ) 1) : ℝ)) := rfl

lemma seamChart_target_snd_mem
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (x : openSeam φ) {v : EuclideanSpace ℝ (Fin (m + 1))}
    (hv : v ∈ (chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).target) :
    ((seamModelEquiv m).symm v).2 ∈ Set.Ioo (-1 : ℝ) 1 := by
  have h1 : (chartAt (EuclideanSpace ℝ (Fin (m + 1))) x)
      ((chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).symm v) = v :=
    (chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).right_inv hv
  rw [seamChartAt_apply] at h1
  rw [← h1, ContinuousLinearEquiv.symm_apply_apply]
  exact (((seamHomeoIoo φ).symm
    ((chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).symm v)).2).2

lemma regionChart_target_subset
    {φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1}
    {S : Set (TwistedSphere φ)} (hS : IsOpen S)
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) S] (x : S) :
    (regionChart hS x).target ⊆
      (chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).target := by
  letI : Nonempty S := ⟨x⟩
  rw [regionChart, OpenPartialHomeomorph.trans_target]
  exact Set.inter_subset_left

lemma seam_interiorFst_trans_hyps
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (x : openSeam φ) (y : interiorFst φ)
    {v : EuclideanSpace ℝ (Fin (m + 1))}
    (hv : v ∈ ((regionChart (isOpen_openSeam φ) x).symm.trans
      (regionChart (isOpen_interiorFst φ) y)).source) :
    ((seamModelEquiv m).symm v).2 ∈ Set.Ioo (-1 : ℝ) 1 ∧
      (((chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).symm v : openSeam φ) :
        TwistedSphere φ) ∈ interiorFst φ := by
  rw [OpenPartialHomeomorph.trans_source] at hv
  obtain ⟨hv1, hv2⟩ := hv
  rw [OpenPartialHomeomorph.symm_source] at hv1
  refine ⟨seamChart_target_snd_mem φ x (regionChart_target_subset _ x hv1), ?_⟩
  have := regionChart_source_subset (isOpen_interiorFst φ) y hv2
  rwa [regionChart_symm_apply] at this

lemma contDiffOn_seam_interiorFst_trans
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (x : openSeam φ) (y : interiorFst φ) :
    ContDiffOn ℝ ∞ ((regionChart (isOpen_openSeam φ) x).symm.trans
        (regionChart (isOpen_interiorFst φ) y))
      ((regionChart (isOpen_openSeam φ) x).symm.trans
        (regionChart (isOpen_interiorFst φ) y)).source := by
  have htarget : (chartAt (EuclideanSpace ℝ (Fin m))
      ((seamHomeoIoo φ).symm x).1).target = Set.univ :=
    stereographic'_target _
  refine ((contDiffOn_seamTransitionCoord ((seamHomeoIoo φ).symm x).1).mono
    ?_).congr ?_
  · intro v _
    simp only [Set.mem_preimage, htarget, Set.mem_univ]
  · intro v hv
    exact seam_interiorFst_trans_coord' φ x y v
      (seam_interiorFst_trans_hyps φ x y hv).1
      (seam_interiorFst_trans_hyps φ x y hv).2

lemma seamHomeoIoo_symm_inl
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    {w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1}
    (hw : 1 / 2 < ‖w.val‖)
    (h : (Quot.mk (GlueRel φ) (Sum.inl w) : TwistedSphere φ) ∈ openSeam φ) :
    (seamHomeoIoo φ).symm ⟨Quot.mk (GlueRel φ) (Sum.inl w), h⟩ =
      (unitOr diskNorth w.val,
        ⟨2 * (1 - ‖w.val‖),
          ⟨by have := mem_closedBall_zero_iff.mp w.2; linarith, by linarith⟩⟩) := by
  have hle : ‖w.val‖ ≤ 1 := mem_closedBall_zero_iff.mp w.2
  have hne : w.val ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hw; linarith
  have hforward : (seamHomeoIoo φ)
      ((unitOr diskNorth w.val,
        ⟨2 * (1 - ‖w.val‖), ⟨by linarith, by linarith⟩⟩) :
          sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × Set.Ioo (-1 : ℝ) 1) =
      ⟨Quot.mk (GlueRel φ) (Sum.inl w), h⟩ := by
    apply Subtype.ext
    show seamMap φ (unitOr diskNorth w.val,
      ⟨2 * (1 - ‖w.val‖), ⟨by linarith, by linarith⟩⟩) =
        Quot.mk (GlueRel φ) (Sum.inl w)
    rw [seamMap_of_nonneg φ _ (by simp only; linarith)]
    congr 1
    apply congrArg Sum.inl
    apply Subtype.ext
    show min 1 (1 - (2 * (1 - ‖w.val‖)) / 2) • (unitOr diskNorth w.val).val = w.val
    have hr : 1 - (2 * (1 - ‖w.val‖)) / 2 = ‖w.val‖ := by ring
    rw [hr, min_eq_right hle, smul_unitOr diskNorth hne]
  rw [← hforward, Homeomorph.symm_apply_apply]

lemma contDiffOn_seamTransitionCoordInv
    (u₀ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    ContDiffOn ℝ ∞ (fun w : EuclideanSpace ℝ (Fin (m + 1)) =>
        seamModelEquiv m
          ((OrthonormalBasis.fromOrthogonalSpanSingleton m
              (ne_zero_of_mem_unit_sphere (-u₀))).repr
            (stereoToFun (((-u₀) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
              EuclideanSpace ℝ (Fin (m + 1))) (‖w‖⁻¹ • w)),
            2 * (1 - ‖w‖)))
      { w : EuclideanSpace ℝ (Fin (m + 1)) | w ≠ 0 ∧
        innerSL ℝ (((-u₀) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1))) (‖w‖⁻¹ • w) ≠ (1 : ℝ) } := by
  have hang := contDiffOn_boundaryAngular u₀ (k := ∞)
  have hrad : ContDiffOn ℝ ∞ (fun w : EuclideanSpace ℝ (Fin (m + 1)) =>
      2 * (1 - ‖w‖))
      { w : EuclideanSpace ℝ (Fin (m + 1)) | w ≠ 0 ∧
        innerSL ℝ (((-u₀) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1))) (‖w‖⁻¹ • w) ≠ (1 : ℝ) } :=
    (contDiffOn_seamRadius (k := ∞)).mono (fun w hw => hw.1)
  exact ((seamModelEquiv m).contDiff).comp_contDiffOn (hang.prodMk hrad)

lemma interiorFstChart_symm_coe
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (y : interiorFst φ) {w : EuclideanSpace ℝ (Fin (m + 1))}
    (hw : w ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    (((chartAt (EuclideanSpace ℝ (Fin (m + 1))) y).symm w : interiorFst φ) :
      TwistedSphere φ) =
      Quot.mk (GlueRel φ) (Sum.inl
        ⟨w, mem_closedBall_zero_iff.mpr (le_of_lt (mem_ball_zero_iff.mp hw))⟩) := by
  have hball : (((Topology.IsOpenEmbedding.toOpenPartialHomeomorph
      (Subtype.val : Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 →
        EuclideanSpace ℝ (Fin (m + 1)))
      Metric.isOpen_ball.isOpenEmbedding_subtypeVal).symm w :
        Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1))) = w :=
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_right_inv _
      Metric.isOpen_ball.isOpenEmbedding_subtypeVal
      (by rw [Subtype.range_coe]; exact hw)
  exact congrArg
    (fun z : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 =>
      (Quot.mk (GlueRel φ) (Sum.inl z) : TwistedSphere φ))
    (Subtype.ext hball)

lemma seamHomeoIoo_symm_inl_fst
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    {w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1}
    (hw : 1 / 2 < ‖w.val‖)
    (h : (Quot.mk (GlueRel φ) (Sum.inl w) : TwistedSphere φ) ∈ openSeam φ) :
    ((seamHomeoIoo φ).symm ⟨Quot.mk (GlueRel φ) (Sum.inl w), h⟩).1 =
      unitOr diskNorth w.val :=
  congrArg Prod.fst (seamHomeoIoo_symm_inl φ hw h)

lemma seamHomeoIoo_symm_inl_snd
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    {w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1}
    (hw : 1 / 2 < ‖w.val‖)
    (h : (Quot.mk (GlueRel φ) (Sum.inl w) : TwistedSphere φ) ∈ openSeam φ) :
    ((((seamHomeoIoo φ).symm ⟨Quot.mk (GlueRel φ) (Sum.inl w), h⟩).2 :
      Set.Ioo (-1 : ℝ) 1) : ℝ) = 2 * (1 - ‖w.val‖) :=
  congrArg (fun p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ×
    Set.Ioo (-1 : ℝ) 1 => ((p.2 : Set.Ioo (-1 : ℝ) 1) : ℝ))
    (seamHomeoIoo_symm_inl φ hw h)

lemma seamChartAt_apply_inl
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (x : openSeam φ)
    {w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1}
    (hw2 : 1 / 2 < ‖w.val‖)
    (h : (Quot.mk (GlueRel φ) (Sum.inl w) : TwistedSphere φ) ∈ openSeam φ) :
    (chartAt (EuclideanSpace ℝ (Fin (m + 1))) x)
        (⟨Quot.mk (GlueRel φ) (Sum.inl w), h⟩ : openSeam φ) =
      seamModelEquiv m
        ((chartAt (EuclideanSpace ℝ (Fin m)) ((seamHomeoIoo φ).symm x).1)
            (unitOr diskNorth w.val), 2 * (1 - ‖w.val‖)) :=
  (seamChartAt_apply φ x _).trans
    (congrArg (seamModelEquiv m)
      (Prod.ext
        (congrArg (fun u : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 =>
          (chartAt (EuclideanSpace ℝ (Fin m)) ((seamHomeoIoo φ).symm x).1) u)
          (seamHomeoIoo_symm_inl_fst φ hw2 h))
        (seamHomeoIoo_symm_inl_snd φ hw2 h)))

lemma interiorFstChart_symm_coe'
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (y : interiorFst φ)
    {w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1} (hw : ‖w.val‖ < 1) :
    (((chartAt (EuclideanSpace ℝ (Fin (m + 1))) y).symm w.val : interiorFst φ) :
      TwistedSphere φ) = Quot.mk (GlueRel φ) (Sum.inl w) :=
  (interiorFstChart_symm_coe φ y (mem_ball_zero_iff.mpr hw)).trans
    (congrArg (fun z : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 =>
      (Quot.mk (GlueRel φ) (Sum.inl z) : TwistedSphere φ)) (Subtype.ext rfl))

lemma seam_interiorFst_trans_symm_coord
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (x : openSeam φ) (y : interiorFst φ)
    {w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1}
    (hw : ‖w.val‖ < 1) (hw2 : 1 / 2 < ‖w.val‖)
    (hmem : (Quot.mk (GlueRel φ) (Sum.inl w) : TwistedSphere φ) ∈ openSeam φ) :
    ((regionChart (isOpen_interiorFst φ) y).symm.trans
        (regionChart (isOpen_openSeam φ) x)) w.val =
      seamModelEquiv m
        ((chartAt (EuclideanSpace ℝ (Fin m)) ((seamHomeoIoo φ).symm x).1)
            (unitOr diskNorth w.val), 2 * (1 - ‖w.val‖)) := by
  letI : Nonempty (openSeam φ) := ⟨x⟩
  have hz := interiorFstChart_symm_coe' φ y hw
  have hmem2 : (((chartAt (EuclideanSpace ℝ (Fin (m + 1))) y).symm w.val :
      interiorFst φ) : TwistedSphere φ) ∈ openSeam φ := by
    rw [hz]; exact hmem
  have step1 : ((regionChart (isOpen_interiorFst φ) y).symm.trans
      (regionChart (isOpen_openSeam φ) x)) w.val =
      (chartAt (EuclideanSpace ℝ (Fin (m + 1))) x) (⟨_, hmem2⟩ : openSeam φ) := by
    rw [OpenPartialHomeomorph.trans_apply, regionChart_symm_apply, regionChart,
      OpenPartialHomeomorph.trans_apply]
    exact congrArg _
      (Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv
        (Subtype.val : openSeam φ → TwistedSphere φ)
        (isOpen_openSeam φ).isOpenEmbedding_subtypeVal
        (x := (⟨_, hmem2⟩ : openSeam φ)))
  have step2 : (chartAt (EuclideanSpace ℝ (Fin (m + 1))) x)
      (⟨_, hmem2⟩ : openSeam φ) =
      (chartAt (EuclideanSpace ℝ (Fin (m + 1))) x)
        (⟨Quot.mk (GlueRel φ) (Sum.inl w), hmem⟩ : openSeam φ) :=
    congrArg _ (Subtype.ext hz)
  exact step1.trans (step2.trans (seamChartAt_apply_inl φ x hw2 hmem))

lemma chartAt_unitOr_eq
    (u₀ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    {v : EuclideanSpace ℝ (Fin (m + 1))} (hv : v ≠ 0) :
    (chartAt (EuclideanSpace ℝ (Fin m)) u₀) (unitOr diskNorth v) =
      (OrthonormalBasis.fromOrthogonalSpanSingleton m
        (ne_zero_of_mem_unit_sphere (-u₀))).repr
        (stereoToFun (((-u₀) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1))) (‖v‖⁻¹ • v)) := by
  show (OrthonormalBasis.fromOrthogonalSpanSingleton m
      (ne_zero_of_mem_unit_sphere (-u₀))).repr
      (stereoToFun (((-u₀) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
        EuclideanSpace ℝ (Fin (m + 1))) ((unitOr diskNorth v).val)) = _
  rw [unitOr_val_of_ne diskNorth hv]

lemma seam_interiorFst_trans_symm_coord_explicit
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (x : openSeam φ) (y : interiorFst φ)
    {w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1}
    (hw : ‖w.val‖ < 1) (hw2 : 1 / 2 < ‖w.val‖)
    (hmem : (Quot.mk (GlueRel φ) (Sum.inl w) : TwistedSphere φ) ∈ openSeam φ) :
    ((regionChart (isOpen_interiorFst φ) y).symm.trans
        (regionChart (isOpen_openSeam φ) x)) w.val =
      seamModelEquiv m
        ((OrthonormalBasis.fromOrthogonalSpanSingleton m
            (ne_zero_of_mem_unit_sphere (-((seamHomeoIoo φ).symm x).1))).repr
          (stereoToFun (((-((seamHomeoIoo φ).symm x).1) :
              sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
            EuclideanSpace ℝ (Fin (m + 1))) (‖w.val‖⁻¹ • w.val)),
          2 * (1 - ‖w.val‖)) := by
  have hne : w.val ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hw2
    linarith
  exact (seam_interiorFst_trans_symm_coord φ x y hw hw2 hmem).trans
    (congrArg (seamModelEquiv m)
      (Prod.ext (chartAt_unitOr_eq ((seamHomeoIoo φ).symm x).1 hne) rfl))

lemma seamChart_source_angular
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (x q : openSeam φ)
    (hq : q ∈ (chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).source) :
    ((seamHomeoIoo φ).symm q).1 ∈
      (chartAt (EuclideanSpace ℝ (Fin m)) ((seamHomeoIoo φ).symm x).1).source := by
  have h1 : (seamHomeoIoo φ).symm q ∈
      (chartAt (EuclideanSpace ℝ (Fin (m + 1)))
        ((seamHomeoIoo φ).symm x)).source := by
    simpa [Homeomorph.pullbackChartedSpace_chartAt] using hq
  rw [chartAt_comp, OpenPartialHomeomorph.trans_source] at h1
  exact h1.1.1

lemma interiorFstChart_target
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (y : interiorFst φ) :
    (chartAt (EuclideanSpace ℝ (Fin (m + 1))) y).target =
      Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 := by
  simp only [Homeomorph.pullbackChartedSpace_chartAt,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target,
    Homeomorph.transOpenPartialHomeomorph_target, Subtype.range_coe]
  ext v
  simp [mem_ball_zero_iff]

lemma seam_interiorFst_trans_symm_basic
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (x : openSeam φ) (y : interiorFst φ)
    {v : EuclideanSpace ℝ (Fin (m + 1))}
    (hv : v ∈ ((regionChart (isOpen_interiorFst φ) y).symm.trans
      (regionChart (isOpen_openSeam φ) x)).source) :
    ‖v‖ < 1 ∧ (((chartAt (EuclideanSpace ℝ (Fin (m + 1))) y).symm v : interiorFst φ) :
      TwistedSphere φ) ∈ openSeam φ := by
  rw [OpenPartialHomeomorph.trans_source] at hv
  obtain ⟨hv1, hv2⟩ := hv
  rw [OpenPartialHomeomorph.symm_source] at hv1
  have hball : v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 := by
    rw [← interiorFstChart_target φ y]
    exact regionChart_target_subset _ y hv1
  refine ⟨mem_ball_zero_iff.mp hball, ?_⟩
  have := regionChart_source_subset (isOpen_openSeam φ) x hv2
  rwa [regionChart_symm_apply] at this

lemma seam_interiorFst_trans_symm_norm
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (x : openSeam φ) (y : interiorFst φ)
    {v : EuclideanSpace ℝ (Fin (m + 1))}
    (hv : v ∈ ((regionChart (isOpen_interiorFst φ) y).symm.trans
      (regionChart (isOpen_openSeam φ) x)).source) :
    1 / 2 < ‖v‖ := by
  obtain ⟨hlt, hmem⟩ := seam_interiorFst_trans_symm_basic φ x y hv
  have hball : v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 :=
    mem_ball_zero_iff.mpr hlt
  have heq := interiorFstChart_symm_coe φ y hball
  have hmem2 : (Quot.mk (GlueRel φ) (Sum.inl
      ⟨v, mem_closedBall_zero_iff.mpr (le_of_lt (mem_ball_zero_iff.mp hball))⟩) :
        TwistedSphere φ) ∈ openSeam φ := heq ▸ hmem
  exact (mem_openSeam_inl φ
    ⟨v, mem_closedBall_zero_iff.mpr (le_of_lt (mem_ball_zero_iff.mp hball))⟩).mp hmem2

lemma regionChart_source_chart
    {φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1}
    {S : Set (TwistedSphere φ)} (hS : IsOpen S)
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) S] (x : S) {z : S}
    (hz : (z : TwistedSphere φ) ∈ (regionChart hS x).source) :
    z ∈ (chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).source := by
  letI : Nonempty S := ⟨x⟩
  rw [regionChart, OpenPartialHomeomorph.trans_source] at hz
  have h2 := hz.2
  rw [Set.mem_preimage] at h2
  have hinv : (Topology.IsOpenEmbedding.toOpenPartialHomeomorph
      (Subtype.val : S → TwistedSphere φ)
      hS.isOpenEmbedding_subtypeVal).symm ((z : TwistedSphere φ)) = z :=
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv
      (Subtype.val : S → TwistedSphere φ) hS.isOpenEmbedding_subtypeVal (x := z)
  exact hinv ▸ h2

lemma unitOr_congr_base
    (p q : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    {v : EuclideanSpace ℝ (Fin (m + 1))} (hv : v ≠ 0) :
    unitOr p v = unitOr q v := by
  apply Subtype.ext
  rw [unitOr_val_of_ne p hv, unitOr_val_of_ne q hv]

lemma sphereChart_source (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    (chartAt (EuclideanSpace ℝ (Fin m)) p).source = {-p}ᶜ :=
  stereographic'_source _

lemma seamChart_source_angular_inl
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (x : openSeam φ)
    {w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1}
    (hw2 : 1 / 2 < ‖w.val‖)
    (h : (Quot.mk (GlueRel φ) (Sum.inl w) : TwistedSphere φ) ∈ openSeam φ)
    (hsrc : (⟨Quot.mk (GlueRel φ) (Sum.inl w), h⟩ : openSeam φ) ∈
      (chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).source) :
    unitOr diskNorth w.val ≠ -((seamHomeoIoo φ).symm x).1 := by
  have hang := seamChart_source_angular φ x _ hsrc
  rw [seamHomeoIoo_symm_inl_fst φ hw2 h, sphereChart_source] at hang
  exact hang

lemma inner_ne_one_of_unitOr_ne
    (u₀ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    {v : EuclideanSpace ℝ (Fin (m + 1))} (hne : v ≠ 0)
    (h : unitOr diskNorth v ≠ -u₀) :
    innerSL ℝ (((-u₀) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
      EuclideanSpace ℝ (Fin (m + 1))) (‖v‖⁻¹ • v) ≠ (1 : ℝ) := by
  refine inner_unit_ne_one _ hne ?_
  rw [unitOr_congr_base u₀ diskNorth hne]
  exact h

lemma seamChart_source_angular_of_eq
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (x q : openSeam φ)
    {w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1}
    (heq : (q : TwistedSphere φ) = Quot.mk (GlueRel φ) (Sum.inl w))
    (hw2 : 1 / 2 < ‖w.val‖)
    (hsrc : q ∈ (chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).source) :
    unitOr diskNorth w.val ≠ -((seamHomeoIoo φ).symm x).1 := by
  have hmem : (Quot.mk (GlueRel φ) (Sum.inl w) : TwistedSphere φ) ∈ openSeam φ :=
    heq ▸ q.2
  have hq : q = ⟨Quot.mk (GlueRel φ) (Sum.inl w), hmem⟩ := Subtype.ext heq
  exact seamChart_source_angular_inl φ x hw2 hmem (hq ▸ hsrc)

lemma seam_interiorFst_trans_symm_angular
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (x : openSeam φ) (y : interiorFst φ)
    {v : EuclideanSpace ℝ (Fin (m + 1))}
    (hv : v ∈ ((regionChart (isOpen_interiorFst φ) y).symm.trans
      (regionChart (isOpen_openSeam φ) x)).source) :
    innerSL ℝ (((-((seamHomeoIoo φ).symm x).1) :
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
        EuclideanSpace ℝ (Fin (m + 1))) (‖v‖⁻¹ • v) ≠ (1 : ℝ) := by
  obtain ⟨hlt, hmemseam⟩ := seam_interiorFst_trans_symm_basic φ x y hv
  have hnorm := seam_interiorFst_trans_symm_norm φ x y hv
  have hne : v ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnorm
    linarith
  have hball : v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 :=
    mem_ball_zero_iff.mpr hlt
  have hv2 : ((regionChart (isOpen_interiorFst φ) y).symm v) ∈
      (regionChart (isOpen_openSeam φ) x).source := by
    rw [OpenPartialHomeomorph.trans_source] at hv
    exact hv.2
  have hsrc : (⟨_, hmemseam⟩ : openSeam φ) ∈
      (chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).source :=
    regionChart_source_chart (isOpen_openSeam φ) x hv2
  exact inner_ne_one_of_unitOr_ne _ hne
    (seamChart_source_angular_of_eq φ x ⟨_, hmemseam⟩
      (interiorFstChart_symm_coe φ y hball) hnorm hsrc)

lemma seam_interiorFst_trans_symm_coord_of_val
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (x : openSeam φ) (y : interiorFst φ)
    {w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1}
    {v : EuclideanSpace ℝ (Fin (m + 1))} (hval : w.val = v)
    (hw : ‖w.val‖ < 1) (hw2 : 1 / 2 < ‖w.val‖)
    (hmem : (Quot.mk (GlueRel φ) (Sum.inl w) : TwistedSphere φ) ∈ openSeam φ) :
    ((regionChart (isOpen_interiorFst φ) y).symm.trans
        (regionChart (isOpen_openSeam φ) x)) v =
      seamModelEquiv m
        ((OrthonormalBasis.fromOrthogonalSpanSingleton m
            (ne_zero_of_mem_unit_sphere (-((seamHomeoIoo φ).symm x).1))).repr
          (stereoToFun (((-((seamHomeoIoo φ).symm x).1) :
              sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
            EuclideanSpace ℝ (Fin (m + 1))) (‖v‖⁻¹ • v)),
          2 * (1 - ‖v‖)) := by
  subst hval
  exact seam_interiorFst_trans_symm_coord_explicit φ x y hw hw2 hmem

lemma contDiffOn_seam_interiorFst_trans_symm
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (x : openSeam φ) (y : interiorFst φ) :
    ContDiffOn ℝ ∞ ((regionChart (isOpen_interiorFst φ) y).symm.trans
        (regionChart (isOpen_openSeam φ) x))
      ((regionChart (isOpen_interiorFst φ) y).symm.trans
        (regionChart (isOpen_openSeam φ) x)).source := by
  refine ((contDiffOn_seamTransitionCoordInv
    ((seamHomeoIoo φ).symm x).1).mono ?_).congr ?_
  · intro v hv
    have hnorm := seam_interiorFst_trans_symm_norm φ x y hv
    refine ⟨?_, seam_interiorFst_trans_symm_angular φ x y hv⟩
    intro h0
    rw [h0, norm_zero] at hnorm
    linarith
  · intro v hv
    obtain ⟨hlt, hmemseam⟩ := seam_interiorFst_trans_symm_basic φ x y hv
    have hnorm := seam_interiorFst_trans_symm_norm φ x y hv
    have hball : v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 :=
      mem_ball_zero_iff.mpr hlt
    have hmem' : (Quot.mk (GlueRel φ) (Sum.inl
        ⟨v, mem_closedBall_zero_iff.mpr (le_of_lt (mem_ball_zero_iff.mp hball))⟩) :
          TwistedSphere φ) ∈ openSeam φ :=
      (interiorFstChart_symm_coe φ y hball) ▸ hmemseam
    exact seam_interiorFst_trans_symm_coord_of_val φ x y
      (w := ⟨v, mem_closedBall_zero_iff.mpr (le_of_lt (mem_ball_zero_iff.mp hball))⟩)
      rfl hlt hnorm hmem'

lemma seamHomeoIoo_symm_inr
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    {w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1}
    (hw : 1 / 2 < ‖w.val‖) (hw1 : ‖w.val‖ < 1)
    (h : (Quot.mk (GlueRel φ) (Sum.inr w) : TwistedSphere φ) ∈ openSeam φ) :
    (seamHomeoIoo φ).symm ⟨Quot.mk (GlueRel φ) (Sum.inr w), h⟩ =
      (φ.symm (unitOr diskNorth w.val),
        ⟨-(2 * (1 - ‖w.val‖)), ⟨by linarith, by linarith⟩⟩) := by
  have hne : w.val ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hw
    linarith
  have hforward : (seamHomeoIoo φ)
      ((φ.symm (unitOr diskNorth w.val),
        ⟨-(2 * (1 - ‖w.val‖)), ⟨by linarith, by linarith⟩⟩) :
          sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × Set.Ioo (-1 : ℝ) 1) =
      ⟨Quot.mk (GlueRel φ) (Sum.inr w), h⟩ := by
    apply Subtype.ext
    show seamMap φ (φ.symm (unitOr diskNorth w.val),
      ⟨-(2 * (1 - ‖w.val‖)), ⟨by linarith, by linarith⟩⟩) =
        Quot.mk (GlueRel φ) (Sum.inr w)
    rw [seamMap_of_neg φ _ (by simp only; push_neg; linarith)]
    congr 1
    apply congrArg Sum.inr
    apply Subtype.ext
    show min 1 (1 + -(2 * (1 - ‖w.val‖)) / 2) •
      (φ (φ.symm (unitOr diskNorth w.val))).val = w.val
    rw [Homeomorph.apply_symm_apply]
    have hr : 1 + -(2 * (1 - ‖w.val‖)) / 2 = ‖w.val‖ := by ring
    rw [hr, min_eq_right (le_of_lt hw1), smul_unitOr diskNorth hne]
  rw [← hforward, Homeomorph.symm_apply_apply]

lemma seamHomeoIoo_symm_inr_fst
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    {w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1}
    (hw : 1 / 2 < ‖w.val‖) (hw1 : ‖w.val‖ < 1)
    (h : (Quot.mk (GlueRel φ) (Sum.inr w) : TwistedSphere φ) ∈ openSeam φ) :
    ((seamHomeoIoo φ).symm ⟨Quot.mk (GlueRel φ) (Sum.inr w), h⟩).1 =
      φ.symm (unitOr diskNorth w.val) :=
  congrArg Prod.fst (seamHomeoIoo_symm_inr φ hw hw1 h)

lemma seamHomeoIoo_symm_inr_snd
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    {w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1}
    (hw : 1 / 2 < ‖w.val‖) (hw1 : ‖w.val‖ < 1)
    (h : (Quot.mk (GlueRel φ) (Sum.inr w) : TwistedSphere φ) ∈ openSeam φ) :
    ((((seamHomeoIoo φ).symm ⟨Quot.mk (GlueRel φ) (Sum.inr w), h⟩).2 :
      Set.Ioo (-1 : ℝ) 1) : ℝ) = -(2 * (1 - ‖w.val‖)) :=
  congrArg (fun p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ×
    Set.Ioo (-1 : ℝ) 1 => ((p.2 : Set.Ioo (-1 : ℝ) 1) : ℝ))
    (seamHomeoIoo_symm_inr φ hw hw1 h)

lemma seamChartAt_apply_inr
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (x : openSeam φ)
    {w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1}
    (hw : 1 / 2 < ‖w.val‖) (hw1 : ‖w.val‖ < 1)
    (h : (Quot.mk (GlueRel φ) (Sum.inr w) : TwistedSphere φ) ∈ openSeam φ) :
    (chartAt (EuclideanSpace ℝ (Fin (m + 1))) x)
        (⟨Quot.mk (GlueRel φ) (Sum.inr w), h⟩ : openSeam φ) =
      seamModelEquiv m
        ((chartAt (EuclideanSpace ℝ (Fin m)) ((seamHomeoIoo φ).symm x).1)
            (φ.symm (unitOr diskNorth w.val)), -(2 * (1 - ‖w.val‖))) :=
  (seamChartAt_apply φ x _).trans
    (congrArg (seamModelEquiv m)
      (Prod.ext
        (congrArg (fun u : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 =>
          (chartAt (EuclideanSpace ℝ (Fin m)) ((seamHomeoIoo φ).symm x).1) u)
          (seamHomeoIoo_symm_inr_fst φ hw hw1 h))
        (seamHomeoIoo_symm_inr_snd φ hw hw1 h)))

lemma interiorSndChart_symm_coe
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (y : interiorSnd φ) {w : EuclideanSpace ℝ (Fin (m + 1))}
    (hw : w ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    (((chartAt (EuclideanSpace ℝ (Fin (m + 1))) y).symm w : interiorSnd φ) :
      TwistedSphere φ) =
      Quot.mk (GlueRel φ) (Sum.inr
        ⟨w, mem_closedBall_zero_iff.mpr (le_of_lt (mem_ball_zero_iff.mp hw))⟩) := by
  have hball : (((Topology.IsOpenEmbedding.toOpenPartialHomeomorph
      (Subtype.val : Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 →
        EuclideanSpace ℝ (Fin (m + 1)))
      Metric.isOpen_ball.isOpenEmbedding_subtypeVal).symm w :
        Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1))) = w :=
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_right_inv _
      Metric.isOpen_ball.isOpenEmbedding_subtypeVal
      (by rw [Subtype.range_coe]; exact hw)
  exact congrArg
    (fun z : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 =>
      (Quot.mk (GlueRel φ) (Sum.inr z) : TwistedSphere φ))
    (Subtype.ext hball)

lemma interiorSndChart_target
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (y : interiorSnd φ) :
    (chartAt (EuclideanSpace ℝ (Fin (m + 1))) y).target =
      Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 := by
  simp only [Homeomorph.pullbackChartedSpace_chartAt,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target,
    Homeomorph.transOpenPartialHomeomorph_target, Subtype.range_coe]
  ext v
  simp [mem_ball_zero_iff]

lemma interiorSndChart_symm_coe'
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (y : interiorSnd φ)
    {w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1} (hw : ‖w.val‖ < 1) :
    (((chartAt (EuclideanSpace ℝ (Fin (m + 1))) y).symm w.val : interiorSnd φ) :
      TwistedSphere φ) = Quot.mk (GlueRel φ) (Sum.inr w) :=
  (interiorSndChart_symm_coe φ y (mem_ball_zero_iff.mpr hw)).trans
    (congrArg (fun z : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 =>
      (Quot.mk (GlueRel φ) (Sum.inr z) : TwistedSphere φ)) (Subtype.ext rfl))

lemma seam_interiorSnd_trans_symm_coord
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (x : openSeam φ) (y : interiorSnd φ)
    {w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1}
    (hw : ‖w.val‖ < 1) (hw2 : 1 / 2 < ‖w.val‖)
    (hmem : (Quot.mk (GlueRel φ) (Sum.inr w) : TwistedSphere φ) ∈ openSeam φ) :
    ((regionChart (isOpen_interiorSnd φ) y).symm.trans
        (regionChart (isOpen_openSeam φ) x)) w.val =
      seamModelEquiv m
        ((chartAt (EuclideanSpace ℝ (Fin m)) ((seamHomeoIoo φ).symm x).1)
            (φ.symm (unitOr diskNorth w.val)), -(2 * (1 - ‖w.val‖))) := by
  letI : Nonempty (openSeam φ) := ⟨x⟩
  have hz := interiorSndChart_symm_coe' φ y hw
  have hmem2 : (((chartAt (EuclideanSpace ℝ (Fin (m + 1))) y).symm w.val :
      interiorSnd φ) : TwistedSphere φ) ∈ openSeam φ := by
    rw [hz]; exact hmem
  have step1 : ((regionChart (isOpen_interiorSnd φ) y).symm.trans
      (regionChart (isOpen_openSeam φ) x)) w.val =
      (chartAt (EuclideanSpace ℝ (Fin (m + 1))) x) (⟨_, hmem2⟩ : openSeam φ) := by
    rw [OpenPartialHomeomorph.trans_apply, regionChart_symm_apply, regionChart,
      OpenPartialHomeomorph.trans_apply]
    exact congrArg _
      (Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv
        (Subtype.val : openSeam φ → TwistedSphere φ)
        (isOpen_openSeam φ).isOpenEmbedding_subtypeVal
        (x := (⟨_, hmem2⟩ : openSeam φ)))
  have step2 : (chartAt (EuclideanSpace ℝ (Fin (m + 1))) x)
      (⟨_, hmem2⟩ : openSeam φ) =
      (chartAt (EuclideanSpace ℝ (Fin (m + 1))) x)
        (⟨Quot.mk (GlueRel φ) (Sum.inr w), hmem⟩ : openSeam φ) :=
    congrArg _ (Subtype.ext hz)
  exact step1.trans (step2.trans (seamChartAt_apply_inr φ x hw2 hw hmem))

lemma contMDiff_unitOr_punctured :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) (𝓡 m) ∞
      (fun w : puncturedOpens m =>
        unitOr diskNorth w.val) := by
  have houter : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞
      (fun x : EuclideanSpace ℝ (Fin (m + 1)) => ‖x‖⁻¹ • x)
      {x : EuclideanSpace ℝ (Fin (m + 1)) | x ≠ 0} :=
    contMDiffOn_iff_contDiffOn.mpr contDiffOn_unitVector
  have hval : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞
      (fun w : puncturedOpens m => ‖w.val‖⁻¹ • w.val) :=
    houter.comp_contMDiff contMDiff_subtype_val (fun w => w.2)
  have hnorm : ∀ w : puncturedOpens m,
      ‖w.val‖⁻¹ • w.val ∈ sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 := by
    intro w
    have hpos : 0 < ‖w.val‖ := norm_pos_iff.mpr w.2
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ (ne_of_gt hpos)]
  refine (hval.codRestrict_sphere hnorm).congr ?_
  intro w
  apply Subtype.ext
  rw [unitOr_val_of_ne diskNorth w.2]
  rfl

lemma contMDiffOn_unitOr :
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) (𝓡 m) ∞
      (fun w : EuclideanSpace ℝ (Fin (m + 1)) => unitOr diskNorth w)
      {w : EuclideanSpace ℝ (Fin (m + 1)) | w ≠ 0} := by
  intro x hx
  have hx' : x ∈ (puncturedOpens m : Set (EuclideanSpace ℝ (Fin (m + 1)))) := hx
  have hsub := (contMDiff_unitOr_punctured (m := m)) ⟨x, hx'⟩
  rw [contMDiffAt_subtype_iff] at hsub
  exact hsub.contMDiffWithinAt

lemma contDiffOn_seamAngleTwisted
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (hφ : ContMDiff (𝓡 m) (𝓡 m) ∞ φ.symm)
    (u₀ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    ContDiffOn ℝ ∞
      (fun w : EuclideanSpace ℝ (Fin (m + 1)) =>
        (chartAt (EuclideanSpace ℝ (Fin m)) u₀) (φ.symm (unitOr diskNorth w)))
      ({w : EuclideanSpace ℝ (Fin (m + 1)) | w ≠ 0} ∩
        (fun w : EuclideanSpace ℝ (Fin (m + 1)) => φ.symm (unitOr diskNorth w)) ⁻¹'
          (chartAt (EuclideanSpace ℝ (Fin m)) u₀).source) := by
  have h1 : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) (𝓡 m) ∞
      (fun w : EuclideanSpace ℝ (Fin (m + 1)) => φ.symm (unitOr diskNorth w))
      ({w : EuclideanSpace ℝ (Fin (m + 1)) | w ≠ 0} ∩
        (fun w : EuclideanSpace ℝ (Fin (m + 1)) => φ.symm (unitOr diskNorth w)) ⁻¹'
          (chartAt (EuclideanSpace ℝ (Fin m)) u₀).source) :=
    hφ.comp_contMDiffOn (contMDiffOn_unitOr.mono Set.inter_subset_left)
  have h2 := (contMDiffOn_chart (I := 𝓡 m) (x := u₀)).comp h1 (fun w hw => hw.2)
  rwa [contMDiffOn_iff_contDiffOn] at h2

lemma contDiffOn_seamTransitionCoordInvTwisted
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (hφ : ContMDiff (𝓡 m) (𝓡 m) ∞ φ.symm)
    (u₀ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    ContDiffOn ℝ ∞
      (fun w : EuclideanSpace ℝ (Fin (m + 1)) =>
        seamModelEquiv m
          ((chartAt (EuclideanSpace ℝ (Fin m)) u₀) (φ.symm (unitOr diskNorth w)),
            -(2 * (1 - ‖w‖))))
      ({w : EuclideanSpace ℝ (Fin (m + 1)) | w ≠ 0} ∩
        (fun w : EuclideanSpace ℝ (Fin (m + 1)) => φ.symm (unitOr diskNorth w)) ⁻¹'
          (chartAt (EuclideanSpace ℝ (Fin m)) u₀).source) := by
  have hrad : ContDiffOn ℝ ∞
      (fun w : EuclideanSpace ℝ (Fin (m + 1)) => -(2 * (1 - ‖w‖)))
      ({w : EuclideanSpace ℝ (Fin (m + 1)) | w ≠ 0} ∩
        (fun w : EuclideanSpace ℝ (Fin (m + 1)) => φ.symm (unitOr diskNorth w)) ⁻¹'
          (chartAt (EuclideanSpace ℝ (Fin m)) u₀).source) :=
    ((contDiffOn_seamRadius (k := ∞)).mono Set.inter_subset_left).neg
  exact ((seamModelEquiv m).contDiff).comp_contDiffOn
    ((contDiffOn_seamAngleTwisted φ hφ u₀).prodMk hrad)

lemma seam_interiorSnd_trans_symm_basic
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (x : openSeam φ) (y : interiorSnd φ)
    {v : EuclideanSpace ℝ (Fin (m + 1))}
    (hv : v ∈ ((regionChart (isOpen_interiorSnd φ) y).symm.trans
      (regionChart (isOpen_openSeam φ) x)).source) :
    ‖v‖ < 1 ∧ (((chartAt (EuclideanSpace ℝ (Fin (m + 1))) y).symm v : interiorSnd φ) :
      TwistedSphere φ) ∈ openSeam φ := by
  rw [OpenPartialHomeomorph.trans_source] at hv
  obtain ⟨hv1, hv2⟩ := hv
  rw [OpenPartialHomeomorph.symm_source] at hv1
  have hball : v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 := by
    rw [← interiorSndChart_target φ y]
    exact regionChart_target_subset _ y hv1
  refine ⟨mem_ball_zero_iff.mp hball, ?_⟩
  have := regionChart_source_subset (isOpen_openSeam φ) x hv2
  rwa [regionChart_symm_apply] at this

lemma seam_interiorSnd_trans_symm_norm
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (x : openSeam φ) (y : interiorSnd φ)
    {v : EuclideanSpace ℝ (Fin (m + 1))}
    (hv : v ∈ ((regionChart (isOpen_interiorSnd φ) y).symm.trans
      (regionChart (isOpen_openSeam φ) x)).source) :
    1 / 2 < ‖v‖ := by
  obtain ⟨hlt, hmem⟩ := seam_interiorSnd_trans_symm_basic φ x y hv
  have hball : v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 :=
    mem_ball_zero_iff.mpr hlt
  have heq := interiorSndChart_symm_coe φ y hball
  have hmem2 : (Quot.mk (GlueRel φ) (Sum.inr
      ⟨v, mem_closedBall_zero_iff.mpr (le_of_lt (mem_ball_zero_iff.mp hball))⟩) :
        TwistedSphere φ) ∈ openSeam φ := heq ▸ hmem
  exact (mem_openSeam_inr φ
    ⟨v, mem_closedBall_zero_iff.mpr (le_of_lt (mem_ball_zero_iff.mp hball))⟩).mp hmem2

lemma seamChart_source_angular_inr
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (x : openSeam φ)
    {w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1}
    (hw : 1 / 2 < ‖w.val‖) (hw1 : ‖w.val‖ < 1)
    (h : (Quot.mk (GlueRel φ) (Sum.inr w) : TwistedSphere φ) ∈ openSeam φ)
    (hsrc : (⟨Quot.mk (GlueRel φ) (Sum.inr w), h⟩ : openSeam φ) ∈
      (chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).source) :
    φ.symm (unitOr diskNorth w.val) ∈
      (chartAt (EuclideanSpace ℝ (Fin m)) ((seamHomeoIoo φ).symm x).1).source := by
  have hang := seamChart_source_angular φ x _ hsrc
  rwa [seamHomeoIoo_symm_inr_fst φ hw hw1 h] at hang

lemma seamChart_source_angular_inr_of_eq
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (x q : openSeam φ)
    {w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1}
    (heq : (q : TwistedSphere φ) = Quot.mk (GlueRel φ) (Sum.inr w))
    (hw : 1 / 2 < ‖w.val‖) (hw1 : ‖w.val‖ < 1)
    (hsrc : q ∈ (chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).source) :
    φ.symm (unitOr diskNorth w.val) ∈
      (chartAt (EuclideanSpace ℝ (Fin m)) ((seamHomeoIoo φ).symm x).1).source := by
  have hmem : (Quot.mk (GlueRel φ) (Sum.inr w) : TwistedSphere φ) ∈ openSeam φ :=
    heq ▸ q.2
  have hq : q = ⟨Quot.mk (GlueRel φ) (Sum.inr w), hmem⟩ := Subtype.ext heq
  exact seamChart_source_angular_inr φ x hw hw1 hmem (hq ▸ hsrc)

lemma seam_interiorSnd_trans_symm_angular
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (x : openSeam φ) (y : interiorSnd φ)
    {v : EuclideanSpace ℝ (Fin (m + 1))}
    (hv : v ∈ ((regionChart (isOpen_interiorSnd φ) y).symm.trans
      (regionChart (isOpen_openSeam φ) x)).source) :
    φ.symm (unitOr diskNorth v) ∈
      (chartAt (EuclideanSpace ℝ (Fin m)) ((seamHomeoIoo φ).symm x).1).source := by
  obtain ⟨hlt, hmemseam⟩ := seam_interiorSnd_trans_symm_basic φ x y hv
  have hnorm := seam_interiorSnd_trans_symm_norm φ x y hv
  have hball : v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 :=
    mem_ball_zero_iff.mpr hlt
  have hv2 : ((regionChart (isOpen_interiorSnd φ) y).symm v) ∈
      (regionChart (isOpen_openSeam φ) x).source := by
    rw [OpenPartialHomeomorph.trans_source] at hv
    exact hv.2
  have hsrc : (⟨_, hmemseam⟩ : openSeam φ) ∈
      (chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).source :=
    regionChart_source_chart (isOpen_openSeam φ) x hv2
  exact seamChart_source_angular_inr_of_eq φ x ⟨_, hmemseam⟩
    (interiorSndChart_symm_coe φ y hball) hnorm hlt hsrc

lemma seam_interiorSnd_trans_symm_coord_of_val
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (x : openSeam φ) (y : interiorSnd φ)
    {w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1}
    {v : EuclideanSpace ℝ (Fin (m + 1))} (hval : w.val = v)
    (hw : ‖w.val‖ < 1) (hw2 : 1 / 2 < ‖w.val‖)
    (hmem : (Quot.mk (GlueRel φ) (Sum.inr w) : TwistedSphere φ) ∈ openSeam φ) :
    ((regionChart (isOpen_interiorSnd φ) y).symm.trans
        (regionChart (isOpen_openSeam φ) x)) v =
      seamModelEquiv m
        ((chartAt (EuclideanSpace ℝ (Fin m)) ((seamHomeoIoo φ).symm x).1)
            (φ.symm (unitOr diskNorth v)), -(2 * (1 - ‖v‖))) := by
  subst hval
  exact seam_interiorSnd_trans_symm_coord φ x y hw hw2 hmem

lemma contDiffOn_seam_interiorSnd_trans_symm
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (hφ : ContMDiff (𝓡 m) (𝓡 m) ∞ φ.symm)
    (x : openSeam φ) (y : interiorSnd φ) :
    ContDiffOn ℝ ∞ ((regionChart (isOpen_interiorSnd φ) y).symm.trans
        (regionChart (isOpen_openSeam φ) x))
      ((regionChart (isOpen_interiorSnd φ) y).symm.trans
        (regionChart (isOpen_openSeam φ) x)).source := by
  refine ((contDiffOn_seamTransitionCoordInvTwisted φ hφ
    ((seamHomeoIoo φ).symm x).1).mono ?_).congr ?_
  · intro v hv
    have hnorm := seam_interiorSnd_trans_symm_norm φ x y hv
    refine ⟨?_, seam_interiorSnd_trans_symm_angular φ x y hv⟩
    intro h0
    rw [h0, norm_zero] at hnorm
    linarith
  · intro v hv
    obtain ⟨hlt, hmemseam⟩ := seam_interiorSnd_trans_symm_basic φ x y hv
    have hnorm := seam_interiorSnd_trans_symm_norm φ x y hv
    have hball : v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 :=
      mem_ball_zero_iff.mpr hlt
    have hmem' : (Quot.mk (GlueRel φ) (Sum.inr
        ⟨v, mem_closedBall_zero_iff.mpr (le_of_lt (mem_ball_zero_iff.mp hball))⟩) :
          TwistedSphere φ) ∈ openSeam φ :=
      (interiorSndChart_symm_coe φ y hball) ▸ hmemseam
    exact seam_interiorSnd_trans_symm_coord_of_val φ x y
      (w := ⟨v, mem_closedBall_zero_iff.mpr (le_of_lt (mem_ball_zero_iff.mp hball))⟩)
      rfl hlt hnorm hmem'

lemma contDiffOn_sphereChartSymm_twisted
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (hφ : ContMDiff (𝓡 m) (𝓡 m) ∞ φ)
    (u₀ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    ContDiffOn ℝ ∞ (fun a : EuclideanSpace ℝ (Fin m) =>
      ((φ ((chartAt (EuclideanSpace ℝ (Fin m)) u₀).symm a) :
        sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1))))
      (chartAt (EuclideanSpace ℝ (Fin m)) u₀).target := by
  have h1 : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (𝓡 m) ∞
      (chartAt (EuclideanSpace ℝ (Fin m)) u₀).symm
      (chartAt (EuclideanSpace ℝ (Fin m)) u₀).target := contMDiffOn_chart_symm
  have h2 : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞
      (fun a => ((φ ((chartAt (EuclideanSpace ℝ (Fin m)) u₀).symm a) :
        sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1))))
      (chartAt (EuclideanSpace ℝ (Fin m)) u₀).target :=
    (contMDiff_coe_sphere.comp hφ).comp_contMDiffOn h1
  rwa [contMDiffOn_iff_contDiffOn] at h2

lemma contDiffOn_seamTransitionCoordTwisted
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (hφ : ContMDiff (𝓡 m) (𝓡 m) ∞ φ)
    (u₀ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    ContDiffOn ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (m + 1)) =>
      (1 + (((seamModelEquiv m).symm v).2) / 2) •
        ((φ ((chartAt (EuclideanSpace ℝ (Fin m)) u₀).symm
            (((seamModelEquiv m).symm v).1)) :
          sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
            EuclideanSpace ℝ (Fin (m + 1))))
      ((fun v : EuclideanSpace ℝ (Fin (m + 1)) => ((seamModelEquiv m).symm v).1) ⁻¹'
        (chartAt (EuclideanSpace ℝ (Fin m)) u₀).target) := by
  have hlin : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (m + 1)) =>
      (seamModelEquiv m).symm v) := (seamModelEquiv m).symm.contDiff
  have hfst : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (m + 1)) =>
      ((seamModelEquiv m).symm v).1) := contDiff_fst.comp hlin
  have hsnd : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (m + 1)) =>
      ((seamModelEquiv m).symm v).2) := contDiff_snd.comp hlin
  have hscalar : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (m + 1)) =>
      1 + ((seamModelEquiv m).symm v).2 / 2) :=
    contDiff_const.add (hsnd.div_const 2)
  exact hscalar.contDiffOn.smul
    ((contDiffOn_sphereChartSymm_twisted φ hφ u₀).comp hfst.contDiffOn
      (fun v hv => hv))

lemma seam_neg_of_mem_interiorSnd
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (q : openSeam φ) (h : (q : TwistedSphere φ) ∈ interiorSnd φ) :
    ((((seamHomeoIoo φ).symm q).2 : Set.Ioo (-1 : ℝ) 1) : ℝ) < 0 := by
  rcases lt_or_eq_of_le (not_lt.mp (seam_nonpos_of_mem_interiorSnd φ q h)) with hlt | heq
  · exact hlt
  · exfalso
    have hz := openSeam_val_eq_inl φ q (le_of_eq heq.symm)
    rw [hz] at h
    exact (mem_interiorSnd_inl φ _).mp h

lemma seam_interiorSnd_trans_coord
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (x : openSeam φ) (y : interiorSnd φ)
    (v : EuclideanSpace ℝ (Fin (m + 1)))
    (hv : ((seamModelEquiv m).symm v).2 ∈ Set.Ioo (-1 : ℝ) 1)
    (h : (((chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).symm v : openSeam φ) :
      TwistedSphere φ) ∈ interiorSnd φ) :
    ((regionChart (isOpen_openSeam φ) x).symm.trans
        (regionChart (isOpen_interiorSnd φ) y)) v =
      (1 + ((seamModelEquiv m).symm v).2 / 2) •
        ((φ ((chartAt (EuclideanSpace ℝ (Fin m)) ((seamHomeoIoo φ).symm x).1).symm
            (((seamModelEquiv m).symm v).1)) :
          sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
            EuclideanSpace ℝ (Fin (m + 1))) := by
  have hsnd : ((((seamHomeoIoo φ).symm
      ((chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).symm v)).2 :
        Set.Ioo (-1 : ℝ) 1) : ℝ) = ((seamModelEquiv m).symm v).2 :=
    seamChart_symm_snd φ x v hv
  have hfst : ((seamHomeoIoo φ).symm
      ((chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).symm v)).1 =
      (chartAt (EuclideanSpace ℝ (Fin m)) ((seamHomeoIoo φ).symm x).1).symm
        (((seamModelEquiv m).symm v).1) := seamChart_symm_fst φ x v
  have hneg := seam_neg_of_mem_interiorSnd φ
    ((chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).symm v : openSeam φ) h
  have hinr := openSeam_val_eq_inr φ
    ((chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).symm v : openSeam φ)
    (not_le.mpr hneg)
  have hfst' : ((((seamHomeo φ).symm
      ((chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).symm v)).val).1) =
      (chartAt (EuclideanSpace ℝ (Fin m)) ((seamHomeoIoo φ).symm x).1).symm
        (((seamModelEquiv m).symm v).1) := hfst
  rw [seam_interiorSnd_trans_polar φ x y v _ (le_of_lt hneg) hinr h]
  congr 1
  · exact congrArg (fun r : ℝ => 1 + r / 2) hsnd
  · exact congrArg (fun u : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 =>
      ((φ u : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
        EuclideanSpace ℝ (Fin (m + 1)))) hfst'

lemma seam_interiorSnd_trans_hyps
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (x : openSeam φ) (y : interiorSnd φ)
    {v : EuclideanSpace ℝ (Fin (m + 1))}
    (hv : v ∈ ((regionChart (isOpen_openSeam φ) x).symm.trans
      (regionChart (isOpen_interiorSnd φ) y)).source) :
    ((seamModelEquiv m).symm v).2 ∈ Set.Ioo (-1 : ℝ) 1 ∧
      (((chartAt (EuclideanSpace ℝ (Fin (m + 1))) x).symm v : openSeam φ) :
        TwistedSphere φ) ∈ interiorSnd φ := by
  rw [OpenPartialHomeomorph.trans_source] at hv
  obtain ⟨hv1, hv2⟩ := hv
  rw [OpenPartialHomeomorph.symm_source] at hv1
  refine ⟨seamChart_target_snd_mem φ x (regionChart_target_subset _ x hv1), ?_⟩
  have := regionChart_source_subset (isOpen_interiorSnd φ) y hv2
  rwa [regionChart_symm_apply] at this

lemma contDiffOn_seam_interiorSnd_trans
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (hφ : ContMDiff (𝓡 m) (𝓡 m) ∞ φ)
    (x : openSeam φ) (y : interiorSnd φ) :
    ContDiffOn ℝ ∞ ((regionChart (isOpen_openSeam φ) x).symm.trans
        (regionChart (isOpen_interiorSnd φ) y))
      ((regionChart (isOpen_openSeam φ) x).symm.trans
        (regionChart (isOpen_interiorSnd φ) y)).source := by
  have htarget : (chartAt (EuclideanSpace ℝ (Fin m))
      ((seamHomeoIoo φ).symm x).1).target = Set.univ :=
    stereographic'_target _
  refine ((contDiffOn_seamTransitionCoordTwisted φ hφ
    ((seamHomeoIoo φ).symm x).1).mono ?_).congr ?_
  · intro v _
    simp only [Set.mem_preimage, htarget, Set.mem_univ]
  · intro v hv
    exact seam_interiorSnd_trans_coord φ x y v
      (seam_interiorSnd_trans_hyps φ x y hv).1
      (seam_interiorSnd_trans_hyps φ x y hv).2

end Hemisphere

end SP4Seam

open Set Metric SP4Gluing SPC4Disk SP4Seam
open scoped ContDiff Manifold

theorem solution {m : ℕ}
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    (∀ (x : openSeam φ) (y : interiorFst φ),
      ContDiffOn ℝ ∞ ((regionChart (isOpen_openSeam φ) x).symm.trans
        (regionChart (isOpen_interiorFst φ) y))
        ((regionChart (isOpen_openSeam φ) x).symm.trans
          (regionChart (isOpen_interiorFst φ) y)).source) ∧
    (∀ (x : openSeam φ) (y : interiorFst φ),
      ContDiffOn ℝ ∞ ((regionChart (isOpen_interiorFst φ) y).symm.trans
        (regionChart (isOpen_openSeam φ) x))
        ((regionChart (isOpen_interiorFst φ) y).symm.trans
          (regionChart (isOpen_openSeam φ) x)).source) ∧
    (ContMDiff (𝓡 m) (𝓡 m) ∞ φ.symm →
      ∀ (x : openSeam φ) (y : interiorSnd φ),
      ContDiffOn ℝ ∞ ((regionChart (isOpen_interiorSnd φ) y).symm.trans
        (regionChart (isOpen_openSeam φ) x))
        ((regionChart (isOpen_interiorSnd φ) y).symm.trans
          (regionChart (isOpen_openSeam φ) x)).source) ∧
    (ContMDiff (𝓡 m) (𝓡 m) ∞ φ →
      ∀ (x : openSeam φ) (y : interiorSnd φ),
      ContDiffOn ℝ ∞ ((regionChart (isOpen_openSeam φ) x).symm.trans
        (regionChart (isOpen_interiorSnd φ) y))
        ((regionChart (isOpen_openSeam φ) x).symm.trans
          (regionChart (isOpen_interiorSnd φ) y)).source) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact contDiffOn_seam_interiorFst_trans φ
  · exact contDiffOn_seam_interiorFst_trans_symm φ
  · intro hφ x y
    exact contDiffOn_seam_interiorSnd_trans_symm φ hφ x y
  · intro hφ x y
    exact contDiffOn_seam_interiorSnd_trans φ hφ x y
