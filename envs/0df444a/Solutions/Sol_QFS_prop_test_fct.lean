-- Prove2me | solution 1 for QFS.prop_test_fct
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T05:03:09.099244+00:00
-- url     : https://prove2.me/submissions/fc0db6cd-fe63-488d-9fcb-16af9efa0ce2

import Theorems.Thm_QFS_cubeCone_subset_cube
import Theorems.Thm_QFS_discreteKernel_integrand_ge
import Theorems.Thm_QFS_lattice_sub
import Theorems.Thm_QFS_lemma_new_config
import Theorems.Thm_QFS_measurableSet_cube
import Theorems.Thm_QFS_volume_cube
import Theorems.Thm_QFS_volume_cube_le_card_mul


import Definitions.Def_QFS_Translate
import Definitions.Def_QFS_Defs
import Definitions.Def_QFS_ConeGap
import Definitions.Def_QFS_RefCones
import Definitions.Def_QFS_Section4
import Definitions.Def_QFS_Cubes
import Definitions.Def_QFS_Section3
import Definitions.Def_QFS_Section5
import Definitions.Def_QFS_Section1
import Definitions.Def_QFS_ThinCones
import Definitions.Def_QFS_Section3Kernel
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open Real Set Metric MeasureTheory ENNReal

open QFS

variable {d : ℕ}



namespace QFSProof_prop_test_fct

theorem exists_isFavoured {Γ : Configuration (EuclideanSpace ℝ (Fin d))} {θ : ℝ}
    (F : RefFamily Γ θ) (h : ℝ) (u : EuclideanSpace ℝ (Fin d)) :
    ∃ v, IsFavoured F h u v := by
  obtain ⟨w₀, hw₀, -⟩ := F.covers 0
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image F.axes
    (fun w => volume (cubeCone Γ (F.cone w) h u)) ⟨w₀, hw₀⟩
  exact ⟨v, hv, hmax⟩

lemma indE_le_indE {S T : Set (EuclideanSpace ℝ (Fin d))}
    {x y : EuclideanSpace ℝ (Fin d)} (h : x ∈ S → y ∈ T) :
    indE S x ≤ indE T y := by
  by_cases hx : x ∈ S
  · rw [indE, Set.indicator_of_mem hx, indE, Set.indicator_of_mem (h hx)]
  · rw [indE, Set.indicator_of_notMem hx]
    exact zero_le

lemma measurableSet_cubeCone {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    (hm : CondMeas Γ) (V : Set (EuclideanSpace ℝ (Fin d))) {h : ℝ} (hh : 0 < h)
    (u : EuclideanSpace ℝ (Fin d)) : MeasurableSet (cubeCone Γ V h u) :=
  (QFS.measurableSet_cube hh u).inter (hm V)

theorem discreteKernel_ge_volume {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    {α Λ : ℝ} {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k) (hα : 0 < α) {θ : ℝ} (F : RefFamily Γ θ)
    (hmeas : CondMeas Γ) {x y : EuclideanSpace ℝ (Fin d)} (hx : x ∈ lattice d)
    (hy : y ∈ lattice d) (hxy : Real.sqrt d < ‖x - y‖)
    (m n : EuclideanSpace ℝ (Fin d)) :
    ENNReal.ofReal Λ⁻¹ *
        ((indE (F.shrunkAt m (Real.sqrt d) x) y + indE (F.shrunkAt n (Real.sqrt d) y) x)
          * ENNReal.ofReal ((2 * Real.sqrt d) ^ (-(d:ℝ) - α) * ‖x - y‖ ^ (-(d:ℝ) - α)))
        * (volume (cubeCone Γ (F.cone m) 1 x) * volume (cubeCone Γ (F.cone n) 1 y))
      ≤ discreteKernel d k 1 x y := by
  have hsub : cubeCone Γ (F.cone m) 1 x ×ˢ cubeCone Γ (F.cone n) 1 y
      ⊆ cube 1 x ×ˢ cube 1 y :=
    Set.prod_mono (QFS.cubeCone_subset_cube _ _ _ _) (QFS.cubeCone_subset_cube _ _ _ _)
  have hpre : discreteKernel d k 1 x y = ∫⁻ p in cube 1 x ×ˢ cube 1 y, k p.1 p.2 := by
    rw [discreteKernel, one_pow, inv_one, ENNReal.ofReal_one, one_mul]
  rw [hpre]
  calc ENNReal.ofReal Λ⁻¹ *
        ((indE (F.shrunkAt m (Real.sqrt d) x) y + indE (F.shrunkAt n (Real.sqrt d) y) x)
          * ENNReal.ofReal ((2 * Real.sqrt d) ^ (-(d:ℝ) - α) * ‖x - y‖ ^ (-(d:ℝ) - α)))
        * (volume (cubeCone Γ (F.cone m) 1 x) * volume (cubeCone Γ (F.cone n) 1 y))
      = ∫⁻ _ in cubeCone Γ (F.cone m) 1 x ×ˢ cubeCone Γ (F.cone n) 1 y,
          ENNReal.ofReal Λ⁻¹ *
            ((indE (F.shrunkAt m (Real.sqrt d) x) y
              + indE (F.shrunkAt n (Real.sqrt d) y) x)
              * ENNReal.ofReal ((2 * Real.sqrt d) ^ (-(d:ℝ) - α)
                * ‖x - y‖ ^ (-(d:ℝ) - α))) := by
        rw [setLIntegral_const, Measure.volume_eq_prod, Measure.prod_prod]
    _ ≤ ∫⁻ p in cubeCone Γ (F.cone m) 1 x ×ˢ cubeCone Γ (F.cone n) 1 y, k p.1 p.2 := by
        refine lintegral_mono_ae (ae_restrict_of_forall_mem
          ((measurableSet_cubeCone hmeas _ one_pos x).prod
            (measurableSet_cubeCone hmeas _ one_pos y)) ?_)
        rintro ⟨s, t⟩ ⟨hs, ht⟩
        exact QFS.discreteKernel_integrand_ge hk hα F hx hy hxy hs ht
    _ ≤ ∫⁻ p in cube 1 x ×ˢ cube 1 y, k p.1 p.2 :=
        lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl

lemma inv_card_le_volume_cubeCone {Γ : Configuration (EuclideanSpace ℝ (Fin d))} {θ : ℝ}
    (F : RefFamily Γ θ) (hne : F.axes.Nonempty) {x v : EuclideanSpace ℝ (Fin d)}
    (hv : IsFavoured F 1 x v) :
    ((F.axes.card : ℝ≥0∞))⁻¹ ≤ volume (cubeCone Γ (F.cone v) 1 x) := by
  have hL : (F.axes.card : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero, Finset.card_eq_zero]
    exact Finset.nonempty_iff_ne_empty.mp hne
  have hLt : (F.axes.card : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have h1 : (1 : ℝ≥0∞) ≤ (F.axes.card : ℝ≥0∞) * volume (cubeCone Γ (F.cone v) 1 x) := by
    have h := QFS.volume_cube_le_card_mul F hv
    rwa [QFS.volume_cube one_pos, one_pow, ENNReal.ofReal_one] at h
  calc ((F.axes.card : ℝ≥0∞))⁻¹ = ((F.axes.card : ℝ≥0∞))⁻¹ * 1 := by rw [mul_one]
    _ ≤ ((F.axes.card : ℝ≥0∞))⁻¹ *
          ((F.axes.card : ℝ≥0∞) * volume (cubeCone Γ (F.cone v) 1 x)) :=
        mul_le_mul' le_rfl h1
    _ = volume (cubeCone Γ (F.cone v) 1 x) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hL hLt, one_mul]

end QFSProof_prop_test_fct
open QFSProof_prop_test_fct

set_option autoImplicit false

theorem solution {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) (hd : 2 ≤ d) {α : ℝ}
    (hα : 0 < α) (hα2 : α ≤ 2) :
    ∃ C θ' : ℝ, 0 < C ∧ 0 < θ' ∧ θ' ≤ π / 2 ∧
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ ϑ → CondMeas Γ →
      ∀ (Λ : ℝ) (k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞),
        KernelBounds Γ α Λ k →
      ∃ Γ' : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ' θ' ∧
        ∀ x ∈ lattice d, ∀ y ∈ lattice d, Real.sqrt d < ‖x - y‖ →
          ENNReal.ofReal (C * Λ⁻¹) *
              ((indE (coneAt Γ' x) y + indE (coneAt Γ' y) x) * jumpKernel d α x y)
            ≤ discreteKernel d k 1 x y := by
  classical
  have hd1 : 0 < d := by omega
  have hsd : (0:ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd1)
  have hθ0 : (0:ℝ) < ϑ / 3 := by positivity
  have hθle : ϑ / 3 ≤ π / 2 := by linarith [pi_pos]

  obtain ⟨S, hSdef⟩ : ∃ S : Finset (EuclideanSpace ℝ (Fin d)),
      S = (ref_cones (E := EuclideanSpace ℝ (Fin d)) hϑ hϑ').choose := ⟨_, rfl⟩
  have hSnorm : ∀ v ∈ S, ‖v‖ = 1 := by
    rw [hSdef]; exact (ref_cones (E := EuclideanSpace ℝ (Fin d)) hϑ hϑ').choose_spec.1
  obtain ⟨e, he⟩ : ∃ e : EuclideanSpace ℝ (Fin d), ‖e‖ = 1 := by
    refine ⟨EuclideanSpace.single (⟨0, hd1⟩ : Fin d) (1:ℝ), ?_⟩
    simp
  have hSne : S.Nonempty := by
    obtain ⟨v, hv, -⟩ :=
      (ref_cones (E := EuclideanSpace ℝ (Fin d)) hϑ hϑ').choose_spec.2
        (fun _ => ⟨e, he, ϑ, hϑ, hϑ'⟩) ⟨hϑ, fun _ => le_rfl⟩ 0
    exact ⟨v, by rw [hSdef]; exact hv⟩

  obtain ⟨θ', hθ'0, hθ'le, hthin⟩ := QFS.lemma_new_config hd hsd hθ0 hθle S hSnorm
  refine ⟨(2 * Real.sqrt d) ^ (-(d:ℝ) - 2) * ((S.card : ℝ)⁻¹ * (S.card : ℝ)⁻¹), θ',
    by positivity, hθ'0, hθ'le, ?_⟩
  intro Γ hΓ hmeas Λ k hk
  obtain ⟨F, hFdef⟩ : ∃ F : RefFamily Γ (ϑ / 3), F = refFamily hϑ hϑ' Γ hΓ := ⟨_, rfl⟩
  have hFaxes : F.axes = S := by rw [hFdef, hSdef]; rfl
  choose fav hfav using (fun u => exists_isFavoured F 1 u)
  have haxex : ∀ u : EuclideanSpace ℝ (Fin d), ∃ w : EuclideanSpace ℝ (Fin d), ‖w‖ = 1 ∧
      (u ∈ S → doubleCone w θ' ∩ lattice d
        ⊆ shrink (doubleCone u (ϑ / 3)) (Real.sqrt d) ∩ lattice d) := by
    intro u
    by_cases hu : u ∈ S
    · obtain ⟨w, hw, hsub⟩ := hthin u hu
      exact ⟨w, hw, fun _ => hsub⟩
    · exact ⟨e, he, fun hc => absurd hc hu⟩
  choose ax hax haxsub using haxex
  refine ⟨fun u => ⟨ax (fav u), hax (fav u), θ', hθ'0, hθ'le⟩, ⟨hθ'0, fun _ => le_rfl⟩, ?_⟩
  intro x hx y hy hxy

  have hind : ∀ u w : EuclideanSpace ℝ (Fin d), u ∈ lattice d → w ∈ lattice d →
      indE (coneAt (fun p => (⟨ax (fav p), hax (fav p), θ', hθ'0, hθ'le⟩ :
          DCone (EuclideanSpace ℝ (Fin d)))) u) w
        ≤ indE (F.shrunkAt (fav u) (Real.sqrt d) u) w := by
    intro u w hu hw
    refine indE_le_indE (fun hmem => ?_)
    exact (haxsub (fav u) (by rw [← hFaxes]; exact (hfav u).1)
      ⟨hmem, QFS.lattice_sub hw hu⟩).1
  have hvolx := inv_card_le_volume_cubeCone F (by rw [hFaxes]; exact hSne) (hfav x)
  have hvoly := inv_card_le_volume_cubeCone F (by rw [hFaxes]; exact hSne) (hfav y)
  refine le_trans ?_ (discreteKernel_ge_volume hk hα F hmeas hx hy hxy (fav x) (fav y))

  have hLpos : (0:ℝ) < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hSne
  have hLinv : ENNReal.ofReal ((S.card : ℝ)⁻¹) = ((F.axes.card : ℝ≥0∞))⁻¹ := by
    rw [hFaxes, ← ENNReal.ofReal_natCast S.card, ← ENNReal.ofReal_inv_of_pos hLpos]
  have hΛ0 : (0:ℝ) ≤ Λ⁻¹ := by
    have := lt_of_lt_of_le zero_lt_one hk.one_le
    positivity
  have hsplit : ENNReal.ofReal ((2 * Real.sqrt d) ^ (-(d:ℝ) - α) *
        ((S.card : ℝ)⁻¹ * (S.card : ℝ)⁻¹) * Λ⁻¹) *
      ((indE (coneAt (fun p => (⟨ax (fav p), hax (fav p), θ', hθ'0, hθ'le⟩ :
          DCone (EuclideanSpace ℝ (Fin d)))) x) y
        + indE (coneAt (fun p => (⟨ax (fav p), hax (fav p), θ', hθ'0, hθ'le⟩ :
          DCone (EuclideanSpace ℝ (Fin d)))) y) x) * jumpKernel d α x y)
      = ENNReal.ofReal Λ⁻¹ *
          ((indE (coneAt (fun p => (⟨ax (fav p), hax (fav p), θ', hθ'0, hθ'le⟩ :
              DCone (EuclideanSpace ℝ (Fin d)))) x) y
            + indE (coneAt (fun p => (⟨ax (fav p), hax (fav p), θ', hθ'0, hθ'le⟩ :
              DCone (EuclideanSpace ℝ (Fin d)))) y) x)
            * ENNReal.ofReal ((2 * Real.sqrt d) ^ (-(d:ℝ) - α) * ‖x - y‖ ^ (-(d:ℝ) - α)))
          * (((F.axes.card : ℝ≥0∞))⁻¹ * ((F.axes.card : ℝ≥0∞))⁻¹) := by
    rw [← hLinv, jumpKernel,
      ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (2 * Real.sqrt d) ^ (-(d:ℝ) - α)),
      ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (2 * Real.sqrt d) ^ (-(d:ℝ) - α) *
        ((S.card : ℝ)⁻¹ * (S.card : ℝ)⁻¹)),
      ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (2 * Real.sqrt d) ^ (-(d:ℝ) - α)),
      ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ ((S.card : ℝ))⁻¹)]
    ring

  have hconst : ENNReal.ofReal ((2 * Real.sqrt d) ^ (-(d:ℝ) - 2) *
        ((S.card : ℝ)⁻¹ * (S.card : ℝ)⁻¹) * Λ⁻¹)
      ≤ ENNReal.ofReal ((2 * Real.sqrt d) ^ (-(d:ℝ) - α) *
        ((S.card : ℝ)⁻¹ * (S.card : ℝ)⁻¹) * Λ⁻¹) := by
    refine ENNReal.ofReal_le_ofReal ?_
    have hbase : (1:ℝ) ≤ 2 * Real.sqrt d := by
      have h1 : (1:ℝ) ≤ Real.sqrt d := by
        rw [show (1:ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ d by omega))
      linarith
    have hmono : (2 * Real.sqrt d) ^ (-(d:ℝ) - 2) ≤ (2 * Real.sqrt d) ^ (-(d:ℝ) - α) :=
      Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
    have hΛpos : (0:ℝ) < Λ⁻¹ := by
      have := lt_of_lt_of_le zero_lt_one hk.one_le
      positivity
    have hL2 : (0:ℝ) < (S.card : ℝ)⁻¹ * (S.card : ℝ)⁻¹ := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hmono hL2.le]
  refine le_trans (mul_le_mul' hconst le_rfl) ?_
  rw [hsplit]
  exact mul_le_mul' (mul_le_mul' le_rfl (mul_le_mul'
    (add_le_add (hind x y hx hy) (hind y x hy hx)) le_rfl))
    (mul_le_mul' hvolx hvoly)
#print axioms solution
