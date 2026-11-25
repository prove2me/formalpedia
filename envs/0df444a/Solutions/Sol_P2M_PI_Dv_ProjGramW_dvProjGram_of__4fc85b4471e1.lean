-- Prove2me | solution 1 for P2M_PI_Dv_ProjGramW_dvProjGram_of__4fc85b4471e1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:53:40.769805+00:00
-- url     : https://prove2.me/submissions/09d0f2c2-62ef-4787-9ee2-f9cab8cdac99

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_IdxDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_DvProjGramOf
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_denom
import Theorems.Thm_P2M_PI_Dv_ProjGramW_vAdd_zero__1a796c960964
import Theorems.Thm_PI_Dv_ProjGramW_algebraMap_ne_zero_of_not_mem
import Theorems.Thm_PI_Dv_ProjGramW_exists_rep
import Theorems.Thm_PI_Dv_ProjGramW_idx_eq_zero_of_loc
import Theorems.Thm_PI_Dv_ProjGramW_idx_nonpos_of_loc
import Theorems.Thm_PI_Dv_ProjGramW_linIndep_mat
import Theorems.Thm_PI_Dv_ProjGramW_locLe_zero_iff
import Theorems.Thm_PI_Dv_ProjGramW_span_le_of_locLe
import Theorems.Thm_PI_Dv_ProjGramW_vAdd_eq_zero_iff
import Theorems.Thm_PI_Dv_ProjGramW_vAdd_natCast_nonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjGramW
open NumberField IsDedekindDomain Formalism.BasicNotions
namespace PI.Dv.ProjGramW
theorem _root_.solution (hA : ProjA) (hI : IdxCalc) (hD : IdxDet) : gram_det_kernel_base_level := by
  intro K _ _ _ _ A e n h _hconj hP hH w w' hww hDw _hDw' d a hB
  classical
  have hee : e * e = e := hP.2.2.1
  obtain ⟨hherm, hnd, hself⟩ := hH
  have hL2a := hA K A e n hP
  set M := cutE A e A.L with hM
  set P := imgE A e A.L with hPdef
  set G : Matrix (Fin d) (Fin d) K := Matrix.of fun i j => h (a i) (a j) with hGdef
  have hvn := vAdd_natCast_nonneg w n
  by_cases hG0 : G.det = 0
  · rw [hG0, vAdd_zero']
    exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hvn
  have hGu : IsUnit G.det := isUnit_iff_ne_zero.mpr hG0
  set a' : Fin d → A.V := fun i => ∑ k, (G⁻¹) k i • a k with ha'

  have hGH : G.conjTranspose = G := by
    ext i j
    simp only [Matrix.conjTranspose_apply, hGdef, Matrix.of_apply]
    exact (hherm (a j) (a i)).symm

  have hdual : ∀ i j, h (a' i) (a j) = if i = j then 1 else 0 := by
    intro i j
    have e1 : h (a' i) (a j) = ∑ k, star ((G⁻¹) k i) * G k j := by
      simp only [ha', map_sum, LinearMap.map_smulₛₗ, starRingEnd_apply, hGdef, Matrix.of_apply]
      rw [LinearMap.sum_apply]
      simp only [LinearMap.smul_apply, smul_eq_mul]
    have e2 : ∑ k, star ((G⁻¹) k i) * G k j = ((G⁻¹).conjTranspose * G) i j := by
      rw [Matrix.mul_apply]
      rfl
    rw [e1, e2, Matrix.conjTranspose_nonsing_inv, hGH, Matrix.nonsing_inv_mul G hGu, Matrix.one_apply]
  have ha_eq : ∀ j, ∑ i, G i j • a' i = a j := by
    intro j
    simp only [ha', Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    have : ∀ k, ∑ i, G i j * (G⁻¹) k i = (G⁻¹ * G) k j := by
      intro k
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    simp_rw [this, Matrix.nonsing_inv_mul G hGu, Matrix.one_apply, ite_smul, one_smul, zero_smul]
    simp
  have hli' : LinearIndependent K a' := linIndep_mat hB.1 G⁻¹
    (Matrix.isUnit_nonsing_inv_det G hGu).ne_zero
  set D := Submodule.span (𝓞 K) (Set.range a') with hDdef
  set S := Submodule.span (𝓞 K) (Set.range a) with hSdef
  have hDS : idxAt w D S = vAdd w G.det := by
    have := hD K A.V w d a' hli' G hG0
    have e : (fun j => ∑ i, G i j • a' i) = a := funext ha_eq
    rw [e] at this
    exact this

  have hBw := hB.2 w (by simp)
  have hBw' := hB.2 w' (by simp)

  have hak : ∀ k, e (a k) = a k := by
    intro k
    obtain ⟨s, hs, hsx⟩ := (locLe_zero_iff w _ _).mp hBw.1 (a k) (Submodule.subset_span ⟨k, rfl⟩)
    have hr : (algebraMap (𝓞 K) K s) • a k ∈ LinearMap.range e := by
      rw [algebraMap_smul]; exact hsx.2
    have hr' := Submodule.smul_mem _ (algebraMap (𝓞 K) K s)⁻¹ hr
    rw [smul_smul, inv_mul_cancel₀ (algebraMap_ne_zero_of_not_mem w hs), one_smul] at hr'
    obtain ⟨z, hz⟩ := hr'
    rw [← hz]
    change (e * e) z = e z
    rw [hee]
  have ha'e : ∀ i, e (a' i) = a' i := by
    intro i
    simp only [ha', map_sum, map_smul, hak]

  have hLfg : A.L.FG := hP.1.2.1
  have hMfg : M.FG := Submodule.FG.of_le hLfg inf_le_left
  have hPfg : P.FG := hLfg.map _
  have hDfg : D.FG := Submodule.fg_span (Set.finite_range _)
  have hSfg : S.FG := Submodule.fg_span (Set.finite_range _)
  have hsDS : Submodule.span K (D : Set A.V) = Submodule.span K (S : Set A.V) := by
    rw [hDdef, hSdef, Submodule.span_span_of_tower, Submodule.span_span_of_tower]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      rw [← ha_eq j]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hsSM : Submodule.span K (S : Set A.V) = Submodule.span K (M : Set A.V) :=
    le_antisymm (span_le_of_locLe w hBw.1) (span_le_of_locLe w hBw.2)
  have hn0 : ((n : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr hP.2.1.ne'
  have hsMP : Submodule.span K (M : Set A.V) = Submodule.span K (P : Set A.V) := by
    apply le_antisymm (Submodule.span_mono hL2a.2.1)
    rw [Submodule.span_le]
    intro x hx
    have h1 := hL2a.1 x hx
    have h2 : ((n : ℕ) : K) • x ∈ Submodule.span K (M : Set A.V) := by
      have : ((n : ℕ) : K) • x = ((n : ℕ) : 𝓞 K) • x := by
        rw [← algebraMap_smul K ((n : ℕ) : 𝓞 K) x, map_natCast]
      rw [this]
      exact Submodule.subset_span h1
    have h3 := Submodule.smul_mem _ ((n : ℕ) : K)⁻¹ h2
    rwa [smul_smul, inv_mul_cancel₀ hn0, one_smul] at h3

  obtain ⟨s', hs'S, hs'⟩ := Formalism.HermitianLatticesTheory.indexBasic_denom w'.asIdeal.primeCompl M S hMfg
    (fun x hx => (locLe_zero_iff w' _ _).mp hBw'.2 x hx)
  have hs'w : s' ∉ w'.asIdeal := hs'S
  have hs'0 : s' ≠ 0 := fun h0 => hs'w (h0 ▸ w'.asIdeal.zero_mem)
  set t : 𝓞 K := RingOfIntegers.mapRingHom (starRingEnd K) s' with ht
  have htK : algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K s') := rfl
  have ht0 : t ≠ 0 := by
    intro h0
    have : algebraMap (𝓞 K) K t = 0 := by rw [h0, map_zero]
    rw [htK, star_eq_zero] at this
    exact algebraMap_ne_zero_of_not_mem w' hs'w this
  have htw : t ∉ w.asIdeal := by
    rw [← vAdd_eq_zero_iff w ht0, htK, ← hww, vAdd_eq_zero_iff w' hs'0]
    exact hs'w
  have hint : ∀ i, ∀ x ∈ S, h (a' i) x ∈ Set.range (algebraMap (𝓞 K) K) := by
    intro i
    have hle : S ≤ (LinearMap.range (Algebra.linearMap (𝓞 K) K)).comap
        ((h (a' i)).restrictScalars (𝓞 K)) := by
      rw [hSdef, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply,
        LinearMap.mem_range, Algebra.linearMap_apply]
      rw [hdual]
      split_ifs
      · exact ⟨1, map_one _⟩
      · exact ⟨0, map_zero _⟩
    intro x hx
    obtain ⟨r, hr⟩ := hle hx
    exact ⟨r, by simpa using hr⟩
  have hDP : ∀ i, ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • a' i ∈ P := by
    intro i
    set ψ : Module.Dual K A.V := h (algebraMap (𝓞 K) K t • a' i) with hψ
    have hψe : ψ ∘ₗ e = ψ := by
      ext y
      simp only [LinearMap.comp_apply, hψ]
      rw [← hself, map_smul, ha'e]
    have hψM : ψ ∈ Formalism.HN.dualLat M := by
      intro m hm
      have e1 : ψ m = h (a' i) (s' • m) := by
        rw [hψ, LinearMap.map_smulₛₗ, ← algebraMap_smul K s' m, map_smul, htK]
        simp [starRingEnd_apply, star_star, smul_eq_mul]
        rw [Algebra.smul_def]
      rw [e1]
      exact hint i _ (hs' m hm)
    obtain ⟨φ, hφ, hψφ⟩ := (hL2a.2.2.2.2 ψ hψe).mp hψM
    obtain ⟨u, hu⟩ := exists_rep A h hnd φ
    obtain ⟨s, hs, hsu⟩ := hDw u (fun x hx => by rw [hu]; exact hφ x hx)
    have heu : e u = algebraMap (𝓞 K) K t • a' i := by
      apply sub_eq_zero.mp
      apply hnd
      intro y
      rw [map_sub, LinearMap.sub_apply, hself, hu]
      change φ (e y) - ψ y = 0
      rw [hψφ]
      simp
    refine ⟨s * t, fun hm => ?_, ?_⟩
    · rcases w.isPrime.mem_or_mem hm with h1 | h1
      · exact hs h1
      · exact htw h1
    · refine ⟨s • u, hsu, ?_⟩
      rw [map_smul, LinearMap.restrictScalars_apply, heu, algebraMap_smul, smul_smul]
  have hLocDP : LocLe w 0 D P := by
    rw [locLe_zero_iff]
    have hle : D ≤ Formalism.HermitianLatticesTheory.locS w.asIdeal.primeCompl P := by
      rw [hDdef, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      obtain ⟨s, hs, hsP⟩ := hDP i
      exact ⟨s, hs, hsP⟩
    intro x hx
    obtain ⟨s, hs, hsP⟩ := hle hx
    exact ⟨s, hs, hsP⟩

  have hsDP : Submodule.span K (D : Set A.V) = Submodule.span K (P : Set A.V) := by
    rw [hsDS, hsSM, hsMP]
  have h2 := (hI K A.V w D P hDfg hPfg hsDP).2.1 S hSfg (by rw [← hsMP, ← hsSM])
  have h3 := idx_nonpos_of_loc hI w hDfg hPfg hsDP hLocDP
  have h4 := (hI K A.V w P M hPfg hMfg hsMP.symm).2.1 S hSfg hsSM
  have h5 := idx_eq_zero_of_loc hI w hMfg hSfg hBw.2 hBw.1
  have h6 := (hL2a.2.2.2.1 w).2.2
  have h7 : ((min (dimE A e) (dimE A (1 - e)) : ℕ) : ℤ) ≤ (dimE A (1 - e) : ℤ) :=
    Nat.cast_le.mpr (min_le_right _ _)
  have h8 := mul_le_mul_of_nonneg_right h7 hvn
  have h9 : 0 ≤ (dimE A (1 - e) : ℤ) * vAdd w ((n : ℕ) : K) := mul_nonneg (Nat.cast_nonneg _) hvn
  rw [← hDS]
  linarith
end PI.Dv.ProjGramW
