-- Prove2me | solution 1 for PI.DvRows.partA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:47:38.085568+00:00
-- url     : https://prove2.me/submissions/daafc790-8ec2-4211-b5aa-ce7f3be89d69

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_ValLeOneOfMemRange
import Theorems.Thm_PI_DvRows_neg_vAdd_le
import Theorems.Thm_PI_DvRows_val_det_le
import Theorems.Thm_PI_DvRows_val_eq_one_of_not_mem
import Theorems.Thm_PI_DvRows_val_le_one_of_mem_range
import Theorems.Thm_PI_DvRows_val_star_eq_one
import Theorems.Thm_PI_DvRows_h_smul_left
import Theorems.Thm_PI_DvRows_h_smul_right
import Theorems.Thm_PI_DvRows_card_le_of_orth
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
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
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace PI.DvRows
theorem _root_.solution (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K)
    (hP : IsProj A e n) (hH : IsHermE A e h) (hD : ∀ w, DualInAt A h A.L w)
    (U : Submodule K A.V) (hU : U ≤ LinearMap.range e) (w : HeightOneSpectrum (𝓞 K)) (k : ℤ)
    (hk : IsValG A e h U w k) :
    k ≤ ((dimE A e : ℤ) - (Module.finrank K U : ℤ)) * vAdd w ((n : ℕ) : K) := by
  classical
  obtain ⟨hG, hn, hee, hnL, -⟩ := hP
  obtain ⟨w', hww, d, y, hy, hloc, rfl⟩ := hk
  have hidem : ∀ x ∈ LinearMap.range e, e x = x := by
    rintro x ⟨z, rfl⟩
    change (e * e) z = e z
    rw [hee]
  have hw : w ∈ ({w, w'} : Set (HeightOneSpectrum (𝓞 K))) := Or.inl rfl
  have hw' : w' ∈ ({w, w'} : Set (HeightOneSpectrum (𝓞 K))) := Or.inr rfl
  have hy_props : ∀ i, y i ∈ LinearMap.range e ∧ ∀ u ∈ U, h (y i) u = 0 := by
    intro i
    obtain ⟨s, hs, hL⟩ := (hloc w hw).1 i
    have hs0 : (algebraMap (𝓞 K) K s) ≠ 0 := by
      intro h0
      have h00 : s = 0 := IsFractionRing.injective (𝓞 K) K (by rw [h0, map_zero])
      exact hs (h00 ▸ w.asIdeal.zero_mem)
    obtain ⟨h1, h2, -⟩ := hL
    rw [← algebraMap_smul K s (y i)] at h1 h2
    refine ⟨?_, fun u hu => ?_⟩
    · have := Submodule.smul_mem (LinearMap.range e) (algebraMap (𝓞 K) K s)⁻¹ h1
      rwa [smul_smul, inv_mul_cancel₀ hs0, one_smul] at this
    · have := h2 u hu
      rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] at this
      rcases mul_eq_zero.1 this with h0 | h0
      · exact absurd (by simpa using h0) hs0
      · exact h0
  have hcard := card_le_of_orth A e h hee hH U hU y hy (fun i => (hy_props i).1)
    (fun i => (hy_props i).2)
  have hnK : ((n : ℕ) : K) ≠ 0 := by exact_mod_cast hn.ne'
  have hnval : w.valuation K ((n : ℕ) : K) ≤ 1 := by
    have := w.valuation_le_one (K := K) (n : 𝓞 K)
    simpa using this
  have hent : ∀ i j, w.valuation K (h (y i) (y j)) * w.valuation K ((n : ℕ) : K) ≤ 1 := by
    intro i j
    obtain ⟨a, ha, hLa⟩ := (hloc w' hw').1 i
    obtain ⟨b, hb, hLb⟩ := (hloc w hw).1 j
    set v : A.V := ((n : ℕ) : 𝓞 K) • (b • y j) with hv
    have hvint : ∀ m ∈ A.L, h v m ∈ Set.range (algebraMap (𝓞 K) K) := by
      intro m hm
      have hbe : b • y j ∈ LinearMap.range e := hLb.1
      have h1 : h v m = h (b • y j) (((n : ℕ) : 𝓞 K) • e m) := by
        rw [hv, h_smul_left, h_smul_right, ← hH.2.2, hidem _ hbe]
        simp
      rw [h1]
      exact hLb.2.2 _ ⟨hnL m hm, Submodule.smul_mem _ _ (LinearMap.mem_range_self e m)⟩
    obtain ⟨t, ht, htv⟩ := hD w v hvint
    have htcut : t • v ∈ cutE A e A.L := by
      refine ⟨htv, ?_⟩
      show t • v ∈ LinearMap.range e
      exact Submodule.smul_of_tower_mem _ t (Submodule.smul_of_tower_mem _ _ hLb.1)
    have hint := hLa.2.2 _ htcut
    have heq : h (a • y i) (t • v) = star (algebraMap (𝓞 K) K a) *
        (algebraMap (𝓞 K) K t * (((n : ℕ) : K) * (algebraMap (𝓞 K) K b * h (y i) (y j)))) := by
      rw [hv, h_smul_left, h_smul_right, h_smul_right, h_smul_right]
      simp only [map_natCast]
    have hv1 := val_le_one_of_mem_range w _ hint
    rw [heq, map_mul, map_mul, map_mul, map_mul, val_star_eq_one w w' hww a ha,
      val_eq_one_of_not_mem w t ht, val_eq_one_of_not_mem w b hb] at hv1
    simpa [mul_comm] using hv1
  have hdet := val_det_le w (Matrix.of fun i j => h (y i) (y j)) ((n : ℕ) : K) (by simpa using hent)
  have := neg_vAdd_le w _ _ hnK hnval d hdet
  have hvn : 0 ≤ vAdd w ((n : ℕ) : K) := by
    unfold vAdd
    rw [neg_nonneg, ← WithZero.log_one]
    exact (WithZero.log_le_log (by simpa using hnK) one_ne_zero).2 hnval
  have hd : (d : ℤ) ≤ (dimE A e : ℤ) - (Module.finrank K U : ℤ) := by omega
  calc -vAdd w (Matrix.of fun i j => h (y i) (y j)).det ≤ (d : ℤ) * vAdd w ((n : ℕ) : K) := this
    _ ≤ _ := mul_le_mul_of_nonneg_right hd hvn
end PI.DvRows
