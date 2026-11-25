-- Prove2me | solution 1 for PI.VolStabS.OrbR.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:00:42.399541+00:00
-- url     : https://prove2.me/submissions/8e423526-0155-41ff-b057-42ee9b537a08

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_HformEntry
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_OrbRing
import Theorems.Thm_PI_VolStabS_OrbR_reflection_mulVec
import Theorems.Thm_PI_VolStabS_OrbR_mem_UJ_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS PI.VolStabS.OrbR
open Matrix Formalism.UG PIW.AdelicOrbitU
variable {S : Type} [CommRing S] (s : S →+* S) {n : ℕ} (J : Matrix (Fin n) (Fin n) S)
namespace PI.VolStabS.OrbR
theorem _root_.solution (hs : ∀ z, s (s z) = z) (hJ : IsHerm s J) (hdet : IsUnit J.det)
    (a b : Fin n → S) (hab : hform s J b b = hform s J a a) (hu : IsUnit (hform s J a a))
    (lam : S) (hlam : lam * s lam = 1) (hc : IsUnit (hform s J a a - s lam * hform s J b a)) :
    ∃ g : GL (Fin n) S, g ∈ UJ s J ∧ (g : Matrix (Fin n) (Fin n) S) *ᵥ a = b ∧
      ∀ z, hform s J a z = 0 → hform s J b z = 0 → (g : Matrix (Fin n) (Fin n) S) *ᵥ z = z := by
  have hJ' : ∀ i j, s (J i j) = J j i := by
    intro i j
    have h1 := congrFun (congrFun hJ j) i
    simpa [cT] using h1
  have hsub1 : ∀ x y z : Fin n → S, hform s J (x - y) z = hform s J x z - hform s J y z := by
    intro x y z
    simp only [hform, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]
  have hsub2 : ∀ x y z : Fin n → S, hform s J x (y - z) = hform s J x y - hform s J x z := by
    intro x y z
    simp only [hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  have hsmul1 : ∀ (c : S) (x z : Fin n → S), hform s J (c • x) z = s c * hform s J x z := by
    intro c x z
    simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hsmul2 : ∀ (c : S) (x z : Fin n → S), hform s J x (c • z) = c * hform s J x z := by
    intro c x z
    simp only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hherm : ∀ x y : Fin n → S, hform s J y x = s (hform s J x y) := by
    intro x y
    simp only [hform, map_sum, map_mul, hs, hJ']
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hRu : ∀ (k : S) (w : Fin n → S), k + s k = s k * k * hform s J w w →
      ∀ z y, hform s J (r1 s J k w w *ᵥ z) (r1 s J k w w *ᵥ y) = hform s J z y := by
    intro k w hk z y
    rw [reflection_mulVec, reflection_mulVec]
    simp only [hsub1, hsub2, hsmul1, hsmul2, map_mul]
    rw [hherm w z]
    linear_combination (-(hform s J w y * s (hform s J w z))) * hk
  have hq : s (hform s J a a) = hform s J a a := (hherm a a).symm
  have hba : hform s J a b = s (hform s J b a) := hherm b a
  have hwa : hform s J (a - lam • b) a = hform s J a a - s lam * hform s J b a := by
    rw [hsub1, hsmul1]
  have e1 : s (hform s J a a - s lam * hform s J b a) = hform s J a a - lam * s (hform s J b a) := by
    rw [map_sub, map_mul, hs, hq]
  have hww : hform s J (a - lam • b) (a - lam • b) =
      (hform s J a a - s lam * hform s J b a) + s (hform s J a a - s lam * hform s J b a) := by
    simp only [hsub1, hsub2, hsmul1, hsmul2]
    linear_combination (-lam) * hba + (s lam * lam) * hab + hform s J a a * hlam - e1
  obtain ⟨ci, hci⟩ : ∃ ci : S, ci * (hform s J a a - s lam * hform s J b a) = 1 := ⟨_, hc.val_inv_mul⟩
  have hci' : s ci * s (hform s J a a - s lam * hform s J b a) = 1 := by
    rw [← map_mul, hci, map_one]
  have hk1 : ci + s ci =
      s ci * ci * hform s J (a - lam • b) (a - lam • b) := by
    linear_combination (-s ci) * hci + (-ci) * hci' +
      (-(s ci * ci)) * hww
  obtain ⟨qi, hqi⟩ : ∃ qi : S, qi * hform s J a a = 1 := ⟨_, hu.val_inv_mul⟩
  have hsqi : s qi = qi := by
    have h1 : s qi * hform s J a a = 1 := by
      have h2 := congrArg s hqi
      rwa [map_mul, hq, map_one] at h2
    calc s qi = s qi * (hform s J a a * qi) := by
          rw [mul_comm (hform s J a a), hqi, mul_one]
      _ = qi := by rw [← mul_assoc, h1, one_mul]
  have hk2 : (1 - s lam) * qi + s ((1 - s lam) * qi) =
      s ((1 - s lam) * qi) * ((1 - s lam) * qi) * hform s J b b := by
    simp only [map_mul, map_sub, map_one, hs, hsqi]
    linear_combination (-qi) * hlam -
      (1 - lam - s lam + lam * s lam) * qi ^ 2 * hab -
      (1 - lam - s lam + lam * s lam) * qi * hqi
  have hM : ∀ z y, hform s J ((r1 s J ((1 - s lam) * qi) b b *
      r1 s J ci (a - lam • b) (a - lam • b)) *ᵥ z)
      ((r1 s J ((1 - s lam) * qi) b b *
      r1 s J ci (a - lam • b) (a - lam • b)) *ᵥ y) = hform s J z y := by
    intro z y
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hRu _ _ hk2, hRu _ _ hk1]
  obtain ⟨g, hg, hgM⟩ := mem_UJ_of s J hdet _ hM
  refine ⟨g, hg, ?_, ?_⟩
  · rw [hgM, ← Matrix.mulVec_mulVec, reflection_mulVec s J ci (a - lam • b) (a - lam • b) a, hwa, hci, one_smul, sub_sub_cancel, reflection_mulVec, hsmul2,
      ← sub_smul]
    convert one_smul S b using 2
    linear_combination hlam - (1 - s lam) * lam * qi * hab - (1 - s lam) * lam * hqi
  · intro z hz1 hz2
    rw [hgM, ← Matrix.mulVec_mulVec, reflection_mulVec s J ci (a - lam • b) (a - lam • b) z, hsub1, hsmul1, hz1, hz2]
    simp only [mul_zero, sub_zero, zero_smul]
    rw [reflection_mulVec, hz2]
    simp
end PI.VolStabS.OrbR
