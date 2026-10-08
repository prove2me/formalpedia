-- Prove2me | solution 1 for WeilDefect.MarkerStability.no_strict_scalar_lower_bound_of_eventual_failure
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T21:29:46.812982+00:00
-- url     : https://prove2.me/submissions/788a63cf-de14-4587-83d9-5a15043606f1

import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace ComplexOrder Topology
open ContinuousLinearMap Filter Set
noncomputable section
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

private lemma scalar_lower_of_norm_close (A B : K →L[ℂ] K)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (a η : ℝ)
    (ha : a • (1 : K →L[ℂ] K) ≤ A) (hη : ‖A - B‖ ≤ η) :
    (a - η) • (1 : K →L[ℂ] K) ≤ B := by
  have hd := IsSelfAdjoint.le_algebraMap_norm_self (hA.sub hB)
  have he : A - B ≤ η • (1 : K →L[ℂ] K) := hd.trans (by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      smul_le_smul_of_nonneg_right hη (zero_le_one : (0 : K →L[ℂ] K) ≤ 1))
  rw [sub_smul]
  exact sub_le_iff_le_add.mpr (by
    simpa only [add_comm] using ha.trans (sub_le_iff_le_add.mp he))

private lemma scalar_identity_mono {a b : ℝ} (hab : a ≤ b) :
    a • (1 : K →L[ℂ] K) ≤ b • 1 :=
  smul_le_smul_of_nonneg_right hab zero_le_one

theorem solution
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (F : ι → K →L[ℂ] K) (A : K →L[ℂ] K) (b a : ℝ)
    (hlim : Tendsto F l (nhds A)) (hA : IsSelfAdjoint A)
    (hself : ∀ᶠ i in l, IsSelfAdjoint (F i))
    (hbad : ∀ᶠ i in l, ¬ b • (1 : K →L[ℂ] K) ≤ F i)
    (hba : b < a) : ¬ a • (1 : K →L[ℂ] K) ≤ A := by
  intro ha
  let η : ℝ := (a - b) / 2
  have hη : 0 < η := by dsimp [η]; linarith
  have hn : Tendsto (fun i => ‖A - F i‖) l (nhds (0 : ℝ)) := by
    simpa using (((tendsto_const_nhds : Tendsto (fun _ : ι => A) l (nhds A)).sub hlim).norm)
  have hev := (tendsto_order.mp hn).2 η hη
  obtain ⟨i, hi, hb, hnorm⟩ := (hself.and (hbad.and hev)).exists
  apply hb
  have hl := scalar_lower_of_norm_close A (F i) hA hi a η ha hnorm.le
  have hs : b • (1 : K →L[ℂ] K) ≤ (a - η) • (1 : K →L[ℂ] K) := by
    apply scalar_identity_mono
    dsimp [η]
    linarith
  exact hs.trans hl
