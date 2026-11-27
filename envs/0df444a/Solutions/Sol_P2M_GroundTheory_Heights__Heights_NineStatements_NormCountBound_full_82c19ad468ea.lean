-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NineStatements_NormCountBound_full_82c19ad468ea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:03:35.893973+00:00
-- url     : https://prove2.me/submissions/bb1346ea-4028-4b0d-b057-08c5d4b0a485

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_PNormCountBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_exists_prime_mem_heightOneSpectrum_c3aeab300187
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_log_absNorm_heightOneSpectrum_nonneg_363f17010b7e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_log_absNorm_eq_sum_bb1719d332cb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_log_absNorm_primeFrac_1bb1ff15a839
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_primeFrac_ne_zero_6c9de5626853


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NineStatements
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace GroundTheory.Heights₂.Heights.NineStatements
namespace NormCountBound
theorem _root_.solution : NormCountBound.Statement := by
  intro L _ _ 𝔠 𝔇 S a b h𝔠 h𝔇 ha hb hloc
  classical
  have fin : ∀ J : FractionalIdeal (𝓞 L)⁰ L,
      {v : HeightOneSpectrum (𝓞 L) | FractionalIdeal.count L v J ≠ 0}.Finite :=
    fun J => Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors J)
  let P := S.filter Nat.Prime
  let T : Finset (HeightOneSpectrum (𝓞 L)) := (fin 𝔠).toFinset ∪ (fin (𝔇 : FractionalIdeal (𝓞 L)⁰ L)).toFinset ∪
    P.biUnion (fun q => (fin (primeFrac L q)).toFinset)
  have h𝔠T : ∀ v, FractionalIdeal.count L v 𝔠 ≠ 0 → v ∈ T := fun v hv =>
    Finset.mem_union_left _ (Finset.mem_union_left _ ((fin 𝔠).mem_toFinset.mpr hv))
  have h𝔇T : ∀ v, FractionalIdeal.count L v (𝔇 : FractionalIdeal (𝓞 L)⁰ L) ≠ 0 → v ∈ T := fun v hv =>
    Finset.mem_union_left _ (Finset.mem_union_right _ ((fin _).mem_toFinset.mpr hv))
  have hqT : ∀ q ∈ P, ∀ v, FractionalIdeal.count L v (primeFrac L q) ≠ 0 → v ∈ T := fun q hq v hv =>
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨q, hq, (fin _).mem_toFinset.mpr hv⟩)
  have h𝔠eq := log_absNorm_eq_sum h𝔠 T h𝔠T
  have h𝔇eq := log_absNorm_eq_sum (I := (𝔇 : FractionalIdeal (𝓞 L)⁰ L))
    (by rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact h𝔇) T h𝔇T
  rw [FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast] at h𝔇eq
  have hqeq : ∀ q ∈ P, ∑ v ∈ T, (FractionalIdeal.count L v (primeFrac L q) : ℝ) *
      Real.log (Ideal.absNorm v.asIdeal : ℝ) = Module.finrank ℚ L * Real.log q := fun q hq => by
    rw [← log_absNorm_eq_sum (primeFrac_ne_zero L (Finset.mem_filter.mp hq).2) T (hqT q hq),
      log_absNorm_primeFrac]
  have hterm : ∀ q ∈ P, ∀ v : HeightOneSpectrum (𝓞 L),
      0 ≤ a * (FractionalIdeal.count L v (primeFrac L q) : ℝ) / ((q : ℝ) - 1) := fun q hq v => by
    apply div_nonneg (mul_nonneg ha (by exact_mod_cast FractionalIdeal.count_coe_nonneg L v _))
    have : (1 : ℝ) ≤ q := by exact_mod_cast (Finset.mem_filter.mp hq).2.one_lt.le
    linarith
  have hv : ∀ v : HeightOneSpectrum (𝓞 L), |(FractionalIdeal.count L v 𝔠 : ℝ)| ≤
      ∑ q ∈ P, a * (FractionalIdeal.count L v (primeFrac L q) : ℝ) / ((q : ℝ) - 1) +
        b * (FractionalIdeal.count L v (𝔇 : FractionalIdeal (𝓞 L)⁰ L) : ℝ) := fun v => by
    obtain ⟨p, hp, hpv⟩ := exists_prime_mem_heightOneSpectrum v
    have h1 := hloc p hp v hpv
    have h2 : (if p ∈ S then a * (FractionalIdeal.count L v (primeFrac L p) : ℝ) / ((p : ℝ) - 1) else 0) ≤
        ∑ q ∈ P, a * (FractionalIdeal.count L v (primeFrac L q) : ℝ) / ((q : ℝ) - 1) := by
      split_ifs with hpS
      · exact Finset.single_le_sum (f := fun q => a * (FractionalIdeal.count L v (primeFrac L q) : ℝ) /
          ((q : ℝ) - 1)) (fun q hq => hterm q hq v) (Finset.mem_filter.mpr ⟨hpS, hp⟩)
      · exact Finset.sum_nonneg fun q hq => hterm q hq v
    linarith
  have hS : ∑ q ∈ P, Real.log q / ((q : ℝ) - 1) ≤ ∑ q ∈ S, Real.log q / ((q : ℝ) - 1) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro q _ _
    rcases q with _ | q
    · simp
    · have : (1 : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 q
      exact div_nonneg (Real.log_nonneg this) (by linarith)
  have hfin : (0 : ℝ) ≤ Module.finrank ℚ L := Nat.cast_nonneg _
  calc |Real.log (FractionalIdeal.absNorm 𝔠 : ℝ)|
      = |∑ v ∈ T, (FractionalIdeal.count L v 𝔠 : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ)| := by
        rw [h𝔠eq]
    _ ≤ ∑ v ∈ T, |(FractionalIdeal.count L v 𝔠 : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ v ∈ T, |(FractionalIdeal.count L v 𝔠 : ℝ)| * Real.log (Ideal.absNorm v.asIdeal : ℝ) :=
        Finset.sum_congr rfl fun v _ => by
          rw [abs_mul, abs_of_nonneg (log_absNorm_heightOneSpectrum_nonneg v)]
    _ ≤ ∑ v ∈ T, (∑ q ∈ P, a * (FractionalIdeal.count L v (primeFrac L q) : ℝ) / ((q : ℝ) - 1) +
          b * (FractionalIdeal.count L v (𝔇 : FractionalIdeal (𝓞 L)⁰ L) : ℝ)) *
          Real.log (Ideal.absNorm v.asIdeal : ℝ) :=
        Finset.sum_le_sum fun v _ =>
          mul_le_mul_of_nonneg_right (hv v) (log_absNorm_heightOneSpectrum_nonneg v)
    _ = ∑ q ∈ P, a / ((q : ℝ) - 1) * ∑ v ∈ T, (FractionalIdeal.count L v (primeFrac L q) : ℝ) *
          Real.log (Ideal.absNorm v.asIdeal : ℝ) +
        b * ∑ v ∈ T, (FractionalIdeal.count L v (𝔇 : FractionalIdeal (𝓞 L)⁰ L) : ℝ) *
          Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
        simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        congr 1
        · exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun v _ => by ring
        · exact Finset.sum_congr rfl fun v _ => by ring
    _ = Module.finrank ℚ L * (a * ∑ q ∈ P, Real.log q / ((q : ℝ) - 1)) +
        b * Real.log (Ideal.absNorm 𝔇 : ℝ) := by
        rw [h𝔇eq, Finset.sum_congr rfl fun q hq => by rw [hqeq q hq]]
        congr 1
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun q _ => by ring
    _ ≤ Module.finrank ℚ L * (a * ∑ q ∈ S, Real.log q / ((q : ℝ) - 1)) +
        b * Real.log (Ideal.absNorm 𝔇 : ℝ) := by
        gcongr
end NormCountBound
end GroundTheory.Heights₂.Heights.NineStatements
