-- Prove2me | solution 1 for SYKFastMix.FastMixing.corollary_11
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:16:48.099038+00:00
-- url     : https://prove2.me/submissions/527e0f60-010a-4845-a133-78ed88ba0ab3

import Mathlib
import Theorems.Thm_SYKFastMix_FastMixing_traceMoment_opNorm_bounds
import Theorems.Thm_SYKFastMix_FastMixing_lemma_9
import Theorems.Thm_SYKFastMix_FastMixing_lemma_10

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open scoped Matrix.Norms.L2Operator
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ComplexOrder
open SYKFastMix.FastMixing

namespace SYKFastMix.FastMixing
variable {Ω : Type} [TopologicalSpace Ω]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

@[fun_prop] private lemma continuous_applySuper (T : Ω → Super ι) (X : Ω → Mat ι)
    (hT : Continuous T) (hX : Continuous X) :
    Continuous (fun w ↦ applySuper (T w) (X w)) := by
  unfold applySuper
  fun_prop

@[fun_prop] private lemma continuous_ad : Continuous (ad : Mat ι → Super ι) := by
  unfold ad super
  fun_prop

@[fun_prop] private lemma continuous_hamiltonian {N : ℕ} (Q : Model N) :
    Continuous (hamiltonian Q) := by
  unfold hamiltonian
  fun_prop

@[fun_prop] private lemma continuous_gammaCoefficient {N : ℕ} (Q : Model N) (m : ℕ) (i : Fin N) :
    Continuous (fun w ↦ gammaCoefficient Q w m i) := by
  unfold gammaCoefficient
  fun_prop

@[fun_prop] private lemma continuous_fermionCoefficient {N : ℕ} (Q : Model N) (m : ℕ) :
    Continuous (fun w ↦ fermionCoefficient Q w m) := by
  unfold fermionCoefficient anticomm
  fun_prop

end SYKFastMix.FastMixing

theorem solution {N : ℕ} (Q : Model N) (m p : ℕ) (hm : 1 ≤ m) (hp : 1 ≤ p) (hmp : m * p ≤ 7 * N) :
  Integrable (fun w => SYKEdge.opNorm (fermionCoefficient Q w m)^(2*p)) (disorderLaw Q) ∧
  (∫ w, SYKEdge.opNorm (fermionCoefficient Q w m)^(2*p) ∂disorderLaw Q) ≤
    (N : ℝ) * 2^(N/2) * (105 * Q.J)^(2*p*m) := by
  have hN := Q.size
  letI : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  have h9 := lemma_9 Q m p hm hp
  have h10 := lemma_10 Q m p hm hp hmp
  have hmeas : AEStronglyMeasurable
      (fun w ↦ SYKEdge.opNorm (fermionCoefficient Q w m)^(2*p)) (disorderLaw Q) := by
    change AEStronglyMeasurable (fun w ↦ ‖fermionCoefficient Q w m‖^(2*p)) _
    exact ((continuous_fermionCoefficient Q m).norm.pow _).aestronglyMeasurable
  have hint := h9.1.mono' hmeas (Filter.Eventually.of_forall fun w ↦ by
    rw [Real.norm_of_nonneg (pow_nonneg (show 0 ≤ SYKEdge.opNorm _ from norm_nonneg _) _)]
    exact (traceMoment_opNorm_bounds p (fermionCoefficient Q w m)).1)
  refine ⟨hint, ?_⟩
  have hc : (∫ w, traceMoment p (classicalCoefficient w m (fun _ ↦ 1)) ∂disorderLaw Q) ≤
      (N : ℝ) * ∫ w, SYKEdge.opNorm (classicalCoefficient w m (fun _ ↦ 1))^(2*p) ∂disorderLaw Q := by
    rw [← integral_const_mul]
    apply integral_mono h9.2.1 (h10.1.const_mul _)
    intro w
    simpa using (traceMoment_opNorm_bounds p (classicalCoefficient w m (fun _ ↦ 1))).2
  have hb : (∫ w, SYKEdge.opNorm (classicalCoefficient w m (fun _ ↦ 1))^(2*p) ∂disorderLaw Q) ≤
      (105 * Q.J)^(2*p*m) := by
    have hi : 0 ≤ ∫ w, SYKEdge.opNorm (classicalCoefficient w m (fun _ ↦ 1))^(2*p) ∂disorderLaw Q :=
      integral_nonneg fun w ↦ pow_nonneg (norm_nonneg _) _
    have hr : 0 < 2 * (p : ℝ) := by positivity
    have hj : 0 ≤ (105 * Q.J)^m := pow_nonneg (mul_nonneg (by norm_num) Q.positive.le) _
    have hroot := h10.2
    change (∫ w, SYKEdge.opNorm (classicalCoefficient w m (fun _ ↦ 1))^(2*p) ∂disorderLaw Q) ^
      (1 / (2 * (p : ℝ))) ≤ (105 * Q.J)^m at hroot
    have h := (Real.rpow_inv_le_iff_of_pos hi hj hr).mp (by simpa only [one_div] using hroot)
    norm_cast at h
    simpa only [← pow_mul, Nat.mul_comm m (2*p)] using h
  have hscale : (∫ w, traceMoment p (fermionCoefficient Q w m) ∂disorderLaw Q) ≤
      (2 ^ (N / 2) : ℝ) * ∫ w, traceMoment p (classicalCoefficient w m (fun _ ↦ 1)) ∂disorderLaw Q := by
    have h := (div_le_iff₀ (by positivity : (0:ℝ) < 2^(N/2))).mp
      (show (∫ w, traceMoment p (fermionCoefficient Q w m) ∂disorderLaw Q) / (2^(N/2) : ℝ) ≤
        ∫ w, traceMoment p (classicalCoefficient w m (fun _ ↦ 1)) ∂disorderLaw Q by
          simpa only [div_eq_mul_inv, one_mul, mul_comm] using h9.2.2)
    simpa only [mul_comm] using h
  calc
    (∫ w, SYKEdge.opNorm (fermionCoefficient Q w m)^(2*p) ∂disorderLaw Q) ≤
        ∫ w, traceMoment p (fermionCoefficient Q w m) ∂disorderLaw Q :=
      integral_mono hint h9.1 fun w ↦ (traceMoment_opNorm_bounds p _).1
    _ ≤ _ := hscale
    _ ≤ (2 ^ (N / 2) : ℝ) * ((N : ℝ) *
        ∫ w, SYKEdge.opNorm (classicalCoefficient w m (fun _ ↦ 1))^(2*p) ∂disorderLaw Q) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ ≤ (2 ^ (N / 2) : ℝ) * ((N : ℝ) * (105 * Q.J)^(2*p*m)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (by positivity)) (by positivity)
    _ = _ := by ring
