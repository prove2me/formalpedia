-- Prove2me | solution 1 for SYKFastMix.FastMixing.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T14:35:08.866049+00:00
-- url     : https://prove2.me/submissions/4d94755b-880f-45a9-b3f0-d5ea5ea46ac7

import Mathlib
import Definitions.Def_SYKFastMix_FastMixing_Coefficients
import Definitions.Def_SYKFastMix_FastMixing_CompactGaussian
import Theorems.Thm_SYKFastMix_FastMixing_corollary_15
import Theorems.Thm_SYKFastMix_FastMixing_lemma_8
import Theorems.Thm_SYKFastMix_FastMixing_corollary_6
import Theorems.Thm_SYKFastMix_FastMixing_lemma_3
import Theorems.Thm_SYKFastMix_FastMixing_eq_2_33

noncomputable section
open scoped Matrix.Norms.L2Operator
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ComplexOrder
namespace SYKFastMix.FastMixing

lemma rawString_hermitian_of_card_four {N : ℕ} (Q : Model N)
    (S : Finset (Fin N)) (hS : S.card = 4) : (rawString Q S).IsHermitian := by
  unfold rawString Matrix.IsHermitian
  rw [Matrix.conjTranspose_list_prod]
  have hlen : (S.sort (· ≤ ·)).length = 4 := by simpa using hS
  have hnodup : (S.sort (· ≤ ·)).Nodup := S.sort_nodup (· ≤ ·)
  obtain ⟨a, b, c, d, hlist⟩ := List.length_eq_four.mp hlen
  rw [hlist] at hnodup
  simp at hnodup
  rcases hnodup with ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩
  rw [hlist]
  simp
  rw [(Q.car.herm a).eq, (Q.car.herm b).eq, (Q.car.herm c).eq, (Q.car.herm d).eq]
  calc
    Q.γ d * (Q.γ c * (Q.γ b * Q.γ a)) =
        (Q.γ d * Q.γ c) * (Q.γ b * Q.γ a) := by noncomm_ring
    _ = -(Q.γ c * Q.γ d) * (Q.γ b * Q.γ a) := by
          rw [Q.car.anticomm d c (Ne.symm hcd)]
    _ = Q.γ c * (-(Q.γ d * Q.γ b) * Q.γ a) := by noncomm_ring
    _ = Q.γ c * (Q.γ b * Q.γ d * Q.γ a) := by
          rw [Q.car.anticomm d b (Ne.symm hbd)]
          noncomm_ring
    _ = (Q.γ c * Q.γ b) * (Q.γ d * Q.γ a) := by noncomm_ring
    _ = -(Q.γ b * Q.γ c) * (Q.γ d * Q.γ a) := by
          rw [Q.car.anticomm c b (Ne.symm hbc)]
    _ = Q.γ b * Q.γ c * (Q.γ a * Q.γ d) := by
          rw [Q.car.anticomm d a (Ne.symm had)]
          noncomm_ring
    _ = Q.γ b * (Q.γ c * Q.γ a) * Q.γ d := by noncomm_ring
    _ = -(Q.γ b * (Q.γ a * Q.γ c) * Q.γ d) := by
          rw [Q.car.anticomm c a (Ne.symm hac)]
          noncomm_ring
    _ = -((Q.γ b * Q.γ a) * (Q.γ c * Q.γ d)) := by noncomm_ring
    _ = (Q.γ a * Q.γ b) * (Q.γ c * Q.γ d) := by
          rw [Q.car.anticomm b a (Ne.symm hab)]
          noncomm_ring
    _ = Q.γ a * (Q.γ b * (Q.γ c * Q.γ d)) := by noncomm_ring

lemma hamiltonian_hermitian {N : ℕ} (Q : Model N) (w : Disorder N) :
    (hamiltonian Q w).IsHermitian := by
  unfold hamiltonian Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro A hA
  rw [Matrix.conjTranspose_smul, (rawString_hermitian_of_card_four Q A.1 A.2).eq]
  simp

end SYKFastMix.FastMixing

open SYKFastMix.FastMixing

theorem solution {N : ℕ} (Q : Model N) :
  ∃ A : Set (Disorder N), MeasurableSet A ∧
    ENNReal.ofReal (1 - 2 * Real.exp (-(N : ℝ))) ≤ disorderLaw Q A ∧
    ∀ w ∈ A, ∀ β : ℝ, 0 ≤ β → β ≤ 1 / (1000 * Q.J) →
      HasGap (discriminant (hamiltonian Q w) Q.γ β) (gibbsRoot (hamiltonian Q w) β) (507/392) ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        mixingTime (lindblad (hamiltonian Q w) Q.γ β) (gibbs (hamiltonian Q w) β) ε ≤
          ENNReal.ofReal ((392/507 : ℝ) * ((N : ℝ)/4 * Real.log 2 +
            2 * β * Q.J * N + Real.log (1/ε))) := by
  obtain ⟨A, hAmeas, hAprob, hA⟩ := corollary_15 Q
  refine ⟨A, hAmeas, hAprob, ?_⟩
  intro w hw β hβ hβupper
  have hgood := hA w hw
  have hJ : 0 < Q.J := Q.positive
  have hβJ : 0 ≤ β * Q.J ∧ β * Q.J ≤ 1 / 1000 := by
    constructor
    · exact mul_nonneg hβ hJ.le
    · calc
        β * Q.J ≤ (1 / (1000 * Q.J)) * Q.J :=
          mul_le_mul_of_nonneg_right hβupper hJ.le
        _ = 1 / 1000 := by field_simp
  have hsβ2 : 133 * Q.J * |β / 2| < 1 := by
    rw [abs_of_nonneg (div_nonneg hβ (by norm_num))]
    nlinarith [hβJ.2]
  have hjraw := (hgood.2 (β / 2) hsβ2).1
  have hjac : SYKEdge.opNorm (jacobian Q w (β / 2) - 1) ≤ 1 / 4 := by
    apply hjraw.trans
    apply (div_le_iff₀ (sub_pos.mpr hsβ2)).2
    rw [abs_of_nonneg (div_nonneg hβ (by norm_num))]
    nlinarith [hβJ.2]
  have hsβ4 : 133 * Q.J * |β / 4| < 1 := by
    rw [abs_of_nonneg (div_nonneg hβ (by norm_num))]
    nlinarith [hβJ.2]
  have hMraw := (hgood.2 (β / 4) hsβ4).2.1
  have ht : 133 * Q.J * |β / 4| ≤ 133 / 4000 := by
    rw [abs_of_nonneg (div_nonneg hβ (by norm_num))]
    nlinarith [hβJ.2]
  have ht0 : 0 ≤ 133 * Q.J * |β / 4| := by positivity
  have hbase : (3867 / 4000 : ℝ) ≤ 1 - 133 * Q.J * |β / 4| := by
    linarith
  have hsq : (3867 / 4000 : ℝ) ^ 2 ≤ (1 - 133 * Q.J * |β / 4|) ^ 2 :=
    by simpa [pow_two] using mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 3867 / 4000) hbase
  have hM : SYKEdge.opNorm (blockM Q w (β / 4)) ≤ 150 * Q.J := by
    apply hMraw.trans
    apply (div_le_iff₀ (sq_pos_of_pos (sub_pos.mpr hsβ4))).2
    nlinarith
  have hunfiltered := (lemma_8 Q w β hβ hjac).1
  have hcomparison := (corollary_6 Q w β hβJ hM).1
  let a : ℝ := (13 / 14 : ℝ) ^ 2 * (3 / 4)
  have ha : 0 < a := by
    dsimp [a]
    norm_num
  have hform : ∀ X, hsInner (gibbsRoot (hamiltonian Q w) β) X = 0 →
      a * hsSq X ≤ qform (filteredK Q w β) X := by
    intro X hX
    calc
      a * hsSq X = (13 / 14 : ℝ)^2 * ((3 / 4 : ℝ) * hsSq X) := by
        dsimp [a]
        ring
      _ ≤ (13 / 14 : ℝ)^2 * qform (unfilteredK Q w β) X :=
        mul_le_mul_of_nonneg_left (hunfiltered X hX) (sq_nonneg _)
      _ ≤ qform (filteredK Q w β) X := hcomparison X
  have hgap0 := lemma_3 Q w β a hβ ha hform
  have hgap : HasGap (discriminant (hamiltonian Q w) Q.γ β)
      (gibbsRoot (hamiltonian Q w) β) (507 / 392) := by
    convert hgap0 using 1 <;> dsimp [a] <;> norm_num
  refine ⟨hgap, ?_⟩
  have hmix := (eq_2_33 (hamiltonian Q w) Q.γ (hamiltonian_hermitian Q w)
    Q.car.herm β (507 / 392) hβ (by norm_num) hgap).2
  intro ε hε hε1
  apply (hmix ε hε hε1).trans
  apply ENNReal.ofReal_le_ofReal
  have hβop : β * SYKEdge.opNorm (hamiltonian Q w) ≤ β * (2 * Q.J * N) :=
    mul_le_mul_of_nonneg_left hgood.1 hβ
  obtain ⟨k, hk⟩ := Q.even
  have hhalf : N / 2 = k := by omega
  have hNcast : (N : ℝ) = 2 * (k : ℝ) := by
    rw [hk]
    push_cast
    ring
  have hlog : Real.log (Fintype.card (SiteHilbert N) : ℝ) =
      (N : ℝ) / 2 * Real.log 2 := by
    simp only [SiteHilbert, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    rw [hhalf, hNcast]
    ring
  rw [hlog]
  norm_num
  nlinarith
