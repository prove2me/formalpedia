-- Prove2me | solution 1 for RobustPCA.Recovery.theorem_2_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T08:53:45.767663+00:00
-- url     : https://prove2.me/submissions/5e581179-7646-401f-a5fc-b03b8e34e3b9

import Mathlib
import Definitions.Def_RobustPCA_Recovery_Setup

set_option autoImplicit false

open MatrixCompletion

namespace RPCA23

open RobustPCA.Recovery
open scoped BigOperators Classical

lemma l1_le_add {n : ℕ} (A B : RealMatrix n n) : l1Norm (A + B) ≤ l1Norm A + l1Norm B := by
  unfold l1Norm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun j _ => ?_)
  simpa using abs_add_le (A i j) (B i j)

/-- Elimination (Theorem 2.2 of the source, elementary form): exactness passes to any matrix
that agrees with `S0` on its own support. -/
lemma elim {n : ℕ} (lam : ℝ) (L0 S0 S0' : RealMatrix n n) (hlam : 0 ≤ lam)
    (hexact : IsPCPExact lam L0 S0) (htr : ∀ i j, S0' i j ≠ 0 → S0' i j = S0 i j) :
    IsPCPExact lam L0 S0' := by
  intro L S hLS hne
  have hsplit : l1Norm S0 = l1Norm S0' + l1Norm (S0 - S0') := by
    unfold l1Norm
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    show |S0 i j| = |S0' i j| + |S0 i j - S0' i j|
    by_cases h : S0' i j = 0
    · simp [h]
    · rw [htr i j h]; simp
  have hfeas : L + (S + (S0 - S0')) = L0 + S0 := by
    rw [← add_assoc, hLS]; abel
  have hne' : (L, S + (S0 - S0')) ≠ (L0, S0) := by
    intro h
    apply hne
    simp only [Prod.mk.injEq] at h ⊢
    refine ⟨h.1, ?_⟩
    calc S = (S + (S0 - S0')) - (S0 - S0') := by abel
      _ = S0' := by rw [h.2]; abel
  have h1 := hexact L (S + (S0 - S0')) hfeas hne'
  have h2 := mul_le_mul_of_nonneg_left (l1_le_add S (S0 - S0')) hlam
  rw [hsplit, mul_add] at h1
  rw [mul_add] at h2
  linarith

lemma flip_trim {n : ℕ} (S : RealMatrix n n) (Ω P : Finset (Fin n × Fin n)) (hP : P ⊆ Ω) :
    ∀ i j, samplingProjection P S i j ≠ 0 →
      samplingProjection P S i j =
        |S i j| * signPattern Ω
          (symmDiff P (Ω ∩ Finset.univ.filter (fun p : Fin n × Fin n => S p.1 p.2 < 0))) i j := by
  intro i j h
  have hin : (i, j) ∈ P := by
    by_contra hc; apply h; simp [samplingProjection, hc]
  have hΩ : (i, j) ∈ Ω := hP hin
  simp only [samplingProjection, if_pos hin, signPattern, Finset.mem_symmDiff, Finset.mem_inter,
    Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hs : S i j < 0
  · simp [hin, hΩ, hs, abs_of_neg hs]
  · rw [not_lt] at hs
    simp [hin, not_lt.2 hs, abs_of_nonneg hs]

lemma weight_c {n : ℕ} (ρ : ℝ) (Ω : Finset (Fin n × Fin n)) :
    bernoulliObservationWeight (2 * ρ) Ω * (1 / 2 : ℝ) ^ Ω.card =
      ρ ^ Ω.card * (1 - 2 * ρ) ^ (Fintype.card (Fin n × Fin n) - Ω.card) := by
  unfold bernoulliObservationWeight
  rw [mul_right_comm, ← mul_pow, show 2 * ρ * (1 / 2) = ρ by ring]

lemma super_sum {n : ℕ} (ρ : ℝ) (P : Finset (Fin n × Fin n)) :
    ∑ Ω : Finset (Fin n × Fin n),
        (if P ⊆ Ω then ρ ^ Ω.card * (1 - 2 * ρ) ^ (Fintype.card (Fin n × Fin n) - Ω.card)
          else 0)
      = bernoulliObservationWeight ρ P := by
  rw [← Finset.sum_filter]
  have hcP : Pᶜ.card = Fintype.card (Fin n × Fin n) - P.card := Finset.card_compl P
  rw [Finset.sum_nbij' (fun Ω => Ω \ P) (fun D => D ∪ P) (t := Pᶜ.powerset)
    (g := fun D => ρ ^ P.card * (ρ ^ D.card * (1 - 2 * ρ) ^ (Pᶜ.card - D.card)))]
  · rw [← Finset.mul_sum, Finset.sum_pow_mul_eq_add_pow, bernoulliObservationWeight, hcP]
    rw [show ρ + (1 - 2 * ρ) = 1 - ρ by ring]
  · intro Ω _
    rw [Finset.mem_powerset]
    intro x hx
    rw [Finset.mem_compl]
    exact (Finset.mem_sdiff.1 hx).2
  · intro D _
    simp
  · intro Ω hΩ
    have hPΩ : P ⊆ Ω := (Finset.mem_filter.1 hΩ).2
    exact Finset.sdiff_union_of_subset hPΩ
  · intro D hD
    rw [Finset.mem_powerset] at hD
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨h | h, h'⟩
      · exact h
      · exact absurd h h'
    · intro h
      exact ⟨Or.inl h, Finset.mem_compl.1 (hD h)⟩
  · intro Ω hΩ
    have hPΩ : P ⊆ Ω := (Finset.mem_filter.1 hΩ).2
    have hc := Finset.card_sdiff_add_card_eq_card hPΩ
    show ρ ^ Ω.card * (1 - 2 * ρ) ^ (Fintype.card (Fin n × Fin n) - Ω.card) =
      ρ ^ P.card * (ρ ^ (Ω \ P).card * (1 - 2 * ρ) ^ (Pᶜ.card - (Ω \ P).card))
    rw [hcP, ← hc, pow_add,
      show Fintype.card (Fin n × Fin n) - ((Ω \ P).card + P.card) =
        Fintype.card (Fin n × Fin n) - P.card - (Ω \ P).card by omega]
    ring

end RPCA23

open RPCA23 in
open scoped Classical in
open MatrixCompletion RobustPCA.Recovery in
theorem solution {n : ℕ} (lam ρs : ℝ) (L0 S : RealMatrix n n) (hlam : 0 ≤ lam)
    (hρ0 : 0 ≤ ρs) (hρ1 : ρs ≤ 1 / 2) :
    randomSignProb (2 * ρs) (fun E => IsPCPExact lam L0 (fun i j => |S i j| * E i j)) ≤
      bernoulliEventProb ρs (fun Ω => IsPCPExact lam L0 (samplingProjection Ω S)) := by
  set T : Finset (Fin n × Fin n) := Finset.univ.filter (fun p => S p.1 p.2 < 0) with hT
  set c : Finset (Fin n × Fin n) → ℝ := fun Ω =>
    ρs ^ Ω.card * (1 - 2 * ρs) ^ (Fintype.card (Fin n × Fin n) - Ω.card) with hc
  have hc0 : ∀ Ω, 0 ≤ c Ω := fun Ω =>
    mul_nonneg (pow_nonneg hρ0 _) (pow_nonneg (by linarith) _)
  set G := (fun E : RealMatrix n n =>
    RobustPCA.Recovery.IsPCPExact lam L0 (fun i j => |S i j| * E i j)) with hG
  set F := (fun Ω : Finset (Fin n × Fin n) =>
    RobustPCA.Recovery.IsPCPExact lam L0 (samplingProjection Ω S)) with hF
  have step1 : RobustPCA.Recovery.randomSignProb (2 * ρs) G =
      ∑ Ω' : Finset (Fin n × Fin n), ∑ P ∈ Ω'.powerset,
        c Ω' * (if G (RobustPCA.Recovery.signPattern Ω' (symmDiff P (Ω' ∩ T))) then 1 else 0) := by
    unfold RobustPCA.Recovery.randomSignProb
    refine Finset.sum_congr rfl (fun Ω' _ => ?_)
    simp_rw [weight_c]
    refine Finset.sum_nbij' (fun P => symmDiff P (Ω' ∩ T)) (fun P => symmDiff P (Ω' ∩ T))
      ?_ ?_ ?_ ?_ ?_
    · intro P hP
      rw [Finset.mem_powerset] at hP ⊢
      exact symmDiff_le (le_sup_of_le_right hP) (le_sup_of_le_right Finset.inter_subset_left)
    · intro P hP
      rw [Finset.mem_powerset] at hP ⊢
      exact symmDiff_le (le_sup_of_le_right hP) (le_sup_of_le_right Finset.inter_subset_left)
    · intro P _
      exact symmDiff_symmDiff_cancel_right _ _
    · intro P _
      exact symmDiff_symmDiff_cancel_right _ _
    · intro P _
      simp only [hc, symmDiff_symmDiff_cancel_right]
  have step2 : ∑ Ω' : Finset (Fin n × Fin n), ∑ P ∈ Ω'.powerset,
        c Ω' * (if G (RobustPCA.Recovery.signPattern Ω' (symmDiff P (Ω' ∩ T))) then 1 else 0) ≤
      ∑ Ω' : Finset (Fin n × Fin n), ∑ P ∈ Ω'.powerset, c Ω' * (if F P then 1 else 0) := by
    refine Finset.sum_le_sum (fun Ω' _ => Finset.sum_le_sum (fun P hP => ?_))
    refine mul_le_mul_of_nonneg_left ?_ (hc0 Ω')
    rw [Finset.mem_powerset] at hP
    by_cases hGP : G (RobustPCA.Recovery.signPattern Ω' (symmDiff P (Ω' ∩ T)))
    · have hFP : F P := elim lam L0 _ _ hlam hGP (flip_trim S Ω' P hP)
      simp [hGP, hFP]
    · simp only [hGP, if_false]
      split_ifs <;> norm_num
  have step3 : ∑ Ω' : Finset (Fin n × Fin n), ∑ P ∈ Ω'.powerset, c Ω' * (if F P then 1 else 0) =
      bernoulliEventProb ρs F := by
    have hrw : ∀ Ω' : Finset (Fin n × Fin n), ∑ P ∈ Ω'.powerset, c Ω' * (if F P then 1 else 0) =
        ∑ P : Finset (Fin n × Fin n), if P ⊆ Ω' then c Ω' * (if F P then 1 else 0) else 0 := by
      intro Ω'
      rw [← Finset.sum_filter]
      congr 1
      ext P
      simp
    simp_rw [hrw]
    rw [Finset.sum_comm]
    unfold bernoulliEventProb
    refine Finset.sum_congr rfl (fun P _ => ?_)
    have hss := super_sum ρs P
    have : ∑ Ω' : Finset (Fin n × Fin n),
        (if P ⊆ Ω' then c Ω' * (if F P then 1 else 0) else 0) =
        (∑ Ω' : Finset (Fin n × Fin n), if P ⊆ Ω' then c Ω' else 0) *
          (if F P then 1 else 0) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun Ω' _ => ?_)
      split_ifs <;> simp
    rw [this]
    simp only [hc] at hss ⊢
    rw [hss]
    split_ifs <;> simp
  rw [step1]
  exact step2.trans step3.le
