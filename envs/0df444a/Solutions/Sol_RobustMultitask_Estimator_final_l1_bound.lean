-- Prove2me | solution 1 for RobustMultitask.Estimator.final_l1_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:36:19.222036+00:00
-- url     : https://prove2.me/submissions/22f1dab0-085f-4389-a767-ea6f29d53851

import Mathlib
import Definitions.Def_RobustMultitask_Estimator_VectorNotation
import Definitions.Def_RobustMultitask_Estimator_Model
import Definitions.Def_RobustMultitask_Estimator_Algorithm
import Definitions.Def_RobustMultitask_Estimator_Alignment

open RobustMultitask.Estimator in
theorem AuxFinalL1_wellAligned_card {N d : ℕ} (β : Fin N → Fin d → ℝ) (βdag : Fin d → ℝ) (s : ℕ)
    (ζ : ℝ) (hζ : 0 < ζ) (hsparse : ∀ j, l0 (β j - βdag) ≤ s) :
    ((wellAligned β βdag ζ).card : ℝ) ≤ (s : ℝ) / ζ := by
  have hmem : ∀ i, i ∈ wellAligned β βdag ζ ↔ ζ ≤ ((misalignedTasks β βdag i).card : ℝ) / N := by
    intro i
    simp [wellAligned, poorlyAligned]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have : wellAligned β βdag ζ = ∅ := by
      ext i
      rw [hmem]
      simp only [Nat.cast_zero, div_zero, Finset.notMem_empty, iff_false, not_le]
      exact hζ
    rw [this, Finset.card_empty, Nat.cast_zero]
    positivity
  · have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    -- double counting
    have hdc : ∑ i, (misalignedTasks β βdag i).card = ∑ j, l0 (β j - βdag) := by
      simp only [misalignedTasks, l0, Finset.card_filter, Pi.sub_apply, sub_ne_zero]
      exact Finset.sum_comm
    have hbound : ∑ i, (misalignedTasks β βdag i).card ≤ N * s := by
      rw [hdc]
      calc ∑ j, l0 (β j - βdag) ≤ ∑ _j : Fin N, s := Finset.sum_le_sum fun j _ => hsparse j
        _ = N * s := by simp
    have hsub : ∑ i ∈ wellAligned β βdag ζ, (misalignedTasks β βdag i).card ≤ N * s :=
      le_trans (Finset.sum_le_sum_of_subset (Finset.subset_univ _)) hbound
    have hsubR : (∑ i ∈ wellAligned β βdag ζ, ((misalignedTasks β βdag i).card : ℝ)) ≤ N * s := by
      exact_mod_cast hsub
    have hlow : ∑ i ∈ wellAligned β βdag ζ, ζ * N ≤
        ∑ i ∈ wellAligned β βdag ζ, ((misalignedTasks β βdag i).card : ℝ) := by
      refine Finset.sum_le_sum fun i hi => ?_
      have := (hmem i).mp hi
      rwa [le_div_iff₀ hNR] at this
    rw [Finset.sum_const, nsmul_eq_mul] at hlow
    rw [le_div_iff₀ hζ]
    have : ((wellAligned β βdag ζ).card : ℝ) * ζ * N ≤ s * N := by nlinarith
    nlinarith

namespace Aux_RobustMultitask_final_l1
open RobustMultitask.Estimator

theorem amgm (lam A c Q ψ : ℝ) (hψ : 0 < ψ) (hA : 0 ≤ A) (hQ : 0 ≤ Q) (hc : 0 ≤ c)
    (hAQ : A ^ 2 ≤ c * Q) : 2 * lam * A ≤ 2 * c * lam ^ 2 / ψ + ψ * Q / 2 := by
  rcases hc.eq_or_lt with h | h
  · subst h
    have : A = 0 := by nlinarith
    subst this
    have : 0 ≤ ψ * Q / 2 := by positivity
    simp only [mul_zero, zero_mul, zero_div, zero_add]
    linarith
  · have hpos : 0 < 2 * c * ψ := by positivity
    refine le_of_mul_le_mul_right ?_ hpos
    have e : (2 * c * lam ^ 2 / ψ + ψ * Q / 2) * (2 * c * ψ) = 4 * c ^ 2 * lam ^ 2 + ψ ^ 2 * (c * Q) := by
      field_simp
      ring
    rw [e]
    nlinarith [sq_nonneg (2 * lam * c - ψ * A), mul_le_mul_of_nonneg_left hAQ (sq_nonneg ψ)]

end Aux_RobustMultitask_final_l1

open RobustMultitask.Estimator Matrix Aux_RobustMultitask_final_l1 in
theorem solution {N d m : ℕ} (X : Matrix (Fin m) (Fin d) ℝ)
    (β : Fin N → Fin d → ℝ) (βdag : Fin d → ℝ) (s : ℕ) (ζ ψ : ℝ) (j : Fin N) (lam : ℝ)
    (e : Fin m → ℝ) (b βhat : Fin d → ℝ) (hm : 0 < m)
    (hsparse : ∀ k, l0 (β k - βdag) ≤ s)
    (hψ : 0 < ψ) (hSigma : MinEigAtLeast (sampleCov X) ψ)
    (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) (hlam : 0 < lam)
    (hH : (2 / (m : ℝ)) * linf (Xᵀ *ᵥ e) ≤ lam / 2)
    (hmin : IsLassoMinimizer X (X *ᵥ β j + e) lam b βhat) :
    (1 / (2 * (m : ℝ))) * l2sq (X *ᵥ (βhat - β j)) + lam / 2 * l1 (βhat - β j)
        ≤ 2 * (1 / ζ + 1) * s * lam ^ 2 / ψ
          + 2 * lam * l1 (restrict (poorlyAligned β βdag ζ) (b - βdag))
      ∧ l1 (βhat - β j)
        ≤ 6 * s * lam / (ζ * ψ) + 4 * l1 (restrict (poorlyAligned β βdag ζ) (b - βdag)) := by
  classical
  set δ := βhat - β j with hδ
  set I := augSupport β βdag ζ j with hI
  set R := l1 (restrict (poorlyAligned β βdag ζ) (b - βdag)) with hR
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  -- l2sq as dot product
  have hl2 : ∀ {k : ℕ} (v : Fin k → ℝ), l2sq v = v ⬝ᵥ v := by
    intro k v; unfold l2sq dotProduct; simp only [sq]
  set Z := (1 / (m : ℝ)) * l2sq (X *ᵥ δ) with hZ
  -- Step A: basic inequality
  have hbasic := hmin (β j)
  unfold lassoObjective at hbasic
  have e1 : X *ᵥ βhat - (X *ᵥ β j + e) = X *ᵥ δ - e := by
    rw [hδ, mulVec_sub]; abel
  have e2 : X *ᵥ β j - (X *ᵥ β j + e) = -e := by abel
  rw [e1, e2] at hbasic
  have hexp : l2sq (X *ᵥ δ - e) = l2sq (X *ᵥ δ) - 2 * ((X *ᵥ δ) ⬝ᵥ e) + l2sq e := by
    rw [hl2, hl2, hl2]
    simp only [sub_dotProduct, dotProduct_sub, dotProduct_comm e (X *ᵥ δ)]
    ring
  have hneg : l2sq (-e) = l2sq e := by unfold l2sq; simp
  rw [hexp, hneg] at hbasic
  -- cross term
  have hcross : (X *ᵥ δ) ⬝ᵥ e = δ ⬝ᵥ (Xᵀ *ᵥ e) := by
    rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
  have hlinf : ∀ i, |(Xᵀ *ᵥ e) i| ≤ linf (Xᵀ *ᵥ e) := fun i =>
    le_ciSup (f := fun i => |(Xᵀ *ᵥ e) i|) (Set.finite_range _).bddAbove i
  have hdot : δ ⬝ᵥ (Xᵀ *ᵥ e) ≤ linf (Xᵀ *ᵥ e) * l1 δ := by
    unfold dotProduct l1
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    calc δ i * (Xᵀ *ᵥ e) i ≤ |δ i * (Xᵀ *ᵥ e) i| := le_abs_self _
      _ = |δ i| * |(Xᵀ *ᵥ e) i| := abs_mul _ _
      _ ≤ |δ i| * linf (Xᵀ *ᵥ e) := mul_le_mul_of_nonneg_left (hlinf i) (abs_nonneg _)
      _ = linf (Xᵀ *ᵥ e) * |δ i| := mul_comm _ _
  have hl1nn : 0 ≤ l1 δ := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hcross2 : (2 / (m : ℝ)) * ((X *ᵥ δ) ⬝ᵥ e) ≤ lam / 2 * l1 δ := by
    rw [hcross]
    calc (2 / (m : ℝ)) * (δ ⬝ᵥ (Xᵀ *ᵥ e)) ≤ (2 / (m : ℝ)) * (linf (Xᵀ *ᵥ e) * l1 δ) :=
          mul_le_mul_of_nonneg_left hdot (by positivity)
      _ = ((2 / (m : ℝ)) * linf (Xᵀ *ᵥ e)) * l1 δ := by ring
      _ ≤ lam / 2 * l1 δ := mul_le_mul_of_nonneg_right hH hl1nn
  -- Step B: coordinatewise decomposition
  set A := ∑ i, (if i ∈ I then |δ i| else 0) with hA
  set Bc := ∑ i, (if i ∈ I then 0 else |δ i|) with hBc
  have hl1split : l1 δ = A + Bc := by
    unfold l1; rw [hA, hBc, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  have hpoor : ∀ i, i ∉ I → i ∈ poorlyAligned β βdag ζ := by
    intro i hi
    by_contra hp
    apply hi
    rw [hI]; unfold augSupport wellAligned
    exact Finset.mem_union_left _ (Finset.mem_compl.mpr hp)
  have htask : ∀ i, i ∉ I → β j i = βdag i := by
    intro i hi
    by_contra hp
    apply hi
    rw [hI]; unfold augSupport taskSupport
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
  have hcoord : ∀ i, |β j i - b i| - |βhat i - b i| ≤
      (if i ∈ I then |δ i| else 0) - (if i ∈ I then 0 else |δ i|) +
        2 * (if i ∈ poorlyAligned β βdag ζ then |b i - βdag i| else 0) := by
    intro i
    by_cases hi : i ∈ I
    · rw [if_pos hi, if_pos hi]
      have h1 : |β j i - b i| - |βhat i - b i| ≤ |(β j i - b i) - (βhat i - b i)| :=
        abs_sub_abs_le_abs_sub _ _
      have h2 : |(β j i - b i) - (βhat i - b i)| = |δ i| := by
        rw [hδ, Pi.sub_apply, abs_sub_comm]; congr 1; ring
      have h3 : 0 ≤ (if i ∈ poorlyAligned β βdag ζ then |b i - βdag i| else 0) := by
        split_ifs <;> simp
      linarith
    · rw [if_neg hi, if_neg hi, if_pos (hpoor i hi), htask i hi]
      have : |δ i| ≤ |βhat i - b i| + |b i - βdag i| := by
        rw [hδ, Pi.sub_apply, htask i hi]
        have := abs_sub_le (βhat i) (b i) (βdag i)
        linarith
      have h4 : |βdag i - b i| = |b i - βdag i| := abs_sub_comm _ _
      linarith
  have hRsum : R = ∑ i, (if i ∈ poorlyAligned β βdag ζ then |b i - βdag i| else 0) := by
    rw [hR]; unfold l1 restrict
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  have hdiff : l1 (β j - b) - l1 (βhat - b) ≤ A - Bc + 2 * R := by
    unfold l1
    rw [← Finset.sum_sub_distrib, hA, hBc, hRsum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => by simpa using hcoord i
  -- Step C
  have hZineq : Z + lam / 2 * Bc ≤ 3 * lam / 2 * A + 2 * lam * R := by
    have : (1 / (m : ℝ)) * (l2sq (X *ᵥ δ) - 2 * ((X *ᵥ δ) ⬝ᵥ e) + l2sq e) =
        Z - (2 / (m : ℝ)) * ((X *ᵥ δ) ⬝ᵥ e) + (1 / (m : ℝ)) * l2sq e := by
      rw [hZ]; ring
    rw [this] at hbasic
    rw [hl1split] at hcross2
    nlinarith
  -- Step D: Cauchy–Schwarz and restricted eigenvalue
  set Q := δ ⬝ᵥ δ with hQ
  have hQnn : 0 ≤ Q := by
    rw [hQ]; unfold dotProduct; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hAI : A = ∑ i ∈ I, |δ i| := by
    rw [hA, Finset.sum_ite_mem, Finset.univ_inter]
  have hCS : A ^ 2 ≤ (I.card : ℝ) * Q := by
    rw [hAI]
    have h1 := sq_sum_le_card_mul_sum_sq (s := I) (f := fun i => |δ i|)
    have h2 : ∑ i ∈ I, |δ i| ^ 2 ≤ Q := by
      rw [hQ]; unfold dotProduct
      calc ∑ i ∈ I, |δ i| ^ 2 ≤ ∑ i, |δ i| ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun i _ _ => sq_nonneg _)
        _ = ∑ i, δ i * δ i := Finset.sum_congr rfl fun i _ => by rw [sq_abs, sq]
    have h3 : (0 : ℝ) ≤ I.card := Nat.cast_nonneg _
    calc (∑ i ∈ I, |δ i|) ^ 2 ≤ (I.card : ℝ) * ∑ i ∈ I, |δ i| ^ 2 := by exact_mod_cast h1
      _ ≤ (I.card : ℝ) * Q := mul_le_mul_of_nonneg_left h2 h3
  have hRE : ψ * Q ≤ Z := by
    have := hSigma δ
    rw [hZ, hl2]
    unfold sampleCov at this
    rw [smul_mulVec, ← mulVec_mulVec, dotProduct_smul, smul_eq_mul, dotProduct_mulVec,
      vecMul_transpose] at this
    exact this
  -- Step E: support size
  have hcard : (I.card : ℝ) ≤ (1 / ζ + 1) * s := by
    have h1 : I.card ≤ (wellAligned β βdag ζ).card + (taskSupport β βdag j).card :=
      Finset.card_union_le _ _
    have h2 := AuxFinalL1_wellAligned_card β βdag s ζ hζ0 hsparse
    have h3 : ((taskSupport β βdag j).card : ℝ) ≤ s := by
      have := hsparse j
      unfold l0 at this
      unfold taskSupport
      have e : (Finset.univ.filter fun i => (β j - βdag) i ≠ 0) =
          Finset.univ.filter fun i => β j i ≠ βdag i := by
        ext i; simp [sub_eq_zero]
      rw [e] at this
      exact_mod_cast this
    have h1' : (I.card : ℝ) ≤ (wellAligned β βdag ζ).card + (taskSupport β βdag j).card := by
      exact_mod_cast h1
    have : (s : ℝ) / ζ = 1 / ζ * s := by ring
    nlinarith
  -- Step F
  have hAnn : 0 ≤ A := Finset.sum_nonneg fun i _ => by split_ifs <;> simp
  have hBnn : 0 ≤ Bc := Finset.sum_nonneg fun i _ => by split_ifs <;> simp
  have ham := amgm lam A (I.card : ℝ) Q ψ hψ hAnn hQnn (Nat.cast_nonneg _) hCS
  have hc0 : 2 * (I.card : ℝ) * lam ^ 2 / ψ ≤ 2 * (1 / ζ + 1) * s * lam ^ 2 / ψ := by
    apply div_le_div_of_nonneg_right _ hψ.le
    have : 0 ≤ lam ^ 2 := sq_nonneg _
    nlinarith
  have hT1 : (1 / (2 * (m : ℝ))) * l2sq (X *ᵥ δ) + lam / 2 * l1 δ ≤
      2 * (1 / ζ + 1) * s * lam ^ 2 / ψ + 2 * lam * R := by
    have e : (1 / (2 * (m : ℝ))) * l2sq (X *ᵥ δ) = Z / 2 := by rw [hZ]; field_simp
    rw [e, hl1split]
    linarith
  refine ⟨hT1, ?_⟩
  have hZnn : 0 ≤ (1 / (2 * (m : ℝ))) * l2sq (X *ᵥ δ) := by
    rw [hl2]; unfold dotProduct
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
  have h1 : lam / 2 * l1 δ ≤ 2 * (1 / ζ + 1) * s * lam ^ 2 / ψ + 2 * lam * R := by linarith
  have h2 : l1 δ ≤ 4 * (1 / ζ + 1) * s * lam / ψ + 4 * R := by
    have e : 2 * (1 / ζ + 1) * s * lam ^ 2 / ψ + 2 * lam * R =
        lam / 2 * (4 * (1 / ζ + 1) * s * lam / ψ + 4 * R) := by field_simp; ring
    rw [e] at h1
    exact le_of_mul_le_mul_left h1 (by linarith)
  have h3 : 4 * (1 / ζ + 1) * s * lam / ψ ≤ 6 * s * lam / (ζ * ψ) := by
    rw [div_le_div_iff₀ hψ (by positivity)]
    have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg _
    have : 4 * (1 / ζ + 1) * ζ = 4 + 4 * ζ := by field_simp
    have hk : 0 ≤ (s : ℝ) * lam * ψ := by positivity
    calc 4 * (1 / ζ + 1) * s * lam * (ζ * ψ) = (4 * (1 / ζ + 1) * ζ) * ((s : ℝ) * lam * ψ) := by
          ring
      _ = (4 + 4 * ζ) * ((s : ℝ) * lam * ψ) := by rw [this]
      _ ≤ 6 * ((s : ℝ) * lam * ψ) := mul_le_mul_of_nonneg_right (by linarith) hk
      _ = 6 * s * lam * ψ := by ring
  linarith
