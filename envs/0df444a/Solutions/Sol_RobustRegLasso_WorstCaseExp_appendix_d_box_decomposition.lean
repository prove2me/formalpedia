-- Prove2me | solution 1 for RobustRegLasso.WorstCaseExp.appendix_d_box_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T02:10:55.873575+00:00
-- url     : https://prove2.me/submissions/ab1ce782-f0e1-4b1b-a674-803ea27fdded

import Mathlib
import Definitions.Def_RobustRegLasso_WorstCaseExp_Basic

namespace RobustRegLasso.WorstCaseExp

private lemma box_eq_pi {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b σ : Fin n → ℝ)
    (Δ : Matrix (Fin n) (Fin m) ℝ) (i : Fin n) :
    box A b σ Δ i = Set.pi Set.univ
      (Fin.cons (Set.Icc (b i - σ i) (b i + σ i))
        (fun j => Set.Icc (A i j - Δ i j) (A i j + Δ i j))) := by
  ext z
  simp [box, Fin.forall_fin_succ]

private lemma isCompact_box {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b σ : Fin n → ℝ)
    (Δ : Matrix (Fin n) (Fin m) ℝ) (i : Fin n) :
    IsCompact (box A b σ Δ i) := by
  rw [box_eq_pi]
  refine isCompact_univ_pi fun k => ?_
  refine Fin.cases ?_ (fun _ => ?_) k <;> exact isCompact_Icc

private lemma continuous_sqLoss {m : ℕ} (x : Fin m → ℝ) :
    Continuous (sqLoss x) := by
  unfold sqLoss
  exact (((continuous_apply 0).sub
    (continuous_finsetSum _ fun j _ => (continuous_apply j.succ).mul continuous_const)).pow 2)

private lemma set1_eq_set2 {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (b : Fin n → ℝ) (c : ℝ) (x : Fin m → ℝ) :
    {v : ℝ | ∃ (σ : Fin n → ℝ) (Δ : Matrix (Fin n) (Fin m) ℝ),
      Admissible c σ Δ ∧ v = l2norm (b + σ - Matrix.mulVec (A + Δ) x)} =
    {v : ℝ | ∃ (σ : Fin n → ℝ) (Δ : Matrix (Fin n) (Fin m) ℝ),
      Admissible c σ Δ ∧ ∃ p : Fin n → Fin (m + 1) → ℝ,
        (∀ i, p i ∈ box A b σ Δ i) ∧ v = Real.sqrt (∑ i, sqLoss x (p i))} := by
  ext v
  constructor
  · rintro ⟨σ, Δ, hAdm, rfl⟩
    let σ' : Fin n → ℝ := fun i => |σ i|
    let Δ' : Matrix (Fin n) (Fin m) ℝ := fun i j => |Δ i j|
    have hAdm' : Admissible c σ' Δ' := by
      refine ⟨?_, fun j => ?_⟩
      · simpa [σ', l2norm] using hAdm.1
      · simpa [Δ', l2norm] using hAdm.2 j
    let p : Fin n → Fin (m + 1) → ℝ :=
      fun i => Fin.cons (b i + σ i) (fun j => A i j + Δ i j)
    refine ⟨σ', Δ', hAdm', p, ?_, ?_⟩
    · intro i
      refine ⟨?_, fun j => ?_⟩
      · simp only [p, σ', Fin.cons_zero, Set.mem_Icc]
        constructor <;> linarith [neg_abs_le (σ i), le_abs_self (σ i)]
      · simp only [p, Δ', Fin.cons_succ, Set.mem_Icc]
        constructor <;> linarith [neg_abs_le (Δ i j), le_abs_self (Δ i j)]
    · unfold l2norm sqLoss
      congr 1
  · rintro ⟨σ, Δ, hAdm, p, hp, rfl⟩
    let σ'' : Fin n → ℝ := fun i => p i 0 - b i
    let Δ'' : Matrix (Fin n) (Fin m) ℝ := fun i j => p i j.succ - A i j
    have hAdm'' : Admissible c σ'' Δ'' := by
      refine ⟨?_, fun j => ?_⟩
      · refine le_trans ?_ hAdm.1
        unfold l2norm
        refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
        have hi := (hp i).1
        rw [Set.mem_Icc] at hi
        rw [sq_le_sq, abs_le]
        constructor <;> linarith [le_abs_self (σ i)]
      · refine le_trans ?_ (hAdm.2 j)
        unfold l2norm
        refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
        have hij := (hp i).2 j
        rw [Set.mem_Icc] at hij
        rw [sq_le_sq, abs_le]
        constructor <;> linarith [le_abs_self (Δ i j)]
    refine ⟨σ'', Δ'', hAdm'', ?_⟩
    unfold l2norm sqLoss
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have hvec : (b + σ'' - Matrix.mulVec (A + Δ'') x) i =
        p i 0 - ∑ j : Fin m, p i j.succ * x j := by
      simp only [Pi.sub_apply, Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.add_apply]
      simp only [σ'', Δ'', add_sub_cancel]
    rw [hvec]

private lemma upperBounds_set2_eq_set3 {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (b : Fin n → ℝ) (c : ℝ) (x : Fin m → ℝ) :
    upperBounds {v : ℝ | ∃ (σ : Fin n → ℝ) (Δ : Matrix (Fin n) (Fin m) ℝ),
      Admissible c σ Δ ∧ ∃ p : Fin n → Fin (m + 1) → ℝ,
        (∀ i, p i ∈ box A b σ Δ i) ∧ v = Real.sqrt (∑ i, sqLoss x (p i))} =
    upperBounds {v : ℝ | ∃ (σ : Fin n → ℝ) (Δ : Matrix (Fin n) (Fin m) ℝ),
      Admissible c σ Δ ∧ ∃ s : Fin n → ℝ,
        (∀ i, IsGreatest (sqLoss x '' box A b σ Δ i) (s i)) ∧
          v = Real.sqrt (∑ i, s i)} := by
  classical
  ext u
  constructor
  · intro hu v ⟨σ, Δ, hAdm, s, hs, hv⟩
    choose p hp_mem hp_eq using fun i => (hs i).1
    apply hu
    refine ⟨σ, Δ, hAdm, p, hp_mem, ?_⟩
    rw [hv]
    congr 1
    exact Finset.sum_congr rfl fun i _ => (hp_eq i).symm
  · intro hu v ⟨σ, Δ, hAdm, p, hp, hv⟩
    have hex : ∀ i : Fin n, ∃ si : ℝ, IsGreatest (sqLoss x '' box A b σ Δ i) si := by
      intro i
      have hK : IsCompact (sqLoss x '' box A b σ Δ i) :=
        (isCompact_box A b σ Δ i).image (continuous_sqLoss x)
      have hne : (sqLoss x '' box A b σ Δ i).Nonempty := ⟨sqLoss x (p i), p i, hp i, rfl⟩
      exact ⟨sSup (sqLoss x '' box A b σ Δ i), hK.sSup_mem hne,
        (isLUB_csSup hne hK.bddAbove).1⟩
    choose s hs using hex
    have hle : v ≤ Real.sqrt (∑ i, s i) := by
      rw [hv]
      refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
      exact (hs i).2 ⟨p i, hp i, rfl⟩
    exact hle.trans (hu ⟨σ, Δ, hAdm, s, hs, rfl⟩)

end RobustRegLasso.WorstCaseExp

open RobustRegLasso.WorstCaseExp in
theorem solution {n m : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin m) ℝ)
    (b : Fin n → ℝ) (c : ℝ) (hc : 0 ≤ c) (x : Fin m → ℝ) (L : ℝ) :
    (IsLUB {v : ℝ | ∃ (σ : Fin n → ℝ) (Δ : Matrix (Fin n) (Fin m) ℝ),
        Admissible c σ Δ ∧ v = l2norm (b + σ - Matrix.mulVec (A + Δ) x)} L ↔
      IsLUB {v : ℝ | ∃ (σ : Fin n → ℝ) (Δ : Matrix (Fin n) (Fin m) ℝ),
        Admissible c σ Δ ∧ ∃ p : Fin n → Fin (m + 1) → ℝ,
          (∀ i, p i ∈ box A b σ Δ i) ∧ v = Real.sqrt (∑ i, sqLoss x (p i))} L) ∧
    (IsLUB {v : ℝ | ∃ (σ : Fin n → ℝ) (Δ : Matrix (Fin n) (Fin m) ℝ),
        Admissible c σ Δ ∧ ∃ p : Fin n → Fin (m + 1) → ℝ,
          (∀ i, p i ∈ box A b σ Δ i) ∧ v = Real.sqrt (∑ i, sqLoss x (p i))} L ↔
      IsLUB {v : ℝ | ∃ (σ : Fin n → ℝ) (Δ : Matrix (Fin n) (Fin m) ℝ),
        Admissible c σ Δ ∧ ∃ s : Fin n → ℝ,
          (∀ i, IsGreatest (sqLoss x '' box A b σ Δ i) (s i)) ∧
            v = Real.sqrt (∑ i, s i)} L) := by
  have _ := hn
  have _ := hc
  refine ⟨?_, ?_⟩
  · rw [set1_eq_set2]
  · simp only [IsLUB, upperBounds_set2_eq_set3]
