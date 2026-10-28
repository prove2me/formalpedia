-- Prove2me | solution 1 for QAlgorithms.Nannicini.implicitMeasurement
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T12:09:30.438703+00:00
-- url     : https://prove2.me/submissions/c2674da1-4e35-444a-ba40-e6719556b031

import Definitions.Def_QAlgorithms_Defs_Measurement
set_option autoImplicit false

namespace QAlgorithms.Nannicini.A3IM
open QAlgorithms
open scoped ComplexOrder

lemma prob_eq {q : ℕ} (ψ : EuclideanSpace ℂ (Qubits q)) (z : Qubits q) : prob ψ z = ‖ψ z‖ ^ 2 := by
  simp [prob, ket, EuclideanSpace.inner_single_left]

lemma probEvent_eq {q : ℕ} (ψ : EuclideanSpace ℂ (Qubits q)) (k : Fin q) (x : Bool) :
    probEvent ψ (fun j => j k = x) = ∑ z, if z k = x then ‖ψ z‖ ^ 2 else 0 := by
  unfold probEvent
  rw [Finset.sum_filter]
  simp only [prob_eq]

lemma collapse_apply {q : ℕ} (ψ : EuclideanSpace ℂ (Qubits q)) (k : Fin q) (x : Bool)
    (z : Qubits q) :
    ‖collapseQubit ψ k x z‖ ^ 2 =
      (probEvent ψ (fun j => j k = x))⁻¹ * (if z k = x then ‖ψ z‖ ^ 2 else 0) := by
  unfold collapseQubit
  have hp : 0 ≤ probEvent ψ (fun j => j k = x) := by
    rw [probEvent_eq]; exact Finset.sum_nonneg fun z _ => by split_ifs <;> positivity
  simp only [PiLp.smul_apply, smul_eq_mul, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow,
    Real.sq_sqrt hp]
  split_ifs with h <;> simp [h]

noncomputable def F {q : ℕ} (ψ : EuclideanSpace ℂ (Qubits q)) (l : List (Fin q)) (y : Qubits q) : ℝ :=
  ∑ z, if (∀ k ∈ l, z k = y k) then ‖ψ z‖ ^ 2 else 0

lemma closed {q : ℕ} (y : Qubits q) :
    ∀ (l : List (Fin q)) (ψ : EuclideanSpace ℂ (Qubits q)), (∑ z, ‖ψ z‖ ^ 2) = 1 →
      seqMeasProb ψ l y = F ψ l y := by
  intro l
  induction l with
  | nil =>
    intro ψ hψ
    simp [seqMeasProb, F, hψ]
  | cons k l ih =>
    intro ψ hψ
    rw [seqMeasProb]
    set p := probEvent ψ (fun j => j k = y k) with hpdef
    have hp' : p = ∑ z, if z k = y k then ‖ψ z‖ ^ 2 else 0 := probEvent_eq ψ k (y k)
    by_cases hp : p = 0
    · rw [hp, zero_mul]
      have hz : ∀ z, z k = y k → ‖ψ z‖ ^ 2 = 0 := by
        intro z hz
        have := (Finset.sum_eq_zero_iff_of_nonneg
          (fun z _ => by split_ifs <;> positivity :
            ∀ z ∈ Finset.univ, 0 ≤ (if z k = y k then ‖ψ z‖ ^ 2 else 0))).mp
          (hp' ▸ hp) z (Finset.mem_univ _)
        simpa [hz] using this
      symm
      unfold F
      refine Finset.sum_eq_zero fun z _ => ?_
      split_ifs with h
      · exact hz z (h k List.mem_cons_self)
      · rfl
    · have h0 : (0:ℝ) ≤ p := by
        rw [hp']; exact Finset.sum_nonneg fun z _ => by split_ifs <;> positivity
      have hnorm : (∑ z, ‖collapseQubit ψ k (y k) z‖ ^ 2) = 1 := by
        simp only [collapse_apply, ← hpdef, ← Finset.mul_sum, ← hp']
        exact inv_mul_cancel₀ hp
      rw [ih _ hnorm]
      unfold F
      simp only [collapse_apply, ← hpdef]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      simp only [List.forall_mem_cons]
      by_cases h1 : z k = y k
      · by_cases h2 : ∀ k ∈ l, z k = y k
        · simp only [h1, if_true, true_and]
          rw [if_pos h2, if_pos h2, ← mul_assoc, mul_inv_cancel₀ hp, one_mul]
        · simp [h2]
      · simp [h1]

theorem main {q : ℕ} (ψ : EuclideanSpace ℂ (Qubits q)) (hψ : IsState ψ)
    (l r : List (Fin q)) (hlr : (l ++ r).Nodup) (y : Qubits q) :
    seqMeasProb ψ l y =
      ∑ z ∈ Finset.univ.filter (fun z : Qubits q => ∀ i, i ∉ r → z i = y i),
        seqMeasProb ψ (l ++ r) z := by
  have hN : (∑ z, ‖ψ z‖ ^ 2) = 1 := by
    have := EuclideanSpace.norm_eq ψ
    unfold IsState at hψ
    rw [hψ] at this
    have h2 := congrArg (· ^ 2) this
    simp only [one_pow] at h2
    rw [h2, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  have hdisj : ∀ k ∈ l, k ∉ r := by
    intro k hk hkr
    exact (List.nodup_append.mp hlr).2.2 k hk k hkr rfl
  rw [closed y l ψ hN]
  simp only [closed _ (l ++ r) ψ hN, F, Finset.sum_filter]
  have hite : ∀ a : Qubits q, (if (∀ i, i ∉ r → a i = y i) then
      ∑ x, (if (∀ k ∈ l ++ r, x k = a k) then ‖ψ x‖ ^ 2 else 0) else 0) =
      ∑ x, (if (∀ i, i ∉ r → a i = y i) then
        (if (∀ k ∈ l ++ r, x k = a k) then ‖ψ x‖ ^ 2 else 0) else 0) := by
    intro a; split_ifs <;> simp
  simp only [hite]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  -- the unique z
  let z0 : Qubits q := fun i => if i ∈ r then w i else y i
  rw [Finset.sum_eq_single z0]
  · have hA : (∀ i, i ∉ r → z0 i = y i) := by intro i hi; simp [z0, hi]
    by_cases hw : ∀ k ∈ l, w k = y k
    · have hB : ∀ k ∈ l ++ r, w k = z0 k := by
        intro k hk
        rcases List.mem_append.mp hk with hk | hk
        · simp [z0, hdisj k hk, hw k hk]
        · simp [z0, hk]
      rw [if_pos hA, if_pos hB, if_pos hw]
    · have hB : ¬ ∀ k ∈ l ++ r, w k = z0 k := by
        intro hB; apply hw; intro k hk
        have := hB k (List.mem_append_left _ hk)
        simpa [z0, hdisj k hk] using this
      rw [if_neg hw, if_pos hA, if_neg hB]
  · intro z _ hz
    split_ifs with h1 h2 <;> try rfl
    exfalso; apply hz
    funext i
    by_cases hi : i ∈ r
    · simp [z0, hi, h2 i (List.mem_append_right _ hi)]
    · simp [z0, hi, h1 i hi]
  · simp

end QAlgorithms.Nannicini.A3IM

theorem solution {q : ℕ} (ψ : EuclideanSpace ℂ (QAlgorithms.Qubits q)) (hψ : QAlgorithms.IsState ψ)
    (l r : List (Fin q)) (hlr : (l ++ r).Nodup) (y : QAlgorithms.Qubits q) :
    QAlgorithms.seqMeasProb ψ l y =
      ∑ z ∈ Finset.univ.filter (fun z : QAlgorithms.Qubits q => ∀ i, i ∉ r → z i = y i),
        QAlgorithms.seqMeasProb ψ (l ++ r) z :=
  QAlgorithms.Nannicini.A3IM.main ψ hψ l r hlr y
