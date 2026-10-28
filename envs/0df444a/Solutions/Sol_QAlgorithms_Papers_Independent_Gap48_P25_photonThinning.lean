-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P25.photonThinning
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T23:20:50.264254+00:00
-- url     : https://prove2.me/submissions/0e65d3c0-49ab-47ed-b850-66568976d213

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P25

open QAlgorithms.Papers.Independent.Gap48.P25
noncomputable section


open scoped BigOperators ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)


namespace P25ThinH
open QAlgorithms.Papers.Independent.Gap48.P25 Finset

def eqv (n : ℕ) : (Fin n → Bool) ≃ Finset (Fin n) where
  toFun b := univ.filter (fun i => b i = true)
  invFun s := fun i => decide (i ∈ s)
  left_inv b := by ext i; simp
  right_inv s := by ext i; simp

lemma surv (n : ℕ) (t : ℝ) (k : ℕ) :
    survivorLaw n t k = (n.choose k : ℝ) * t^k * (1-t)^(n-k) := by
  unfold survivorLaw lossPattern
  have hp : ∀ b : Fin n → Bool, (∏ i, if b i then t else 1-t) =
      t^(eqv n b).card * (1-t)^(n - (eqv n b).card) := by
    intro b
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun i => b i = true)
    simp only [card_univ, Fintype.card_fin] at h
    simp only [eqv, Equiv.coe_fn_mk]
    congr 2
    simp only [Bool.not_eq_true] at h ⊢
    omega
  simp_rw [hp]
  refine (Fintype.sum_equiv (eqv n) (fun b => if (eqv n b).card = k then
    t^(eqv n b).card*(1-t)^(n-(eqv n b).card) else 0)
    (fun s => if s.card = k then t^s.card*(1-t)^(n-s.card) else 0) (fun b => rfl)).trans ?_
  rw [← Finset.sum_filter]
  have hf : univ.filter (fun s : Finset (Fin n) => s.card = k) = powersetCard k univ := by
    rw [powersetCard_eq_filter, powerset_univ]
  rw [hf, Finset.sum_congr rfl (g := fun _ => t^k*(1-t)^(n-k))
    (by intro s hs; rw [(mem_powersetCard.1 hs).2])]
  simp [card_powersetCard]; ring

lemma survsum (n : ℕ) (t : ℝ) : ∑ k ∈ range (n+1), survivorLaw n t k = 1 := by
  have := add_pow t (1-t) n
  simp only [add_sub_cancel, one_pow] at this
  rw [this]; apply sum_congr rfl; intro k _; rw [surv]; ring

lemma survnn (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) (k : ℕ) : 0 ≤ survivorLaw n t k := by
  rw [surv]; have := ht.1; have : 0 ≤ 1 - t := by linarith [ht.2]
  positivity

lemma survzero (n : ℕ) (t : ℝ) (k : ℕ) (hk : n < k) : survivorLaw n t k = 0 := by
  rw [surv, Nat.choose_eq_zero_of_lt hk]; simp

lemma survle (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) (k : ℕ) : survivorLaw n t k ≤ 1 := by
  by_cases hk : k ≤ n
  · rw [← survsum n t]
    exact single_le_sum (f := fun k => survivorLaw n t k) (fun i _ => survnn n t ht i)
      (mem_range.2 (by omega))
  · rw [survzero n t k (by omega)]; norm_num

lemma hs (p : PhotonLaw) (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ∀ k, Summable (fun n => p.mass n * survivorLaw n t k) := fun k =>
  Summable.of_nonneg_of_le (fun n => mul_nonneg (p.nonnegative n) (survnn n t ht k))
    (fun n => mul_le_of_le_one_right (p.nonnegative n) (survle n t ht k))
    p.normalized.summable

lemma h2 (p : PhotonLaw) (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : ∀ k, thinned p t k = ∑' m : ℕ,
      p.mass (m+k)*(Nat.choose (m+k) k : ℝ)*t^k*(1-t)^m := by
  intro k; unfold thinned
  rw [← (hs p t ht k).sum_add_tsum_nat_add k]
  have : ∑ i ∈ Finset.range k, p.mass i * survivorLaw i t k = 0 := by
    apply Finset.sum_eq_zero; intro i hi
    rw [survzero i t k (Finset.mem_range.1 hi), mul_zero]
  rw [this, zero_add]; congr 1; funext m
  rw [surv, Nat.add_sub_cancel]; ring

end P25ThinH

/-- IV.A.1, PDF p.27: independent-loss thinning. Corrects the printed reciprocal
factorial k!/[n!(n-k)!] to Nat.choose; n=2,k=1 requires 2, not 1/2.
Round-one independent moderation confirmed this minimal correction. -/
theorem solution (p : PhotonLaw) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (∀ n k, survivorLaw n t k =
      if k ≤ n then (Nat.choose n k : ℝ)*t^k*(1-t)^(n-k) else 0) ∧
    (∀ k, thinned p t k = ∑' m : ℕ,
      p.mass (m+k)*(Nat.choose (m+k) k : ℝ)*t^k*(1-t)^m) ∧
    (∀ k, 0 ≤ thinned p t k) ∧ HasSum (thinned p t) 1 ∧
    thinned p 0 = vacuumLaw.mass ∧ thinned p 1 = p.mass := by
  have hs := P25ThinH.hs p t ht
  have h2 := P25ThinH.h2 p t ht
  refine ⟨fun n k => ?_, h2, fun k => tsum_nonneg (fun n => mul_nonneg (p.nonnegative n)
    (P25ThinH.survnn n t ht k)), ?_, ?_, ?_⟩
  · rw [P25ThinH.surv]; split_ifs with h
    · rfl
    · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  · let F : ℕ × ℕ → ℝ := fun q => p.mass q.1 * survivorLaw q.1 t q.2
    have hF0 : 0 ≤ F := fun q => mul_nonneg (p.nonnegative _) (P25ThinH.survnn _ t ht _)
    have fib : ∀ n, HasSum (fun k => F (n,k)) (p.mass n) := by
      intro n
      have e : p.mass n = ∑ k ∈ Finset.range (n+1), F (n,k) := by
        simp only [F, ← Finset.mul_sum, P25ThinH.survsum, mul_one]
      rw [e]
      exact hasSum_sum_of_ne_finset_zero (fun k hk => by
          simp only [F]; rw [P25ThinH.survzero n t k (by simpa using hk), mul_zero])
    have hsF : Summable F := (summable_prod_of_nonneg hF0).2
      ⟨fun n => (fib n).summable, by simp_rw [(fib _).tsum_eq]; exact p.normalized.summable⟩
    have h1 := hsF.hasSum.prod_fiberwise fib
    have hT : ∑' q, F q = 1 := h1.unique p.normalized
    have hG : HasSum (F ∘ (Equiv.prodComm ℕ ℕ)) 1 := by
      rw [(Equiv.prodComm ℕ ℕ).hasSum_iff, ← hT]; exact hsF.hasSum
    have := hG.prod_fiberwise (fun k => (hG.summable.prod_factor k).hasSum)
    exact this
  · funext k; rw [P25ThinH.h2 p 0 ⟨le_refl _, zero_le_one⟩]
    rcases k with _ | k
    · simp [vacuumLaw]; exact p.normalized.tsum_eq
    · simp [vacuumLaw]
  · funext k; rw [P25ThinH.h2 p 1 ⟨zero_le_one, le_refl _⟩]
    rw [tsum_eq_single 0 (fun m hm => by simp [zero_pow hm])]
    simp




