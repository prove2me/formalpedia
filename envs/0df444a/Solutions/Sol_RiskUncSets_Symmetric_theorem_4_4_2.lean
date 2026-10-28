-- Prove2me | solution 2 for RiskUncSets.Symmetric.theorem_4_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T07:31:18.928993+00:00
-- url     : https://prove2.me/submissions/4d698030-b9c6-48f8-ba64-1f90435e4b0a

import Mathlib
import Definitions.Def_RiskUncSets_Symmetric_Setting
import Theorems.Thm_RiskUncSets_Symmetric_symRestrictedSimplex_subset_mixtures

-- carved verbatim out of submission 19b3cf27-7226-40e9-a9b5-9bf71ca5688a, lines 383-402

section
set_option autoImplicit false
open RiskUncSets
open RiskUncSets.Symmetric

lemma p84_sphere_mem {n : ℕ} {S : Set (Fin n → ℝ)} {r : ℝ}
    (hS : ∀ x ∈ S, ∑ k, x k ^ 2 = r) {y : Fin n → ℝ} (hy : y ∈ convexHull ℝ S)
    (hyr : ∑ k, y k ^ 2 = r) : y ∈ S := by
  obtain ⟨ι, _, w, z, hw0, hw1, hz, hx⟩ := mem_convexHull_iff_exists_fintype.mp hy
  have hyk : ∀ k, ∑ i, w i * z i k = y k := by
    intro k
    have := congrFun hx k
    simpa [Finset.sum_apply, smul_eq_mul] using this
  have hzero : ∑ i, w i * ∑ k, (z i k - y k) ^ 2 = 0 := by
    have e1 : ∀ i, w i * ∑ k, (z i k - y k) ^ 2
        = w i * (∑ k, z i k ^ 2) - 2 * ∑ k, y k * (w i * z i k) + w i * ∑ k, y k ^ 2 := by
      intro i
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring
    rw [Finset.sum_congr rfl (fun i _ => e1 i), Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_comm (f := fun i k => y k * (w i * z i k))]
    have h2 : ∀ k, ∑ i, y k * (w i * z i k) = y k ^ 2 := by
      intro k; rw [← Finset.mul_sum, hyk k]; ring
    rw [Finset.sum_congr rfl (fun k _ => h2 k), ← Finset.sum_mul, hw1,
      Finset.sum_congr rfl (fun i _ => by rw [hS (z i) (hz i)])]
    rw [← Finset.sum_mul, hw1, hyr]
    ring
  have hnn : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ w i * ∑ k, (z i k - y k) ^ 2 :=
    fun i _ => mul_nonneg (hw0 i) (Finset.sum_nonneg (fun k _ => sq_nonneg _))
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra h
    push Not at h
    simp [h] at hw1
  have hsq : ∑ k, (z i k - y k) ^ 2 = 0 := by
    have := hall i (Finset.mem_univ _)
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hi
    · exact h
  have hk := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (z i k - y k))).mp hsq
  have : z i = y := by
    funext k
    have := hk k (Finset.mem_univ _)
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith
  rw [← this]; exact hz i

lemma p84_reflect {N n : ℕ} (q : Fin N → ℝ) (σ : Equiv.Perm (Fin N))
    (hσ : q = fun i => 2 / (N : ℝ) - q (σ i)) (a : Fin N → Fin n → ℝ) :
    ∀ x ∈ permutohull q a, (2 : ℝ) • sampleMean a - x ∈ permutohull q a := by
  have hv : ∀ τ : Equiv.Perm (Fin N), (2 : ℝ) • sampleMean a - ∑ i, q (τ i) • a i
      = ∑ i, q ((σ * τ) i) • a i := by
    intro τ
    unfold sampleMean
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have h : q (τ i) = 2 / (N : ℝ) - q (σ (τ i)) := congrFun hσ (τ i)
    rw [Equiv.Perm.mul_apply, smul_smul, ← sub_smul]
    congr 1
    rw [h]; ring
  intro x hx
  unfold permutohull at hx ⊢
  have key : convexHull ℝ (Set.range fun τ : Equiv.Perm (Fin N) => ∑ i, q (τ i) • a i) ⊆
      {x | (2 : ℝ) • sampleMean a - x ∈
        convexHull ℝ (Set.range fun τ : Equiv.Perm (Fin N) => ∑ i, q (τ i) • a i)} := by
    refine convexHull_min ?_ ?_
    · rintro _ ⟨τ, rfl⟩
      simp only [Set.mem_ofPred_eq]
      rw [hv τ]
      exact subset_convexHull ℝ _ ⟨σ * τ, rfl⟩
    · intro u hu v hv' s t hs ht hst
      simp only [Set.mem_ofPred_eq] at hu hv' ⊢
      have e : (2 : ℝ) • sampleMean a - (s • u + t • v)
          = s • ((2 : ℝ) • sampleMean a - u) + t • ((2 : ℝ) • sampleMean a - v) := by
        obtain rfl : t = 1 - s := by linarith
        module
      rw [e]
      exact (convex_convexHull ℝ _) hu hv' hs ht hst
  exact key hx

lemma p84_C1_mpr {N n : ℕ} (q : Fin N → ℝ) (σ : Equiv.Perm (Fin N))
    (hσ : q = fun i => 2 / (N : ℝ) - q (σ i)) (a : Fin N → Fin n → ℝ) :
    CentrallySymmetric (permutohull q a) (sampleMean a) := by
  have hR := p84_reflect q σ hσ a
  have hv1 : ∑ i, q ((1 : Equiv.Perm (Fin N)) i) • a i ∈ permutohull q a :=
    subset_convexHull ℝ _ ⟨1, rfl⟩
  have hc : Convex ℝ (permutohull q a) := convex_convexHull ℝ _
  refine ⟨?_, ?_⟩
  · have hm := hc hv1 (hR _ hv1) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    convert hm using 1
    module
  · intro x hx
    have := hR _ hx
    convert this using 1
    module

lemma p84_C1_mp {N : ℕ} (hN : 0 < N) (q : Fin N → ℝ)
    (hq : q ∈ restrictedSimplex N)
    (h : ∀ (n : ℕ) (a : Fin N → Fin n → ℝ),
      CentrallySymmetric (permutohull q a) (sampleMean a)) :
    ∃ σ : Equiv.Perm (Fin N), q = fun i => 2 / (N : ℝ) - q (σ i) := by
  classical
  set a : Fin N → Fin N → ℝ := fun i k => if k = i then 1 else 0 with ha
  have hvert : ∀ τ : Equiv.Perm (Fin N), (∑ i, q (τ i) • a i) = fun k => q (τ k) := by
    intro τ; funext k
    simp [ha, Finset.sum_apply, smul_eq_mul]
  have hmean : sampleMean a = fun _ => 1 / (N : ℝ) := by
    funext k
    simp [sampleMean, ha, Finset.sum_apply, smul_eq_mul]
  obtain ⟨_, hcs⟩ := h N a
  have hq1 : q ∈ permutohull q a := by
    have : (∑ i, q ((1 : Equiv.Perm (Fin N)) i) • a i) ∈ permutohull q a :=
      subset_convexHull ℝ _ ⟨1, rfl⟩
    rw [hvert] at this
    simpa using this
  have hy := hcs (q - sampleMean a) (by simpa using hq1)
  set y : Fin N → ℝ := sampleMean a - (q - sampleMean a) with hydef
  have hyk : ∀ k, y k = 2 / (N : ℝ) - q k := by
    intro k
    simp only [hydef, hmean, Pi.sub_apply]
    ring
  have hsumq : ∑ k, q k = 1 := hq.1.2
  have hS : ∀ x ∈ Set.range (fun τ : Equiv.Perm (Fin N) => ∑ i, q (τ i) • a i),
      ∑ k, x k ^ 2 = ∑ k, q k ^ 2 := by
    rintro _ ⟨τ, rfl⟩
    show ∑ k, (∑ i, q (τ i) • a i) k ^ 2 = _
    rw [hvert τ]
    exact Equiv.sum_comp τ (fun k => q k ^ 2)
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hyr : ∑ k, y k ^ 2 = ∑ k, q k ^ 2 := by
    have e : ∀ k, y k ^ 2 = q k ^ 2 + (4 / (N : ℝ) ^ 2 - 4 / (N : ℝ) * q k) := by
      intro k; rw [hyk]; ring
    rw [Finset.sum_congr rfl (fun k _ => e k), Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hsumq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
    ring
  obtain ⟨τ, hτ⟩ := p84_sphere_mem hS hy hyr
  refine ⟨τ, ?_⟩
  have hτ' : (fun k => q (τ k)) = y := by rw [← hvert τ]; exact hτ
  funext k
  have := congrFun hτ' k
  rw [this, hyk]
  ring

lemma p84_qbar_rev {N : ℕ} (j : Fin (Nhat N)) (i : Fin N) :
    2 / (N : ℝ) - qbar j i = qbar j (Fin.rev i) := by
  have hj : (j : ℕ) < N / 2 + 1 := j.isLt
  have hi : (i : ℕ) < N := i.isLt
  unfold qbar
  simp only [Fin.val_rev]
  split_ifs <;> first | ring1 | (exfalso; omega)

lemma p84_qbar_nonneg {N : ℕ} (j : Fin (Nhat N)) (i : Fin N) : 0 ≤ qbar j i := by
  unfold qbar
  split_ifs <;> positivity

lemma p84_qbar_anti {N : ℕ} (j : Fin (Nhat N)) : Antitone (qbar j) := by
  intro a b hab
  have hab' : (a : ℕ) ≤ b := hab
  have h1 : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  have h2 : 1 / (N : ℝ) ≤ 2 / (N : ℝ) := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N); norm_num
  unfold qbar
  split_ifs <;> first | exact le_refl _ | linarith | (exfalso; omega)

lemma p84_mixture {N : ℕ} (hN : 0 < N)
    (lam : Fin (Nhat N) → ℝ) (h0 : ∀ j, 0 ≤ lam j)
    (h1 : ∑ j, lam j = 1) :
    (∑ j, lam j • qbar j) ∈ symRestrictedSimplex N := by
  set q : Fin N → ℝ := ∑ j, lam j • qbar j with hqdef
  have hq : ∀ i, q i = ∑ j, lam j * qbar j i := by
    intro i; simp [hqdef, Finset.sum_apply, smul_eq_mul]
  have hsym : ∀ i : Fin N, 2 / (N : ℝ) - q i = q (Fin.rev i) := by
    intro i
    rw [hq, hq]
    have : 2 / (N : ℝ) = ∑ j, lam j * (2 / (N : ℝ)) := by
      rw [← Finset.sum_mul, h1, one_mul]
    rw [this, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← p84_qbar_rev, mul_sub]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, Fin.revPerm, ?_⟩
  · intro i
    rw [hq]
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (h0 j) (p84_qbar_nonneg j i))
  · have hrev : ∑ i, q (Fin.rev i) = ∑ i, q i :=
      Fintype.sum_equiv Fin.revPerm _ _ (fun _ => rfl)
    have hsum : ∑ i, (2 / (N : ℝ) - q i) = ∑ i, q (Fin.rev i) :=
      Finset.sum_congr rfl (fun i _ => hsym i)
    rw [hrev, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hsum
    have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have : (N : ℝ) * (2 / (N : ℝ)) = 2 := by field_simp
    linarith
  · intro a b hab
    rw [hq, hq]
    exact Finset.sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_left (p84_qbar_anti j hab) (h0 j))
  · funext i
    show q i = 2 / (N : ℝ) - q (Fin.revPerm i)
    rw [Fin.revPerm_apply, ← hsym]
    ring

lemma p84_muQ_sum {N : ℕ} (lam : Fin (Nhat N) → ℝ) (X : Fin N → ℝ) :
    muQ (∑ j, lam j • qbar j) X = ∑ j, lam j * muQ (qbar j) X := by
  unfold muQ
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, mul_neg,
    Finset.mul_sum, Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

end

section
set_option autoImplicit false

open RiskUncSets.Symmetric in
theorem solution {N : ℕ} (hN : 0 < N)
    (μ : (Fin N → ℝ) → ℝ) :
    (∃ q ∈ restrictedSimplex N,
      (∀ X, μ X = muQ q X) ∧
      ∀ (n : ℕ) (a : Fin N → Fin n → ℝ),
        CentrallySymmetric (permutohull q a) (sampleMean a)) ↔
    ∃ lam : Fin (Nhat N) → ℝ,
      (∀ j, 0 ≤ lam j) ∧
      ∑ j, lam j = 1 ∧
      ∀ X, μ X = ∑ j, lam j * muQ (qbar j) X := by
  constructor
  · rintro ⟨q, hq, hμ, hcs⟩
    obtain ⟨σ, hσ⟩ := p84_C1_mp hN q hq hcs
    obtain ⟨lam, h0, h1, hqe⟩ := RiskUncSets.Symmetric.symRestrictedSimplex_subset_mixtures hN q ⟨hq, σ, hσ⟩
    refine ⟨lam, h0, h1, fun X => ?_⟩
    rw [hμ, hqe, p84_muQ_sum]
  · rintro ⟨lam, h0, h1, hμ⟩
    obtain ⟨hq, σ, hσ⟩ := p84_mixture hN lam h0 h1
    exact ⟨_, hq, fun X => by rw [hμ, p84_muQ_sum], fun n a => p84_C1_mpr _ σ hσ a⟩

end
