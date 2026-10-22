-- Prove2me | solution 1 for RiskUncSets.Symmetric.symRestrictedSimplex_subset_mixtures
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T00:55:02.198192+00:00
-- url     : https://prove2.me/submissions/cf532c4a-ca7b-4fc5-b9b6-8a82725e2ad0

import Mathlib
import Definitions.Def_RiskUncSets_Symmetric_Setting



namespace RiskUncSets.Symmetric

lemma refl_mem_permutohull {N n : ℕ} (q : Fin N → ℝ) (σ : Equiv.Perm (Fin N))
    (hσ : q = fun i => 2 / (N : ℝ) - q (σ i)) (a : Fin N → Fin n → ℝ) :
    ∀ y ∈ permutohull q a, (2:ℝ) • sampleMean a - y ∈ permutohull q a := by
  intro y hy
  unfold permutohull at hy ⊢
  have hconv : Convex ℝ {y : Fin n → ℝ | (2:ℝ) • sampleMean a - y ∈
      convexHull ℝ (Set.range fun τ : Equiv.Perm (Fin N) => ∑ i, q (τ i) • a i)} := by
    intro x hx y hy s t hs ht hst
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    have e : (2:ℝ) • sampleMean a - (s • x + t • y)
        = s • ((2:ℝ) • sampleMean a - x) + t • ((2:ℝ) • sampleMean a - y) := by
      have : t = 1 - s := by linarith
      subst this
      module
    rw [e]
    exact convex_convexHull ℝ _ hx hy hs ht hst
  have hsub : (Set.range fun τ : Equiv.Perm (Fin N) => ∑ i, q (τ i) • a i) ⊆
      {y : Fin n → ℝ | (2:ℝ) • sampleMean a - y ∈
        convexHull ℝ (Set.range fun τ : Equiv.Perm (Fin N) => ∑ i, q (τ i) • a i)} := by
    rintro _ ⟨τ, rfl⟩
    show _ ∈ convexHull ℝ _
    apply subset_convexHull
    refine ⟨σ * τ, ?_⟩
    simp only [Equiv.Perm.mul_apply]
    unfold sampleMean
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hq : q (σ (τ i)) = 2 / (N:ℝ) - q (τ i) := by
      have := congrFun hσ (τ i)
      linarith
    rw [hq]
    module
  exact convexHull_min hsub hconv hy

lemma symm_of_perm {N n : ℕ} (q : Fin N → ℝ) (σ : Equiv.Perm (Fin N))
    (hσ : q = fun i => 2 / (N : ℝ) - q (σ i)) (a : Fin N → Fin n → ℝ) :
    CentrallySymmetric (permutohull q a) (sampleMean a) := by
  have hrefl := refl_mem_permutohull q σ hσ a
  have hy : (∑ i, q ((1 : Equiv.Perm (Fin N)) i) • a i) ∈ permutohull q a :=
    subset_convexHull ℝ _ ⟨1, rfl⟩
  have h2 := hrefl _ hy
  have h0 : sampleMean a ∈ permutohull q a := by
    have e : sampleMean a = (1/2:ℝ) • (∑ i, q ((1 : Equiv.Perm (Fin N)) i) • a i) +
        (1/2:ℝ) • ((2:ℝ) • sampleMean a - ∑ i, q ((1 : Equiv.Perm (Fin N)) i) • a i) := by
      module
    rw [e]
    exact convex_convexHull ℝ _ hy h2 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨h0, fun x hx => ?_⟩
  have := hrefl _ hx
  have e : (2:ℝ) • sampleMean a - (sampleMean a + x) = sampleMean a - x := by module
  rwa [e] at this

lemma rev_of_symm {N : ℕ} (hN : 0 < N) (q : Fin N → ℝ) (hq : q ∈ restrictedSimplex N)
    (h : CentrallySymmetric
      (permutohull q (fun i : Fin N => (Pi.single i (1:ℝ) : Fin N → ℝ)))
      (sampleMean (fun i : Fin N => (Pi.single i (1:ℝ) : Fin N → ℝ)))) :
    ∀ i, q i + q (Fin.rev i) = 2 / (N:ℝ) := by
  obtain ⟨⟨hnn, hsum⟩, hanti⟩ := hq
  set e : Fin N → Fin N → ℝ := fun i => (Pi.single i (1:ℝ) : Fin N → ℝ) with he
  have hgen : ∀ τ : Equiv.Perm (Fin N), ∑ i, q (τ i) • e i = fun k => q (τ k) := by
    intro τ
    ext k
    simp [he, Finset.sum_apply, Pi.single_apply]
  have hmean : sampleMean e = fun _ => 1 / (N:ℝ) := by
    ext k
    simp [sampleMean, he, Finset.sum_apply, Pi.single_apply]
  have hqP : q ∈ permutohull q e := by
    apply subset_convexHull ℝ _
    refine ⟨1, ?_⟩
    simpa using hgen 1
  have hw : (fun k => 2 / (N:ℝ) - q k) ∈ permutohull q e := by
    have := h.2 (q - fun _ => 1 / (N:ℝ)) (by
      rw [hmean]; convert hqP using 1; ext k; simp)
    rw [hmean] at this
    convert this using 1
    ext k; simp; ring
  -- halfspace bound
  have hk : ∀ k : ℕ, (∑ j : Fin N, if (j:ℕ) < k then (2 / (N:ℝ) - q (Fin.rev j)) else 0) ≤
      ∑ j : Fin N, if (j:ℕ) < k then q j else 0 := by
    intro k
    let c : Fin N → ℝ := fun j => if (j:ℕ) < k then 1 else 0
    have hc : Antitone c := by
      intro i j hij
      simp only [c]
      by_cases hj : (j:ℕ) < k
      · have : (i:ℕ) < k := lt_of_le_of_lt hij hj
        simp [hj, this]
      · simp only [hj, if_false]
        split_ifs <;> norm_num
    have hmono : Monovary c q := by
      intro i j hij
      apply hc
      by_contra hcon
      push_neg at hcon
      exact absurd (hanti hcon.le) (not_le.mpr hij)
    let L : (Fin N → ℝ) → ℝ := fun x => ∑ j, c j * x (Fin.rev j)
    have hL : IsLinearMap ℝ L := by
      constructor
      · intro x y; simp [L, mul_add, Finset.sum_add_distrib]
      · intro r x; simp [L, Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
    have hsub : permutohull q e ⊆ {x | L x ≤ ∑ j, c j * q j} := by
      apply convexHull_min
      · rintro _ ⟨τ, rfl⟩
        show L _ ≤ _
        rw [hgen τ]
        have := hmono.sum_smul_comp_perm_le_sum_smul (σ := τ * Fin.revPerm)
        simpa [L, smul_eq_mul] using this
      · exact convex_halfSpace_le hL _
    have := hsub hw
    simp only [Set.mem_setOf_eq, L, c] at this
    simpa [ite_mul] using this
  intro i
  set t : Fin N → ℝ := fun j => q j + q (Fin.rev j) - 2 / (N:ℝ) with ht
  have hT : ∀ k : ℕ, 0 ≤ ∑ j : Fin N, if (j:ℕ) < k then t j else 0 := by
    intro k
    have e : (∑ j : Fin N, if (j:ℕ) < k then t j else 0) =
        (∑ j : Fin N, if (j:ℕ) < k then q j else 0) -
        (∑ j : Fin N, if (j:ℕ) < k then (2 / (N:ℝ) - q (Fin.rev j)) else 0) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : (j:ℕ) < k
      · simp only [hj, if_true, ht]; ring
      · simp [hj]
    rw [e]; linarith [hk k]
  have hNr : (N:ℝ) ≠ 0 := by positivity
  have htot : ∑ j, t j = 0 := by
    simp only [ht]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have : ∑ j : Fin N, q (Fin.rev j) = ∑ j, q j := Equiv.sum_comp Fin.revPerm q
    rw [this, hsum]
    simp [Finset.sum_const, Finset.card_univ]
    field_simp
    norm_num
  have hT' : ∀ k ≤ N, (∑ j : Fin N, if k ≤ (j:ℕ) then t j else 0) =
      ∑ j : Fin N, if (j:ℕ) < N - k then t j else 0 := by
    intro k hkN
    rw [← Equiv.sum_comp Fin.revPerm (fun j : Fin N => if (j:ℕ) < N - k then t j else 0)]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hr : t (Fin.revPerm j) = t j := by
      simp only [ht, Fin.revPerm_apply, Fin.rev_rev]; ring
    have hjN := j.isLt
    simp only [Fin.revPerm_apply, Fin.val_rev]
    rw [show Fin.rev j = Fin.revPerm j from rfl, hr]
    have : (k ≤ (j:ℕ)) ↔ (N - ((j:ℕ) + 1) < N - k) := by omega
    simp only [this]
  have hzero : ∀ k ≤ N, (∑ j : Fin N, if (j:ℕ) < k then t j else 0) = 0 := by
    intro k hkN
    have h1 := hT k
    have h2 := hT (N - k)
    rw [← hT' k hkN] at h2
    have hs : (∑ j : Fin N, if (j:ℕ) < k then t j else 0) +
        (∑ j : Fin N, if k ≤ (j:ℕ) then t j else 0) = ∑ j, t j := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : (j:ℕ) < k
      · have : ¬ k ≤ (j:ℕ) := by omega
        simp [hj, this]
      · have : k ≤ (j:ℕ) := by omega
        simp [hj, this]
    linarith
  have hiN := i.isLt
  have z1 := hzero ((i:ℕ) + 1) (by omega)
  have z0 := hzero (i:ℕ) (by omega)
  have : t i = (∑ j : Fin N, if (j:ℕ) < (i:ℕ) + 1 then t j else 0) -
      (∑ j : Fin N, if (j:ℕ) < (i:ℕ) then t j else 0) := by
    rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      have : (j:ℕ) ≠ i := fun h => hji (Fin.ext h)
      by_cases h1 : (j:ℕ) < (i:ℕ)
      · have : (j:ℕ) < (i:ℕ) + 1 := by omega
        simp [h1, this]
      · have : ¬ (j:ℕ) < (i:ℕ) + 1 := by omega
        simp [h1, this]
    · simp
  rw [z1, z0] at this
  simp only [ht] at this
  linarith

lemma prop41_core {N : ℕ} (hN : 0 < N) (q : Fin N → ℝ)
    (hq : q ∈ restrictedSimplex N) :
    (∀ (n : ℕ) (a : Fin N → Fin n → ℝ),
      CentrallySymmetric (permutohull q a) (sampleMean a)) ↔
    ∃ σ : Equiv.Perm (Fin N), q = fun i => 2 / (N : ℝ) - q (σ i) := by
  constructor
  · intro h
    have hr := rev_of_symm hN q hq (h N _)
    refine ⟨Fin.revPerm, ?_⟩
    funext i
    have := hr i
    simp only [Fin.revPerm_apply]
    linarith
  · rintro ⟨σ, hσ⟩ n a
    exact symm_of_perm q σ hσ a

lemma rev_of_perm {N : ℕ} (hN : 0 < N) (q : Fin N → ℝ) (hq : q ∈ restrictedSimplex N)
    (σ : Equiv.Perm (Fin N)) (hσ : q = fun i => 2 / (N : ℝ) - q (σ i)) :
    ∀ i, q i + q (Fin.rev i) = 2 / (N:ℝ) :=
  rev_of_symm hN q hq (symm_of_perm q σ hσ _)

lemma sum_telescope (f : ℕ → ℝ) (c n : ℕ) (hcn : c ≤ n) :
    ∑ j ∈ Finset.range n, (if c ≤ j then f j - f (j+1) else 0) = f c - f n := by
  induction n, hcn using Nat.le_induction with
  | base =>
    rw [Finset.sum_eq_zero]
    · ring
    · intro j hj
      have := Finset.mem_range.mp hj
      simp [not_le.mpr this]
  | succ n hn ih =>
    rw [Finset.sum_range_succ, ih]
    simp [hn]

lemma sum_telescope' (f : ℕ → ℝ) (c n : ℕ) (hcn : n ≤ c) :
    ∑ j ∈ Finset.range n, (if c ≤ j then f j - f (j+1) else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  have := Finset.mem_range.mp hj
  simp [not_le.mpr (lt_of_lt_of_le this hcn)]

lemma qbar_formula {N : ℕ} (hN : 0 < N) (j : Fin (Nhat N)) (i : Fin N) :
    qbar j i = 1 / (N:ℝ) + (if (i:ℕ) < (j:ℕ) then 1 / (N:ℝ) else 0)
      - (if N ≤ (i:ℕ) + (j:ℕ) then 1 / (N:ℝ) else 0) := by
  have hj := j.isLt
  have hi := i.isLt
  simp only [Nhat] at hj
  unfold qbar
  split_ifs <;> first | omega | ring

lemma symRestricted_core {N : ℕ} (hN : 0 < N)
    (q : Fin N → ℝ) (hq : q ∈ symRestrictedSimplex N) :
    ∃ lam : Fin (Nhat N) → ℝ,
      (∀ j, 0 ≤ lam j) ∧
      ∑ j, lam j = 1 ∧
      q = ∑ j, lam j • qbar j := by
  obtain ⟨hq1, σ, hσ⟩ := hq
  have h0 := rev_of_perm hN q hq1 σ hσ
  obtain ⟨⟨hnn, hsum⟩, hanti⟩ := hq1
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  set M := N / 2 with hM
  -- r and g
  let g : ℕ → ℝ := fun i => if hi : i < M then (N:ℝ) * q ⟨i, by omega⟩ - 1 else 0
  have hhalf : ∀ i : Fin N, (i:ℕ) < M → 1 / (N:ℝ) ≤ q i := by
    intro i hi
    have hle : i ≤ Fin.rev i := by
      rw [Fin.le_def, Fin.val_rev]; omega
    have h1 := hanti hle
    have h2 := h0 i
    have : 1 / (N:ℝ) = (2 / (N:ℝ)) / 2 := by ring
    linarith
  have hg_nn : ∀ i, 0 ≤ g i := by
    intro i
    simp only [g]
    split_ifs with hi
    · have := hhalf ⟨i, by omega⟩ hi
      have h3 : 1 ≤ (N:ℝ) * q ⟨i, by omega⟩ := by
        calc (1:ℝ) = (N:ℝ) * (1 / (N:ℝ)) := by field_simp
          _ ≤ _ := by exact mul_le_mul_of_nonneg_left this hNr.le
      linarith
    · exact le_refl _
  have hg_anti : ∀ i, g (i+1) ≤ g i := by
    intro i
    by_cases hi : i + 1 < M
    · simp only [g, dif_pos hi, dif_pos (show i < M by omega)]
      have := hanti (show (⟨i, by omega⟩ : Fin N) ≤ ⟨i+1, by omega⟩ from Fin.mk_le_mk.mpr (by omega))
      have := mul_le_mul_of_nonneg_left this hNr.le
      linarith
    · have : g (i+1) = 0 := by simp only [g]; rw [dif_neg hi]
      rw [this]; exact hg_nn i
  have hgM : ∀ i, M ≤ i → g i = 0 := by
    intro i hi; simp only [g]; rw [dif_neg (by omega)]
  have hg0 : g 0 ≤ 1 := by
    simp only [g]
    split_ifs with hi
    · have h2 := h0 ⟨0, by omega⟩
      have h3 := hnn (Fin.rev ⟨0, by omega⟩)
      have : (N:ℝ) * q ⟨0, by omega⟩ ≤ 2 := by
        have : q ⟨0, by omega⟩ ≤ 2 / (N:ℝ) := by linarith
        calc (N:ℝ) * q ⟨0, by omega⟩ ≤ (N:ℝ) * (2 / (N:ℝ)) := mul_le_mul_of_nonneg_left this hNr.le
          _ = 2 := by field_simp
      linarith
    · norm_num
  let hh : ℕ → ℝ := fun k => if k = 0 then 1 else g (k - 1)
  have hh_succ : ∀ k, hh (k+1) = g k := by intro k; simp [hh]
  have hh_anti : ∀ k, hh (k+1) ≤ hh k := by
    intro k
    cases k with
    | zero => simpa [hh] using hg0
    | succ k => rw [hh_succ, hh_succ]; exact hg_anti k
  let lam0 : ℕ → ℝ := fun k => hh k - hh (k+1)
  refine ⟨fun j => lam0 j, fun j => sub_nonneg.mpr (hh_anti j), ?_, ?_⟩
  · rw [Fin.sum_univ_eq_sum_range lam0 (Nhat N)]
    simp only [lam0]
    rw [Finset.sum_range_sub' hh]
    have : hh (Nhat N) = 0 := by
      rw [show Nhat N = M + 1 from rfl, hh_succ]; exact hgM M le_rfl
    rw [this]; simp [hh]
  · have key1 : ∀ c, 1 ≤ c → ∑ j ∈ Finset.range (M+1), (if c ≤ j then lam0 j else 0) = g (c - 1) := by
      intro c hc
      by_cases hcM : c ≤ M + 1
      · have := sum_telescope hh c (M+1) hcM
        simp only [lam0]
        rw [this, hh_succ M, hgM M le_rfl]
        obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
        rw [hh_succ]; simp
      · rw [show (∑ j ∈ Finset.range (M+1), (if c ≤ j then lam0 j else 0)) = 0 from
          sum_telescope' hh c (M+1) (by omega)]
        rw [hgM _ (by omega)]
    have hsumlam : ∑ j ∈ Finset.range (M+1), lam0 j = 1 := by
      rw [Finset.sum_range_sub' hh, hh_succ M, hgM M le_rfl]; simp [hh]
    funext i
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    have hexp : ∀ j : Fin (Nhat N), lam0 j * qbar j i =
        lam0 j * (1 / (N:ℝ)) + (if (i:ℕ) + 1 ≤ (j:ℕ) then lam0 j * (1 / (N:ℝ)) else 0)
        - (if N - (i:ℕ) ≤ (j:ℕ) then lam0 j * (1 / (N:ℝ)) else 0) := by
      intro j
      rw [qbar_formula hN j i, mul_sub, mul_add]
      have hi := i.isLt
      have e1 : ((i:ℕ) < (j:ℕ)) ↔ ((i:ℕ) + 1 ≤ (j:ℕ)) := by omega
      have e2 : (N ≤ (i:ℕ) + (j:ℕ)) ↔ (N - (i:ℕ) ≤ (j:ℕ)) := by omega
      simp only [e1, e2, mul_ite, mul_zero]
    simp only [hexp]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have conv : ∀ F : ℕ → ℝ, ∑ j : Fin (Nhat N), F j = ∑ j ∈ Finset.range (M+1), F j :=
      fun F => Fin.sum_univ_eq_sum_range F (M+1)
    rw [conv (fun j => lam0 j * (1 / (N:ℝ))), conv (fun j => if (i:ℕ) + 1 ≤ j then lam0 j * (1 / (N:ℝ)) else 0),
      conv (fun j => if N - (i:ℕ) ≤ j then lam0 j * (1 / (N:ℝ)) else 0)]
    have hi := i.isLt
    have A : ∑ j ∈ Finset.range (M+1), lam0 j * (1 / (N:ℝ)) = 1 / (N:ℝ) := by
      rw [← Finset.sum_mul, hsumlam]; ring
    have B : ∑ j ∈ Finset.range (M+1), (if (i:ℕ) + 1 ≤ j then lam0 j * (1 / (N:ℝ)) else 0)
        = g i / N := by
      have : ∀ j, (if (i:ℕ) + 1 ≤ j then lam0 j * (1 / (N:ℝ)) else 0)
          = (if (i:ℕ) + 1 ≤ j then lam0 j else 0) * (1 / (N:ℝ)) := by
        intro j; split_ifs <;> simp
      simp only [this]
      rw [← Finset.sum_mul, key1 ((i:ℕ)+1) (by omega)]
      simp; ring
    have C : ∑ j ∈ Finset.range (M+1), (if N - (i:ℕ) ≤ j then lam0 j * (1 / (N:ℝ)) else 0)
        = g (N - (i:ℕ) - 1) / N := by
      have : ∀ j, (if N - (i:ℕ) ≤ j then lam0 j * (1 / (N:ℝ)) else 0)
          = (if N - (i:ℕ) ≤ j then lam0 j else 0) * (1 / (N:ℝ)) := by
        intro j; split_ifs <;> simp
      simp only [this]
      rw [← Finset.sum_mul, key1 (N - (i:ℕ)) (by omega)]
      ring
    rw [A, B, C]
    have hq2 := h0 i
    have hq3 : (q i + q (Fin.rev i)) * N = 2 := by rw [hq2]; field_simp
    have hrv : ((Fin.rev i : Fin N) : ℕ) = N - (i:ℕ) - 1 := by rw [Fin.val_rev]; omega
    by_cases hiM : (i:ℕ) < M
    · have h2 : M ≤ N - (i:ℕ) - 1 := by omega
      rw [hgM _ h2]
      simp only [g, dif_pos hiM]
      field_simp
      ring
    · by_cases hrM : N - (i:ℕ) - 1 < M
      · rw [hgM _ (by omega)]
        simp only [g, dif_pos hrM]
        have e : (⟨N - (i:ℕ) - 1, by omega⟩ : Fin N) = Fin.rev i := Fin.ext (by rw [hrv])
        rw [e]
        field_simp
        nlinarith [hq3]
      · have hieq : Fin.rev i = i := Fin.ext (by rw [hrv]; omega)
        rw [hieq] at hq2 hq3
        rw [hgM _ (by omega), hgM _ (by omega)]
        field_simp
        nlinarith [hq3]

end RiskUncSets.Symmetric

open RiskUncSets.Symmetric


theorem solution {N : ℕ} (hN : 0 < N)
    (q : Fin N → ℝ) (hq : q ∈ symRestrictedSimplex N) :
    ∃ lam : Fin (Nhat N) → ℝ,
      (∀ j, 0 ≤ lam j) ∧
      ∑ j, lam j = 1 ∧
      q = ∑ j, lam j • qbar j := by
  exact symRestricted_core hN q hq
