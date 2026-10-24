-- Prove2me | solution 1 for StrictCompatLB.MeanField.lemma_H_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T14:44:13.911972+00:00
-- url     : https://prove2.me/submissions/c85198e3-9e1f-4897-a6d4-c63b7e2b6dbb

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Model

open Filter Topology MeasureTheory Finset
open scoped ENNReal

namespace StrictCompatLB.MeanField.H2

open StrictCompatLB.MeanField

section kernel
variable (lam : ℝ) (d : ℕ) (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)

lemma kexp_formula (V : (Fin N → ℕ) → ℝ) (z : Fin N → ℕ) :
    kexp (jsqdKernel lam d M G N) V z =
      lam / (lam + 1) * (1 / (M N : ℝ)) *
        ∑ w : Fin (M N), ∑ v : Fin N, jsqdRoute M G N d w z v * V (arrive z v) +
      1 / (lam + 1) * (1 / (N : ℝ)) * ∑ v : Fin N, V (depart z v) := by
  set A := lam / (lam + 1) * (1 / (M N : ℝ))
  set Bc := 1 / (lam + 1) * (1 / (N : ℝ))
  have hfun : (fun z' => jsqdKernel lam d M G N z z' * V z') = fun z' =>
      (∑ w : Fin (M N), ∑ v : Fin N, A * jsqdRoute M G N d w z v *
        (if z' = arrive z v then V (arrive z v) else 0)) +
      ∑ v : Fin N, Bc * (if z' = depart z v then V (depart z v) else 0) := by
    funext z'
    simp only [jsqdKernel, lbKernel]
    rw [add_mul]
    simp only [Finset.mul_sum, Finset.sum_mul]
    congr 1
    · apply Finset.sum_congr rfl; intro w _
      apply Finset.sum_congr rfl; intro v _
      split_ifs with h
      · subst h; ring
      · ring
    · apply Finset.sum_congr rfl; intro v _
      split_ifs with h
      · subst h; ring
      · ring
  have hs : HasSum (fun z' => jsqdKernel lam d M G N z z' * V z')
      ((∑ w : Fin (M N), ∑ v : Fin N, A * jsqdRoute M G N d w z v * V (arrive z v)) +
        ∑ v : Fin N, Bc * V (depart z v)) := by
    rw [hfun]
    exact (hasSum_sum (fun w _ => hasSum_sum (fun v _ =>
      (hasSum_ite_eq (arrive z v) (V (arrive z v))).mul_left (A * jsqdRoute M G N d w z v)))).add
      (hasSum_sum (fun v _ => (hasSum_ite_eq (depart z v) (V (depart z v))).mul_left Bc))
  unfold kexp
  rw [hs.tsum_eq, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl; intro w _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro v _
    ring

lemma jsqdRoute_nonneg (w : Fin (M N)) (z : Fin N → ℕ) (v : Fin N) :
    0 ≤ jsqdRoute M G N d w z v := by
  unfold jsqdRoute
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_nonneg
  intro U _
  split_ifs
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · exact le_refl _

/-- Per sample set: joining a shortest queue of `U` gives at most the `γ`-average of `f`. -/
lemma argmin_le (z : Fin N → ℕ) (U : Finset (Fin N)) (f : ℕ → ℝ) (hf0 : ∀ n, 0 ≤ f n)
    (hfm : Monotone f) (γ : Fin N → ℝ) (hγ0 : ∀ v, 0 ≤ γ v) (hγU : ∀ v, v ∉ U → γ v = 0)
    (hγ1 : U.Nonempty → ∑ v ∈ U, γ v = 1) :
    ∑ v : Fin N, (if v ∈ argminSet U z then ((argminSet U z).card : ℝ)⁻¹ else 0) * f (z v) ≤
      ∑ v : Fin N, γ v * f (z v) := by
  set R := ∑ v : Fin N, γ v * f (z v)
  have hR0 : 0 ≤ R := Finset.sum_nonneg (fun v _ => mul_nonneg (hγ0 v) (hf0 _))
  have hRU : R = ∑ v ∈ U, γ v * f (z v) := by
    symm
    apply Finset.sum_subset (subset_univ _)
    intro v _ hv; rw [hγU v hv, zero_mul]
  have hmin : ∀ v ∈ argminSet U z, f (z v) ≤ R := by
    intro v hv
    simp only [argminSet, mem_filter] at hv
    have hne : U.Nonempty := ⟨v, hv.1⟩
    rw [hRU]
    calc f (z v) = ∑ u ∈ U, γ u * f (z v) := by rw [← Finset.sum_mul, hγ1 hne, one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun u hu => mul_le_mul_of_nonneg_left (hfm (hv.2 u hu)) (hγ0 u))
  calc _ ≤ ∑ v : Fin N, (if v ∈ argminSet U z then ((argminSet U z).card : ℝ)⁻¹ else 0) * R := by
        apply Finset.sum_le_sum; intro v _
        split_ifs with h
        · exact mul_le_mul_of_nonneg_left (hmin v h) (inv_nonneg.mpr (Nat.cast_nonneg _))
        · simp
    _ = R * (((argminSet U z).card : ℝ) * ((argminSet U z).card : ℝ)⁻¹) := by
        rw [← Finset.sum_mul, Finset.sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]; ring
    _ ≤ R := by
        by_cases hc : ((argminSet U z).card : ℝ) = 0
        · rw [hc]; simp [hR0]
        · rw [mul_inv_cancel₀ hc, mul_one]

lemma route_sum_le_one (w : Fin (M N)) (z : Fin N → ℕ) : ∑ v : Fin N, jsqdRoute M G N d w z v ≤ 1 := by
  have h := fun U => argmin_le N z U (fun _ => 1) (fun _ => zero_le_one) (fun _ _ _ => le_refl _)
    (fun v => if v ∈ U then ((U.card : ℝ))⁻¹ else 0)
    (fun v => by split_ifs <;> simp)
    (fun v hv => by simp [hv])
    (fun hne => by
      rw [Finset.sum_ite_mem, Finset.inter_self, sum_const, nsmul_eq_mul]
      exact mul_inv_cancel₀ (by exact_mod_cast hne.card_pos.ne'))
  unfold jsqdRoute
  rw [← Finset.mul_sum, Finset.sum_comm]
  set n := (nbrW M G N w).card
  set s := (nbrW M G N w).powersetCard (min d n)
  have hsc : s.card = Nat.choose n (min d n) := by
    simp only [s, n, Finset.card_powersetCard]
  calc _ ≤ ((Nat.choose n (min d n) : ℕ) : ℝ)⁻¹ * ∑ U ∈ s, (1 : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
        apply Finset.sum_le_sum; intro U hU
        have := h U
        simp only [mul_one] at this
        calc _ ≤ ∑ v : Fin N, (if v ∈ U then ((U.card : ℝ))⁻¹ else 0) := this
          _ ≤ 1 := by
            rw [Finset.sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]
            by_cases hc : (U.card : ℝ) = 0
            · rw [hc]; simp
            · rw [mul_inv_cancel₀ hc]
    _ = ((Nat.choose n (min d n) : ℕ) : ℝ)⁻¹ * (Nat.choose n (min d n) : ℝ) := by
        rw [sum_const, nsmul_eq_mul, mul_one, hsc]
    _ ≤ 1 := by
        have : (0 : ℝ) < Nat.choose n (min d n) := by
          exact_mod_cast Nat.choose_pos (min_le_right _ _)
        rw [inv_mul_cancel₀ this.ne']

end kernel

/-! The Lyapunov function in closed form. -/

/-- `ψ_B(ℓ) = ∑_{k ≤ i < B} (ℓ + 1 − i)`. -/
def psi (k B ℓ : ℕ) : ℕ := ∑ i ∈ Ico k B, (ℓ + 1 - i)

lemma psi_succ (k B ℓ : ℕ) (h : ℓ + 2 ≤ B) : psi k B (ℓ + 1) = psi k B ℓ + (ℓ + 2 - k) := by
  unfold psi
  have : ∀ i ∈ Ico k B, ℓ + 1 + 1 - i = (ℓ + 1 - i) + (if i ≤ ℓ + 1 then 1 else 0) := by
    intro i _; split_ifs <;> omega
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.card_filter]
  congr 1
  have : (Ico k B).filter (fun i => i ≤ ℓ + 1) = Ico k (ℓ + 2) := by
    ext i; simp only [mem_filter, mem_Ico]; omega
  rw [this, Nat.card_Ico]

lemma Qcount_eq_zero {N : ℕ} (z : Fin N → ℕ) (i : ℕ) (hi : maxLen z < i) : Qcount z i = 0 := by
  unfold Qcount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro u _ h
  have : z u ≤ maxLen z := Finset.le_sup (f := z) (mem_univ u)
  omega

lemma le_maxLen {N : ℕ} (z : Fin N → ℕ) (u : Fin N) : z u ≤ maxLen z :=
  Finset.le_sup (f := z) (mem_univ u)

lemma lyap_eq {N : ℕ} (k : ℕ) (z : Fin N → ℕ) (B : ℕ) (hB : maxLen z < B) :
    lyap k z = ∑ u : Fin N, (psi k B (z u) : ℝ) := by
  have h1 : lyap k z = ∑ i ∈ Ico k B, ∑ j ∈ Ico i B, (Qcount z j : ℝ) := by
    unfold lyap
    have e : ∀ i ∈ Ico k (maxLen z + 1),
        ∑ j ∈ Ico i (maxLen z + 1), (Qcount z j : ℝ) = ∑ j ∈ Ico i B, (Qcount z j : ℝ) := by
      intro i _
      apply Finset.sum_subset
      · intro j hj; simp only [mem_Ico] at hj ⊢; omega
      · intro j hj hj'
        simp only [mem_Ico] at hj hj'
        rw [Qcount_eq_zero z j (by omega)]; simp
    rw [Finset.sum_congr rfl e]
    apply Finset.sum_subset
    · intro i hi; simp only [mem_Ico] at hi ⊢; omega
    · intro i hi hi'
      simp only [mem_Ico] at hi hi'
      apply Finset.sum_eq_zero
      intro j hj
      simp only [mem_Ico] at hj
      rw [Qcount_eq_zero z j (by omega)]; simp
  rw [h1]
  have h2 : ∑ i ∈ Ico k B, ∑ j ∈ Ico i B, Qcount z j = ∑ u : Fin N, psi k B (z u) := by
    unfold Qcount psi
    simp only [card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    rw [← Finset.card_filter]
    have hu := le_maxLen z u
    have : (Ico i B).filter (fun j => j ≤ z u) = Ico i (z u + 1) := by
      ext j; simp only [mem_filter, mem_Ico]; omega
    rw [this, Nat.card_Ico]
  exact_mod_cast h2

lemma maxLen_le_of {N : ℕ} (z z' : Fin N → ℕ) (h : ∀ u, z' u ≤ z u + 1) :
    maxLen z' ≤ maxLen z + 1 := by
  unfold maxLen
  apply Finset.sup_le
  intro u _
  have : z u ≤ univ.sup z := Finset.le_sup (f := z) (mem_univ u)
  have := h u
  omega

lemma sum_update {N : ℕ} (z : Fin N → ℕ) (v : Fin N) (c : ℕ) (g : ℕ → ℝ) :
    ∑ u : Fin N, g (Function.update z v c u) = ∑ u : Fin N, g (z u) - g (z v) + g c := by
  rw [← Finset.add_sum_erase _ _ (mem_univ v), ← Finset.add_sum_erase _ _ (mem_univ v)]
  have : ∑ x ∈ univ.erase v, g (Function.update z v c x) = ∑ x ∈ univ.erase v, g (z x) := by
    apply Finset.sum_congr rfl; intro x hx
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  rw [this, Function.update_self]; ring

lemma lyap_arrive {N : ℕ} (k : ℕ) (z : Fin N → ℕ) (v : Fin N) :
    lyap k (arrive z v) - lyap k z = ((z v + 2 - k : ℕ) : ℝ) := by
  set B := maxLen z + 2
  have hB1 : maxLen (arrive z v) < B := by
    have := maxLen_le_of z (arrive z v) (fun u => by
      unfold arrive; by_cases h : u = v
      · subst h; simp
      · rw [Function.update_of_ne h]; omega)
    omega
  rw [lyap_eq k _ B hB1, lyap_eq k z B (by omega)]
  unfold arrive
  rw [sum_update z v (z v + 1) (fun ℓ => (psi k B ℓ : ℝ))]
  have := psi_succ k B (z v) (by have := le_maxLen z v; omega)
  simp only [this]; push_cast; ring

lemma lyap_depart {N : ℕ} (k : ℕ) (hk : 1 ≤ k) (z : Fin N → ℕ) (v : Fin N) :
    lyap k (depart z v) - lyap k z = -((z v + 1 - k : ℕ) : ℝ) := by
  set B := maxLen z + 2
  have hB1 : maxLen (depart z v) < B := by
    have := maxLen_le_of z (depart z v) (fun u => by
      unfold depart; by_cases h : u = v
      · subst h; simp; omega
      · rw [Function.update_of_ne h]; omega)
    omega
  rw [lyap_eq k _ B hB1, lyap_eq k z B (by omega)]
  unfold depart
  rw [sum_update z v (z v - 1) (fun ℓ => (psi k B ℓ : ℝ))]
  rcases Nat.eq_zero_or_pos (z v) with h0 | hpos
  · rw [h0]; simp; omega
  · obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, z v = ℓ + 1 := ⟨z v - 1, by omega⟩
    rw [hℓ]
    have := psi_succ k B ℓ (by have := le_maxLen z v; omega)
    simp only [Nat.add_sub_cancel, this]
    push_cast
    have e : ℓ + 1 + 1 - k = ℓ + 2 - k := by omega
    rw [e]; ring

lemma sum_sub_k {N : ℕ} (k : ℕ) (z : Fin N → ℕ) :
    ∑ u : Fin N, (z u + 1 - k) = ∑ i ∈ Ico k (maxLen z + 1), Qcount z i := by
  unfold Qcount
  simp only [card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [← Finset.card_filter]
  have hu := le_maxLen z u
  have : (Ico k (maxLen z + 1)).filter (fun i => i ≤ z u) = Ico k (z u + 1) := by
    ext j; simp only [mem_filter, mem_Ico]; omega
  rw [this, Nat.card_Ico]

lemma sum_sub_k2 {N : ℕ} (k : ℕ) (hk : 1 ≤ k) (z : Fin N → ℕ) :
    ∑ u : Fin N, (z u + 2 - k) = Qcount z (k - 1) + ∑ u : Fin N, (z u + 1 - k) := by
  unfold Qcount
  rw [card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  split_ifs <;> omega

end StrictCompatLB.MeanField.H2

open StrictCompatLB.MeanField StrictCompatLB.MeanField.H2 in
theorem solution (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) (d : ℕ) (hd : 1 ≤ d)
    (M : ℕ → ℕ) (hM : ∀ N, 0 < M N) (G : (N : ℕ) → Finset (Fin N × Fin (M N)))
    (hconn : IsConnectedSeq M G) (hsub : IsSubcritical d M G) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ k : ℕ, 1 ≤ k → ∀ z : Fin N → ℕ,
      oneStepDrift (jsqdKernel lam d M G N) (lyap k) z ≤
        1 / (lam + 1) * ((1 + ε) * lam * occ z (k - 1) - (1 - (1 + ε) * lam) * tailSum k z) := by
  obtain ⟨γ, hγ0, hγU, hγ1, hγε⟩ := hsub
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := hγε ε hε
  refine ⟨max N₁ 1, le_max_right _ _, ?_⟩
  intro N hN k hk z
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hMpos : (0 : ℝ) < M N := by exact_mod_cast hM N
  have hl1 : 0 < lam + 1 := by linarith
  set A := lam / (lam + 1) * (1 / (M N : ℝ)) with hA
  set Bc := 1 / (lam + 1) * (1 / (N : ℝ)) with hBc
  have hA0 : 0 ≤ A := by positivity
  have hBc0 : 0 ≤ Bc := by positivity
  set r := jsqdRoute M G N d with hr
  -- the Lyapunov function is nonnegative
  have hV0 : 0 ≤ lyap k z := by
    unfold lyap
    exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
  -- step 1: drift in terms of increments
  have hdrift : oneStepDrift (jsqdKernel lam d M G N) (lyap k) z ≤
      A * ∑ w : Fin (M N), ∑ v : Fin N, r w z v * ((z v + 2 - k : ℕ) : ℝ) +
        Bc * ∑ v : Fin N, (-((z v + 1 - k : ℕ) : ℝ)) := by
    unfold oneStepDrift
    rw [kexp_formula]
    have e1 : ∀ w v, r w z v * lyap k (arrive z v) =
        r w z v * ((z v + 2 - k : ℕ) : ℝ) + r w z v * lyap k z := by
      intro w v; rw [← lyap_arrive k z v]; ring
    have e2 : ∀ v, lyap k (depart z v) = (-((z v + 1 - k : ℕ) : ℝ)) + lyap k z := by
      intro v; rw [← lyap_depart k hk z v]; ring
    simp only [← hr, e1, e2, Finset.sum_add_distrib]
    have hrs : ∑ w : Fin (M N), ∑ v : Fin N, r w z v * lyap k z ≤ (M N : ℝ) * lyap k z := by
      calc _ = ∑ w : Fin (M N), (∑ v : Fin N, r w z v) * lyap k z := by
            apply Finset.sum_congr rfl; intro w _; rw [Finset.sum_mul]
        _ ≤ ∑ w : Fin (M N), 1 * lyap k z := by
            apply Finset.sum_le_sum; intro w _
            exact mul_le_mul_of_nonneg_right (route_sum_le_one d M G N w z) hV0
        _ = _ := by simp
    have hsumc : ∑ v : Fin N, lyap k z = (N : ℝ) * lyap k z := by simp
    rw [hsumc]
    have hAM : A * (M N : ℝ) + Bc * (N : ℝ) = 1 := by
      rw [hA, hBc]; field_simp
    nlinarith [mul_le_mul_of_nonneg_left hrs hA0]
  -- step 2: subcriticality bound for the arrival term
  have hsubN := hN₁ N (le_trans (le_max_left _ _) hN)
  set f : ℕ → ℝ := fun ℓ => ((ℓ + 2 - k : ℕ) : ℝ) with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n => Nat.cast_nonneg _
  have hfm : Monotone f := by
    intro a b hab; simp only [hf]; exact_mod_cast (by omega : a + 2 - k ≤ b + 2 - k)
  have harr : ∑ w : Fin (M N), ∑ v : Fin N, r w z v * f (z v) ≤
      (1 + ε) * (M N : ℝ) / N * ∑ v : Fin N, f (z v) := by
    set C : Fin (M N) → ℝ := fun w =>
      ((Nat.choose (nbrW M G N w).card (min d (nbrW M G N w).card) : ℕ) : ℝ)⁻¹
    set S : Fin (M N) → Finset (Finset (Fin N)) := fun w =>
      (nbrW M G N w).powersetCard (min d (nbrW M G N w).card)
    have hC0 : ∀ w, 0 ≤ C w := fun w => inv_nonneg.mpr (Nat.cast_nonneg _)
    have step : ∀ w, ∑ v : Fin N, r w z v * f (z v) ≤
        ∑ v : Fin N, f (z v) * (C w * ∑ U ∈ S w, γ N w U v) := by
      intro w
      have e : ∑ v : Fin N, r w z v * f (z v) = C w * ∑ U ∈ S w, ∑ v : Fin N,
          (if v ∈ argminSet U z then ((argminSet U z).card : ℝ)⁻¹ else 0) * f (z v) := by
        simp only [hr, jsqdRoute, C, S]
        rw [Finset.mul_sum]
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro U _
        apply Finset.sum_congr rfl; intro v _
        ring
      rw [e]
      calc _ ≤ C w * ∑ U ∈ S w, ∑ v : Fin N, γ N w U v * f (z v) := by
            apply mul_le_mul_of_nonneg_left _ (hC0 w)
            apply Finset.sum_le_sum; intro U _
            exact argmin_le N z U f hf0 hfm (γ N w U) (hγ0 N w U) (hγU N w U) (hγ1 N w U)
        _ = _ := by
            simp only [Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro v _
            apply Finset.sum_congr rfl; intro U _
            ring
    calc _ ≤ ∑ w : Fin (M N), ∑ v : Fin N, f (z v) * (C w * ∑ U ∈ S w, γ N w U v) :=
          Finset.sum_le_sum (fun w _ => step w)
      _ = ∑ v : Fin N, f (z v) * ∑ w : Fin (M N), C w * ∑ U ∈ S w, γ N w U v := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro v _
          rw [Finset.mul_sum]
      _ ≤ ∑ v : Fin N, f (z v) * ((1 + ε) * (M N : ℝ) / N) := by
          apply Finset.sum_le_sum; intro v _
          apply mul_le_mul_of_nonneg_left _ (hf0 _)
          have h := hsubN v
          rw [div_mul_eq_mul_div, div_le_iff₀ hMpos] at h
          rw [le_div_iff₀ hNpos]
          linarith
      _ = _ := by rw [← Finset.sum_mul]; ring
  -- step 3: identities and assembly
  have hSg : (∑ v : Fin N, ((z v + 1 - k : ℕ) : ℝ)) = (N : ℝ) * tailSum k z := by
    have := sum_sub_k k z
    unfold tailSum occ
    rw [← Finset.sum_div, mul_div_cancel₀ _ hNpos.ne']
    exact_mod_cast this
  have hSf : (∑ v : Fin N, f (z v)) = (N : ℝ) * occ z (k - 1) + (N : ℝ) * tailSum k z := by
    have := sum_sub_k2 k hk z
    simp only [hf]
    rw [← hSg]
    unfold occ
    rw [mul_div_cancel₀ _ hNpos.ne']
    exact_mod_cast this
  have harr' := mul_le_mul_of_nonneg_left harr hA0
  simp only [hf] at harr'
  rw [Finset.sum_neg_distrib, hSg] at hdrift
  have hfin : A * ((1 + ε) * (M N : ℝ) / N * ∑ v : Fin N, f (z v)) + Bc * -((N : ℝ) * tailSum k z) =
      1 / (lam + 1) * ((1 + ε) * lam * occ z (k - 1) - (1 - (1 + ε) * lam) * tailSum k z) := by
    rw [hSf, hA, hBc]
    field_simp
    ring
  simp only [hf] at hfin
  linarith
