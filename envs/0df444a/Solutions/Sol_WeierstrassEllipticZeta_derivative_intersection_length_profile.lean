-- Prove2me | solution 1 for WeierstrassEllipticZeta.derivative_intersection_length_profile
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T01:19:25.198359+00:00
-- url     : https://prove2.me/submissions/7862ec6c-bb0b-4211-85f0-71a68b0a0294

import Theorems.Thm_WeierstrassEllipticZeta_finite_contact_jet_intersection_length

noncomputable section
open WeierstrassEllipticZeta

private lemma common_jet_prefix_iff (a : ℕ → ℂ) (t : ℕ)
    (hne : a t ≠ 0) (hbefore : ∀ j < t, a j = 0)
    (s k : ℕ) (hs : 0 < s) :
    (∀ i : Fin s, ∀ j < k, a (j + i.val) = 0) ↔ k ≤ t + 1 - s := by
  constructor
  · intro h
    by_contra hk
    let i : Fin s := ⟨min t (s - 1), by omega⟩
    have hj : t - i.val < k := by dsimp [i]; omega
    have hi : i.val ≤ t := Nat.min_le_left _ _
    have hz := h i (t - i.val) hj
    rw [Nat.sub_add_cancel hi] at hz
    exact hne hz
  · intro hk i j hj
    apply hbefore
    have hi := i.isLt
    omega

theorem solution
    (g₂ g₃ : ℂ) (c : Fin 2)
    (hcontact : ∀ (v : Fin 4 → ℂ) (n : ℕ) (p : MvPolynomial (Fin 4) ℂ),
      p ∈ extensionChartContactIdeal g₂ g₃ c v n ↔
        ∀ k < n, MvPolynomial.eval v ((extensionChartDerivation g₂ g₃ c)^[k] p) = 0)
    (V : Finset (Fin 4 → ℂ))
    (hV : Function.Injective (fun v : V => v.val 0)) (n : V → ℕ)
    (r : Fin 3 → Polynomial ℂ)
    (hmem : ∀ p : MvPolynomial (Fin 4) ℂ,
      p ∈ (⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)) ↔
        (∏ v : V, (Polynomial.X - Polynomial.C (v.val 0)) ^ n v) ∣
          MvPolynomial.aeval (Fin.cons Polynomial.X r) p)
    (p : MvPolynomial (Fin 4) ℂ) (B : ℕ)
    (hB : ∀ v : V, ∃ j < B,
      MvPolynomial.eval v.val ((extensionChartDerivation g₂ g₃ c)^[j] p) ≠ 0) :
    ∃ t : V → ℕ,
      (∀ v : V, t v < B ∧
        MvPolynomial.eval v.val ((extensionChartDerivation g₂ g₃ c)^[t v] p) ≠ 0 ∧
        ∀ j < t v, MvPolynomial.eval v.val ((extensionChartDerivation g₂ g₃ c)^[j] p) = 0) ∧
      ∀ s : ℕ, 0 < s →
        let I := ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)
        let J := I ⊔ Ideal.span (Set.range (fun i : Fin s =>
          (extensionChartDerivation g₂ g₃ c)^[i.val] p))
        FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ∧
        Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) =
          ∑ v : V, min (n v) (t v + 1 - s) ∧
        (J = ⊤ ↔ ∀ v : V, n v = 0 ∨ t v < s) ∧
        (B ≤ s → J = ⊤) := by
  classical
  have hex (v : V) : ∃ j : ℕ,
      MvPolynomial.eval v.val ((extensionChartDerivation g₂ g₃ c)^[j] p) ≠ 0 := by
    obtain ⟨j, _, hj⟩ := hB v
    exact ⟨j, hj⟩
  let t : V → ℕ := fun v => Nat.find (hex v)
  have ht (v : V) : t v < B ∧
      MvPolynomial.eval v.val ((extensionChartDerivation g₂ g₃ c)^[t v] p) ≠ 0 ∧
      ∀ j < t v, MvPolynomial.eval v.val ((extensionChartDerivation g₂ g₃ c)^[j] p) = 0 := by
    refine ⟨?_, Nat.find_spec (hex v), ?_⟩
    · obtain ⟨j, hj, hne⟩ := hB v
      exact (Nat.find_min' (hex v) hne).trans_lt hj
    · intro j hj
      exact not_ne_iff.mp (Nat.find_min (hex v) hj)
  refine ⟨t, ht, ?_⟩
  intro s hs
  let I := ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)
  let J := I ⊔ Ideal.span (Set.range (fun i : Fin s =>
    (extensionChartDerivation g₂ g₃ c)^[i.val] p))
  obtain ⟨hfinite, e, he, hsum⟩ := finite_contact_jet_intersection_length
    g₂ g₃ c hcontact V hV n r hmem s (fun i : Fin s =>
      (extensionChartDerivation g₂ g₃ c)^[i.val] p)
  have heq (v : V) : e v = min (n v) (t v + 1 - s) := by
    have hchar (k : ℕ) (hk : k ≤ n v) : k ≤ e v ↔ k ≤ t v + 1 - s := by
      rw [(he v).2 k hk]
      simpa only [Function.iterate_add_apply] using
        common_jet_prefix_iff
          (fun j => MvPolynomial.eval v.val ((extensionChartDerivation g₂ g₃ c)^[j] p))
          (t v) (ht v).2.1 (ht v).2.2 s k hs
    exact le_antisymm (le_min (he v).1 ((hchar (e v) (he v).1).mp le_rfl))
      ((hchar _ (Nat.min_le_left _ _)).mpr (Nat.min_le_right _ _))
  have hrank : Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) =
      ∑ v : V, min (n v) (t v + 1 - s) := hsum.trans (Finset.sum_congr rfl fun v _ => heq v)
  have : FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) := hfinite
  have htop : J = ⊤ ↔ ∀ v : V, n v = 0 ∨ t v < s := by
    rw [← Ideal.Quotient.subsingleton_iff, ← Module.finrank_zero_iff (R := ℂ), hrank,
      Finset.sum_eq_zero_iff]
    simp only [Finset.mem_univ, forall_const]
    exact forall_congr' fun v => by omega
  exact ⟨hfinite, hrank, htop, fun hBs => htop.mpr fun v => Or.inr ((ht v).1.trans_le hBs)⟩

