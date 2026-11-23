-- Prove2me | solution 1 for SubmodMDP.Policies.lemma_11
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:23:32.384968+00:00
-- url     : https://prove2.me/submissions/bbbeff7f-4099-4860-af88-fb8a672f10b2

import Definitions.Def_SubmodMDP_Policies_GraphMDP

open SubmodMDP.Policies

namespace Lemma11Aux

lemma alg4K_subset_range (d r ℓ : ℕ) (hd : 2 ≤ d) (hℓ : ℓ < d ^ r) :
    alg4K d ℓ ⊆ (Finset.range r).image (fun j => (ℓ / d ^ j) * d ^ j) := by
  intro k hk
  simp only [alg4K, Finset.mem_erase, Finset.mem_image, Finset.mem_range] at hk ⊢
  rcases hk with ⟨hk0, j, _, rfl⟩
  refine ⟨j, ?_, rfl⟩
  by_contra hj
  have hj' : r ≤ j := Nat.le_of_not_lt hj
  have hpow : d ^ r ≤ d ^ j := Nat.pow_le_pow_right (by omega) hj'
  have hdiv : ℓ / d ^ j = 0 := Nat.div_eq_of_lt (lt_of_lt_of_le hℓ hpow)
  simp [hdiv] at hk0

lemma card_alg4K_le (d r ℓ : ℕ) (hd : 2 ≤ d) (hℓ : ℓ < d ^ r) :
    (alg4K d ℓ).card ≤ r := by
  calc
    (alg4K d ℓ).card ≤ ((Finset.range r).image (fun j => (ℓ / d ^ j) * d ^ j)).card :=
      Finset.card_le_card (alg4K_subset_range d r ℓ hd hℓ)
    _ ≤ (Finset.range r).card := Finset.card_image_le
    _ = r := Finset.card_range r

lemma self_mem_alg4K (d ℓ : ℕ) (hℓ : 1 ≤ ℓ) : ℓ ∈ alg4K d ℓ := by
  simp only [alg4K, Finset.mem_erase, Finset.mem_image, Finset.mem_range]
  refine ⟨by omega, 0, by omega, by simp⟩

lemma mem_alg4K_pos_le (d ℓ i : ℕ) (hi : i ∈ alg4K d ℓ) : 1 ≤ i ∧ i ≤ ℓ := by
  simp only [alg4K, Finset.mem_erase, Finset.mem_image, Finset.mem_range] at hi
  rcases hi with ⟨hi0, j, _, rfl⟩
  exact ⟨Nat.pos_of_ne_zero hi0, Nat.div_mul_le_self ℓ (d ^ j)⟩

lemma card_alg4I_le {N : ℕ} (d r : ℕ) (traj : List (Fin N)) (hd : 2 ≤ d)
    (hℓ : traj.length < d ^ r) : (alg4I d traj).card ≤ r := by
  calc
    (alg4I d traj).card
      ≤ ∑ i ∈ alg4K d traj.length, (traj[i - 1]?).toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ alg4K d traj.length, 1 := by
      refine Finset.sum_le_sum fun i _ => ?_
      cases traj[i - 1]? <;> simp
    _ = (alg4K d traj.length).card := by simp
    _ ≤ r := card_alg4K_le d r traj.length hd hℓ

end Lemma11Aux

set_option linter.unusedVariables false in
theorem solution (M : GMDP) (hM : M.WF) (d r : ℕ) (hd : 2 ≤ d) (hr : 1 ≤ r)
    (hH : M.G.H = d ^ r) (x : Finset (Fin M.G.N) → ℝ) (hx : InQ M.G r x) (h7 : Sat7 M r x)
    (traj : List (Fin M.G.N)) (hlen1 : 1 ≤ traj.length) (hlen2 : traj.length ≤ M.G.H - 1)
    (hlayer : ∀ (i : ℕ) (h : i < traj.length), M.G.layer traj[i] = i + 1)
    (vℓ : Fin M.G.N) (hlast : traj.getLast? = some vℓ) (hc : M.chance vℓ = true) :
    alg4 M d x traj = none ∨ ∃ q, alg4 M d x traj = some q ∧ ∀ u, q u = M.p vℓ u := by
  have _ := hx
  by_cases h0 : x (alg4I d traj) = 0
  · left
    simp [alg4, h0]
  · right
    refine ⟨fun u => if M.G.layer u = traj.length + 1 then
        x (insert u (alg4I d traj)) / x (alg4I d traj) else 0, ?_, ?_⟩
    · simp [alg4, h0]
    · intro u
      have hHpos : 1 ≤ M.G.H := by
        rw [hH]
        exact Nat.one_le_pow r d (by omega)
      have hℓ_lt_H : traj.length < M.G.H := by omega
      have hℓ_lt : traj.length < d ^ r := by simpa [hH] using hℓ_lt_H
      have hne : traj ≠ [] := List.ne_nil_of_length_pos (by omega)
      have hget_last : traj[traj.length - 1]? = some vℓ := by
        rw [← List.getLast?_eq_getElem?, hlast]
      have hidx_lt : traj.length - 1 < traj.length := by omega
      have hvℓ_eq : traj[traj.length - 1] = vℓ := by
        rw [List.getElem?_eq_getElem hidx_lt] at hget_last
        exact Option.some.inj hget_last
      have hvℓ_layer : M.G.layer vℓ = traj.length := by
        rw [← hvℓ_eq, hlayer (traj.length - 1) hidx_lt]
        omega
      have hvℓ_mem : vℓ ∈ alg4I d traj := by
        simp only [alg4I, Finset.mem_biUnion, Option.mem_toFinset, Option.mem_def]
        exact ⟨traj.length, Lemma11Aux.self_mem_alg4K d traj.length hlen1, hget_last⟩
      have hI_layer : ∀ v ∈ alg4I d traj, M.G.layer v ≤ traj.length := by
        intro v hv
        simp only [alg4I, Finset.mem_biUnion, Option.mem_toFinset, Option.mem_def] at hv
        rcases hv with ⟨i, hiK, hvi⟩
        obtain ⟨hi1, hi2⟩ := Lemma11Aux.mem_alg4K_pos_le d traj.length i hiK
        have hi_lt : i - 1 < traj.length := by omega
        rw [List.getElem?_eq_getElem hi_lt] at hvi
        have hv_eq : traj[i - 1] = v := Option.some.inj hvi
        rw [← hv_eq, hlayer (i - 1) hi_lt]
        omega
      have hI_card : (alg4I d traj).card ≤ r :=
        Lemma11Aux.card_alg4I_le d r traj hd hℓ_lt
      by_cases hu : M.G.layer u = traj.length + 1
      · simp only [hu, ↓reduceIte]
        have hsat := h7 traj.length hlen1 hlen2 vℓ hc hvℓ_layer u hu
          (alg4I d traj) hvℓ_mem hI_layer hI_card
        rw [hsat, mul_div_cancel_left₀ _ h0]
      · simp only [hu, ↓reduceIte]
        symm
        by_contra hp0
        have harc : M.G.arc vℓ u = true := ((hM.2.2.2 vℓ hc).2.1 u).mp hp0
        have hulay : M.G.layer u = M.G.layer vℓ + 1 := hM.1.2 vℓ u harc
        rw [hvℓ_layer] at hulay
        exact hu hulay
