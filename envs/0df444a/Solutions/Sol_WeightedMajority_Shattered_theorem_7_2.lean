-- Prove2me | solution 1 for WeightedMajority.Shattered.theorem_7_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T18:54:25.411805+00:00
-- url     : https://prove2.me/submissions/2cd417de-4b28-40c0-95d3-46ccdedfe301

import Definitions.Def_UnderstandingML_Online
import Definitions.Def_WeightedMajority_Shattered_ShatteredByDomain



namespace WeightedMajority.Shattered

theorem pow2_core {ι : Type*} [DecidableEq ι] (e : ι → ℕ) :
    ∀ L : ℕ, ∀ s : Finset ι, (∀ i ∈ s, e i ≤ L) → (2:ℝ)^L ≤ ∑ i ∈ s, (2:ℝ)^(e i) →
      ∃ K ⊆ s, ∑ i ∈ K, (2:ℝ)^(e i) = 2^L := by
  intro L
  induction L with
  | zero =>
    intro s hs hsum
    have h0 : ∀ i ∈ s, e i = 0 := fun i hi => Nat.le_zero.mp (hs i hi)
    by_cases hne : s.Nonempty
    · obtain ⟨i, hi⟩ := hne
      refine ⟨{i}, by simpa using hi, ?_⟩
      simp [h0 i hi]
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      subst hne
      simp at hsum
      norm_num at hsum
  | succ L ih =>
    intro s hs hsum
    by_cases hex : ∃ i ∈ s, e i = L + 1
    · obtain ⟨i, hi, hei⟩ := hex
      refine ⟨{i}, by simpa using hi, ?_⟩
      simp [hei]
    · push_neg at hex
      have hs' : ∀ i ∈ s, e i ≤ L := fun i hi => by
        have := hs i hi; have := hex i hi; omega
      have h1 : (2:ℝ)^L ≤ ∑ i ∈ s, (2:ℝ)^(e i) := by
        have : (2:ℝ)^L ≤ 2^(L+1) := pow_le_pow_right₀ (by norm_num) (by omega)
        linarith
      obtain ⟨K1, hK1, hs1⟩ := ih s hs' h1
      have hsplit : ∑ i ∈ s \ K1, (2:ℝ)^(e i) = ∑ i ∈ s, (2:ℝ)^(e i) - 2^L := by
        rw [Finset.sum_sdiff_eq_sub hK1, hs1]
      have h2 : (2:ℝ)^L ≤ ∑ i ∈ s \ K1, (2:ℝ)^(e i) := by
        rw [hsplit]; rw [pow_succ] at hsum; linarith
      obtain ⟨K2, hK2, hs2⟩ := ih (s \ K1) (fun i hi => hs' i (Finset.sdiff_subset hi)) h2
      have hdisj : Disjoint K1 K2 := by
        rw [Finset.disjoint_left]
        intro i hi1 hi2
        have := hK2 hi2
        simp at this
        exact this.2 hi1
      refine ⟨K1 ∪ K2, Finset.union_subset hK1 (hK2.trans Finset.sdiff_subset), ?_⟩
      rw [Finset.sum_union hdisj, hs1, hs2, pow_succ]; ring

open UnderstandingML

theorem le_M {X : Type*} (A : OnlineAlg X Bool) (f : X → Bool) (hist : List (X × Bool))
    (hg : ∀ s (h : s < hist.length), A (hist.take s) (hist[s]).1 ≠ (hist[s]).2)
    (hc : ∀ e ∈ hist, f e.1 = e.2) :
    (hist.length : ℕ∞) ≤ mistakeBound A ({f} : Set (X → Bool)) := by
  unfold mistakeBound
  refine le_trans ?_ (le_iSup_of_le hist.length (le_iSup_of_le (fun s : Fin hist.length => (hist.get s).1)
    (le_iSup_of_le f (le_iSup_of_le (Set.mem_singleton f) le_rfl))))
  have hS : (fun t : Fin hist.length => ((hist.get t).1, f ((hist.get t).1))) = hist.get := by
    funext t
    exact Prod.ext rfl (hc _ (List.get_mem _ _))
  have : mistakes A (fun t : Fin hist.length => ((hist.get t).1, f ((hist.get t).1))) = hist.length := by
    unfold mistakes
    rw [Finset.filter_true_of_mem, Finset.card_univ, Fintype.card_fin]
    intro t _
    simp only [history]
    rw [hS, List.ofFn_get]
    have h3 := hc _ (List.get_mem hist t)
    rw [h3]
    exact hg t t.2
  rw [this]

theorem main_core {X : Type*} {n : ℕ} (φ : Fin n → X → Bool)
    (hφ : ShatteredByDomain φ) (A : OnlineAlg X Bool)
    (hfin : ∀ i, mistakeBound A ({φ i} : Set (X → Bool)) < ⊤) :
    (∑ i : Fin n, (2 : ℝ) ^ (-((mistakeBound A ({φ i} : Set (X → Bool))).toNat : ℤ))) < 2 := by
  classical
  set M : Fin n → ℕ := fun i => (mistakeBound A ({φ i} : Set (X → Bool))).toNat with hMdef
  have hle : ∀ i (hist : List (X × Bool)),
      (∀ s (h : s < hist.length), A (hist.take s) (hist[s]).1 ≠ (hist[s]).2) →
      (∀ e ∈ hist, φ i e.1 = e.2) → hist.length ≤ M i := by
    intro i hist hg hc
    have h1 := le_M A (φ i) hist hg hc
    have h2 := hfin i
    have : ((hist.length : ℕ) : ℕ∞) ≤ ((M i : ℕ) : ℕ∞) := by
      rw [hMdef]; simp only
      rw [ENat.coe_toNat h2.ne]; exact h1
    exact_mod_cast this
  set B : ℕ := Finset.univ.sup M with hB
  have hMB : ∀ i, M i ≤ B := fun i => Finset.le_sup (f := M) (Finset.mem_univ i)
  -- main claim
  have claim : ∀ d : ℕ, ∀ (hist : List (X × Bool)),
      (∀ s (h : s < hist.length), A (hist.take s) (hist[s]).1 ≠ (hist[s]).2) →
      B + 1 ≤ hist.length + d →
      ∀ K : Finset (Fin n), (∀ i ∈ K, ∀ e ∈ hist, φ i e.1 = e.2) →
        ∑ i ∈ K, (2:ℝ)^(B + hist.length - M i) ≠ 2^(B+1) := by
    intro d
    induction d with
    | zero =>
      intro hist hg hlen K hK hsum
      have hpos : (0:ℝ) < 2^(B+1) := by positivity
      have hne : K.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        rintro rfl
        simp at hsum; linarith
      obtain ⟨i, hi⟩ := hne
      have := hle i hist hg (hK i hi)
      have := hMB i
      omega
    | succ d ih =>
      intro hist hg hlen K hK hsum
      have hbd : ∀ i ∈ K, B + hist.length - M i ≤ B := fun i hi => by
        have := hle i hist hg (hK i hi)
        omega
      obtain ⟨S, hSK, hS⟩ := pow2_core (fun i => B + hist.length - M i) B K hbd
        (by rw [hsum]; exact pow_le_pow_right₀ (by norm_num) (by omega))
      have hSc : ∑ i ∈ K \ S, (2:ℝ)^(B + hist.length - M i) = 2^B := by
        rw [Finset.sum_sdiff_eq_sub hSK, hS, hsum, pow_succ]; ring
      obtain ⟨x, hx⟩ := hφ (fun i => decide (i ∈ S))
      set p := A hist x with hp
      -- survivors: those with φ i x = !p
      set K' : Finset (Fin n) := K.filter (fun i => φ i x = !p) with hK'
      have hKs : ∑ i ∈ K', (2:ℝ)^(B + hist.length - M i) = 2^B := by
        have hK'eq : K' = if p = false then S else K \ S := by
          rw [hK']
          ext i
          rw [Finset.mem_filter]
          have hxi := hx i
          by_cases hpf : p = false
          · rw [if_pos hpf, hpf, hxi]
            constructor
            · rintro ⟨_, h⟩; simpa using h
            · intro hi; exact ⟨hSK hi, by simpa using hi⟩
          · have hpt : p = true := by simpa using hpf
            rw [if_neg hpf, hpt, hxi, Finset.mem_sdiff]
            constructor
            · rintro ⟨hi, h⟩; exact ⟨hi, by simpa using h⟩
            · rintro ⟨hi, h⟩; exact ⟨hi, by simpa using h⟩
        rw [hK'eq]
        split_ifs
        · exact hS
        · exact hSc
      have hg' : ∀ s (h : s < (hist ++ [(x, !p)]).length),
          A ((hist ++ [(x, !p)]).take s) ((hist ++ [(x, !p)])[s]).1 ≠ ((hist ++ [(x, !p)])[s]).2 := by
        intro s hs
        simp only [List.length_append, List.length_singleton] at hs
        by_cases hlt : s < hist.length
        · rw [List.take_append_of_le_length hlt.le, List.getElem_append_left hlt]
          exact hg s hlt
        · have hs' : s = hist.length := by omega
          subst hs'
          rw [List.take_append_of_le_length le_rfl, List.take_length, List.getElem_append_right le_rfl]
          simp [hp]
      refine ih (hist ++ [(x, !p)]) hg' (by simp; omega) K' ?_ ?_
      · intro i hi e he
        rw [hK', Finset.mem_filter] at hi
        rcases List.mem_append.mp he with h | h
        · exact hK i hi.1 e h
        · simp at h; subst h; exact hi.2
      · have : ∑ i ∈ K', (2:ℝ)^(B + (hist ++ [(x, !p)]).length - M i)
            = 2 * ∑ i ∈ K', (2:ℝ)^(B + hist.length - M i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          have hi' := (Finset.mem_filter.mp hi).1
          have := hle i hist hg (hK i hi')
          have hM := hMB i
          simp only [List.length_append, List.length_singleton]
          rw [show B + (hist.length + 1) - M i = (B + hist.length - M i) + 1 by omega, pow_succ]; ring
        rw [this, hKs, pow_succ]; ring
  by_contra hcon
  push_neg at hcon
  have hrw : ∀ i, (2 : ℝ) ^ (-((mistakeBound A ({φ i} : Set (X → Bool))).toNat : ℤ)) = (2:ℝ)^(-(M i : ℤ)) := fun i => rfl
  simp only [hrw] at hcon
  have hpow : ∀ i, (2:ℝ)^(B - M i) = 2^B * (2:ℝ)^(-(M i : ℤ)) := fun i => by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (by norm_num)]
    congr 1
    have := hMB i
    omega
  obtain ⟨K, -, hK⟩ := pow2_core (fun i => B - M i) (B + 1) Finset.univ
    (fun i _ => by omega)
    (by
      simp only [hpow, ← Finset.mul_sum]
      rw [pow_succ]; nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) B])
  exact claim (B + 1) [] (by intro s hs; simp at hs) (by simp) K (by simp)
    (by simpa using hK)

end WeightedMajority.Shattered

open WeightedMajority.Shattered


theorem solution {X : Type*} {n : ℕ} (φ : Fin n → X → Bool)
    (hφ : ShatteredByDomain φ) (A : UnderstandingML.OnlineAlg X Bool)
    (hfin : ∀ i, UnderstandingML.mistakeBound A ({φ i} : Set (X → Bool)) < ⊤) :
    (∑ i : Fin n, (2 : ℝ) ^ (-((UnderstandingML.mistakeBound A
      ({φ i} : Set (X → Bool))).toNat : ℤ))) < 2 := by
  exact main_core φ hφ A hfin
