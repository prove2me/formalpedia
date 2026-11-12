-- Prove2me | solution 1 for SampleRemoval.monotone_rounding
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T23:34:47.259179+00:00
-- url     : https://prove2.me/submissions/e33f327b-5211-4d92-96f8-5403a8867f1a

import Mathlib
import Definitions.Def_SampleRemoval_ind
import Definitions.Def_SampleRemoval_feasible
import Definitions.Def_SampleRemoval_sInt
import Definitions.Def_SampleRemoval_sFrac
import Definitions.Def_SampleRemoval_GeneralPosition
import Definitions.Def_SampleRemoval_IsTarget
import Theorems.Thm_SampleRemoval_lemma_3_2
import Theorems.Thm_SampleRemoval_sFrac_attained
import Theorems.Thm_SampleRemoval_rounding_step

section
set_option autoImplicit false

open Matrix

namespace SampleRemoval.Dev.MonoRound

lemma sum_ind {n : ℕ} (S : Finset (Fin n)) : ∑ i, ind S i = S.card := by
  simp [ind, Finset.sum_ite_mem]

lemma sFrac_le {n d : ℕ} (x : Fin n → Fin d → ℝ) (y : Fin n → ℝ) (e : Fin d → ℝ) (θ : ℝ)
    (w : Fin n → ℝ) (hw : w ∈ feasible x y e θ) :
    sFrac x y e θ ≤ (n : ℝ) - ∑ i, w i := by
  refine csInf_le ⟨0, ?_⟩ ⟨w, hw, rfl⟩
  rintro _ ⟨v, hv, rfl⟩
  have : ∑ i, v i ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => (hv.1 i).2
  simp at this
  linarith

lemma round_core {n d : ℕ} (x : Fin n → Fin d → ℝ) (y : Fin n → ℝ) (e : Fin d → ℝ) (θ : ℝ)
    (hGP : GeneralPosition x) (hd : 1 ≤ d) (w : Fin n → ℝ) (hw : w ∈ feasible x y e θ)
    (hm : 2 * (d : ℝ) ≤ ∑ i, w i) :
    ∃ S : Finset (Fin n), ind S ∈ feasible x y e θ ∧
      (n : ℝ) - S.card < n - ∑ i, w i + d := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨w', hw', hmass, -, hJ⟩ := SampleRemoval.lemma_3_2 x y e θ hGP w hw
    (by linarith)
  set J := Finset.univ.filter (fun i => 0 < w' i ∧ w' i < 1) with hJdef
  set I := Finset.univ.filter (fun i => w' i = 1) with hIdef
  have hI01 := hw'.1
  -- pointwise bound
  have hpt : ∀ i, w' i ≤ (if i ∈ I then (1 : ℝ) else 0) + (if i ∈ J then w' i else 0) := by
    intro i
    have h := hI01 i
    have hA : (0 : ℝ) ≤ (if i ∈ I then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    have hB : (0 : ℝ) ≤ (if i ∈ J then w' i else 0) := by
      split_ifs
      · exact h.1
      · exact le_rfl
    rcases eq_or_lt_of_le h.1 with h0 | h0
    · linarith [h0.symm]
    · rcases eq_or_lt_of_le h.2 with h1 | h1
      · have : i ∈ I := by simp [hIdef, h1]
        simp only [this, if_true]; linarith
      · have : i ∈ J := by simp [hJdef, h0, h1]
        simp only [this, if_true]; linarith
  have hsum : ∑ i, w' i ≤ (I.card : ℝ) + ∑ i ∈ J, w' i := by
    calc ∑ i, w' i ≤ ∑ i, ((if i ∈ I then (1 : ℝ) else 0) + (if i ∈ J then w' i else 0)) :=
          Finset.sum_le_sum fun i _ => hpt i
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem]
        simp
  have hJd : ∑ i ∈ J, w' i < d := by
    by_cases hne : J.Nonempty
    · calc ∑ i ∈ J, w' i < ∑ _i ∈ J, (1 : ℝ) :=
            Finset.sum_lt_sum_of_nonempty hne fun i hi => ((Finset.mem_filter.mp hi).2).2
        _ = J.card := by simp
        _ ≤ d := by exact_mod_cast hJ
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp; linarith
  have hJd' : ∑ i ∈ J, w' i ≤ d := by
    by_cases hne : J.Nonempty
    · linarith
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp
  have hIcard : (d : ℝ) ≤ I.card := by linarith
  have hIcard' : d ≤ I.card := by exact_mod_cast hIcard
  obtain ⟨S, hIS, -, hSW⟩ := SampleRemoval.rounding_step x y e θ hGP w' hw' hIcard'
  refine ⟨S, hSW, ?_⟩
  have : (I.card : ℝ) ≤ S.card := by exact_mod_cast Finset.card_le_card hIS
  linarith

end SampleRemoval.Dev.MonoRound

namespace SampleRemoval

open Matrix

theorem chk_monotone_rounding {n d : ℕ} (x : Fin n → Fin d → ℝ) (y : Fin n → ℝ) (e : Fin d → ℝ)
    (θ : ℝ) (hGP : GeneralPosition x) (hT : IsTarget x y e θ) :
    ((feasible x y e θ).Nonempty → (d : ℝ) - 1 < n - sFrac x y e θ →
        ∃ w ∈ feasible x y e θ, (n : ℝ) - ∑ i, w i = sFrac x y e θ) ∧
      ((∃ w ∈ feasible x y e θ, 2 * (d : ℝ) ≤ ∑ i, w i) →
        (∃ w ∈ feasible x y e θ, (n : ℝ) - ∑ i, w i = sFrac x y e θ) ∧
        (∃ S : Finset (Fin n), ind S ∈ feasible x y e θ) ∧
        sFrac x y e θ ≤ (sInt x y e θ : ℝ) ∧
        (sInt x y e θ : ℝ) < sFrac x y e θ + d ∧
        ⌈sFrac x y e θ⌉ ≤ (sInt x y e θ : ℤ) ∧
        (sInt x y e θ : ℤ) ≤ ⌈sFrac x y e θ⌉ + d - 1 ∧
        ∀ w ∈ feasible x y e θ, 2 * (d : ℝ) ≤ ∑ i, w i →
          ∃ S : Finset (Fin n), ind S ∈ feasible x y e θ ∧
            (n : ℝ) - S.card < n - ∑ i, w i + d) := by
  refine ⟨fun hne h => SampleRemoval.sFrac_attained x y e θ hGP hne h, ?_⟩
  rintro ⟨w₀, hw₀, hm₀⟩
  have hne : (feasible x y e θ).Nonempty := ⟨w₀, hw₀⟩
  have hd : 1 ≤ d := by
    by_contra hd
    have hd0 : d = 0 := by omega
    subst hd0
    have h1 := hw₀.2.2
    have h2 := hT
    simp [IsTarget, dotProduct] at h1 h2
    linarith
  have hs₀ := Dev.MonoRound.sFrac_le x y e θ w₀ hw₀
  have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hatt := SampleRemoval.sFrac_attained x y e θ hGP hne (by linarith)
  obtain ⟨ws, hws, hwsm⟩ := hatt
  have hcore := fun w (hw : w ∈ feasible x y e θ) (hm : 2 * (d : ℝ) ≤ ∑ i, w i) =>
    Dev.MonoRound.round_core x y e θ hGP hd w hw hm
  obtain ⟨S₁, hS₁, hS₁lt⟩ := hcore ws hws (by linarith)
  have hmem : sInt x y e θ ∈ {k : ℕ | ∃ S : Finset (Fin n), ind S ∈ feasible x y e θ ∧
      k = n - S.card} := Nat.sInf_mem ⟨n - S₁.card, S₁, hS₁, rfl⟩
  obtain ⟨S₀, hS₀, hS₀eq⟩ := hmem
  have hcard : S₀.card ≤ n := by simpa using Finset.card_le_univ S₀
  have hsInt₀ : (sInt x y e θ : ℝ) = n - S₀.card := by
    rw [hS₀eq]; push_cast [Nat.cast_sub hcard]; ring
  have hle : sFrac x y e θ ≤ (sInt x y e θ : ℝ) := by
    rw [hsInt₀]
    have := Dev.MonoRound.sFrac_le x y e θ _ hS₀
    rwa [Dev.MonoRound.sum_ind] at this
  have hlt : (sInt x y e θ : ℝ) < sFrac x y e θ + d := by
    have hle1 : sInt x y e θ ≤ n - S₁.card := Nat.sInf_le ⟨S₁, hS₁, rfl⟩
    have hc1 : S₁.card ≤ n := by simpa using Finset.card_le_univ S₁
    have : (sInt x y e θ : ℝ) ≤ n - S₁.card := by
      have := (Nat.cast_le (α := ℝ)).mpr hle1
      rwa [Nat.cast_sub hc1] at this
    linarith
  refine ⟨⟨ws, hws, hwsm⟩, ⟨S₁, hS₁⟩, hle, hlt, ?_, ?_, fun w hw hm => hcore w hw hm⟩
  · exact Int.ceil_le.mpr (by exact_mod_cast hle)
  · have h1 : (sInt x y e θ : ℝ) < ((⌈sFrac x y e θ⌉ + d : ℤ) : ℝ) := by
      push_cast
      have := Int.le_ceil (sFrac x y e θ)
      linarith
    have h2 : (sInt x y e θ : ℤ) < ⌈sFrac x y e θ⌉ + d := by exact_mod_cast h1
    omega

end SampleRemoval
end

theorem solution : type_of% @SampleRemoval.chk_monotone_rounding := @SampleRemoval.chk_monotone_rounding
