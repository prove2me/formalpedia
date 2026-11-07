-- Prove2me | solution 1 for SymBoolPCSP.CFixing.lemma_4_12
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T19:10:49.529734+00:00
-- url     : https://prove2.me/submissions/1c2a91f8-7c9b-4213-9ba4-f7393b06e13b

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic
import Theorems.Thm_SymBoolPCSP_CFixing_lemma_4_7
import Theorems.Thm_SymBoolPCSP_CFixing_lemma_4_10
import Theorems.Thm_SymBoolPCSP_CFixing_corollary_4_11
import Theorems.Thm_SymBoolPCSP_CFixing_eq_false_of_vanish_increasing
import Theorems.Thm_SymBoolPCSP_CFixing_card_lt_of_subsets_true
import Theorems.Thm_SymBoolPCSP_CFixing_subset_true_of_relax_maj
import Theorems.Thm_SymBoolPCSP_CFixing_card_lt_of_minimal
import Theorems.Thm_SymBoolPCSP_CFixing_cfixing_of_small_witness

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

/-- Lemma 4.12 (p. 24): if `Γ` is finite, symmetric, folded and idempotent and
`Par_{L₁}, AT_{L₂}, Maj_{L₃} ∉ Pol(Γ)` for some odd `L₁, L₂, L₃`, then there is `C(Γ) ∈ ℕ` such
that every polymorphism of `Γ` is `C(Γ)`-fixing. -/
theorem lemma_4_12 {τ : Type} [Fintype τ] {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPF : IsPromiseFamily 𝔸 𝔹) (hsym : IsSymmetricFamily 𝔸 𝔹) (hfold : IsFoldedFamily 𝔸 𝔹)
    (hidem : IsIdempotentFamily 𝔸 𝔹) (L₁ L₂ L₃ : ℕ) (hL₁ : Odd L₁) (hL₂ : Odd L₂)
    (hL₃ : Odd L₃) (hPar : ¬ IsPolymorphism 𝔸 𝔹 (Par L₁)) (hAT : ¬ IsPolymorphism 𝔸 𝔹 (AT L₂))
    (hMaj : ¬ IsPolymorphism 𝔸 𝔹 (Maj L₃)) :
    ∃ C : ℕ, ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsPolymorphism 𝔸 𝔹 f → IsCFixing C f := by
  classical
  obtain ⟨c, hc⟩ := lemma_4_10 𝔸 𝔹 hPF hsym hfold hidem L₁ L₂ hL₁ hL₂ hPar hAT
  have hcor := corollary_4_11 𝔸 𝔹 hPF hsym hfold hidem L₁ L₂ hL₁ hL₂ hPar hAT c hc
  obtain ⟨k, hk⟩ := lemma_4_7 𝔸 𝔹 hPF hsym hfold hidem L₃ hL₃ hMaj
  rcases hk with ⟨_, ⟨m, rfl⟩, hrel⟩ | ⟨_, b, hb2, hbk, hrel⟩
  · -- Case 1: `k = 2m + 1`, relaxation `(Ham_k({m+1}), Ham_k({0, …, 2m}))`
    refine ⟨m * (c + 1), fun L f hf => ?_⟩
    have h0 : f (fun _ => false) = false := (hidem L f hf).1
    have hpol := hrel L f hf
    rw [show (2 * m + 1 + 1) / 2 = m + 1 by omega, show 2 * m + 1 - 1 = 2 * m by omega] at hpol
    refine ⟨Finset.univ.filter (fun j : Fin L => ∃ Y : Finset (Fin L), j ∉ Y ∧
      f (indicator Y) = false ∧ f (indicator (insert j Y)) = true),
      (card_lt_of_subsets_true f c m _ (fun Z hZ hZc =>
      subset_true_of_relax_maj f (hfold L f hf) hpol Z hZc
        (fun j hj => (Finset.mem_filter.mp (hZ hj)).2)) (hcor L f hf)).le, fun x hx => ?_⟩
    rw [eq_false_of_vanish_increasing f h0 x hx, h0]
  · -- Case 2: relaxation `(Ham_k({1, k}), Ham_k({0, …, k} \ {b}))`, `2 ≤ b ≤ k - 1`
    obtain ⟨r, rfl⟩ : ∃ r, k = b + r := ⟨k - b, by omega⟩
    refine ⟨(c + 1) * b, fun L f hf => ?_⟩
    refine cfixing_of_small_witness f (hidem L f hf).1 b c (fun X hX => ?_) (hcor L f hf)
    obtain ⟨T, hT, hTmin⟩ := Finset.exists_min_image
      (X.powerset.filter (fun T => f (indicator T) = true)) Finset.card
      ⟨X, Finset.mem_filter.mpr ⟨Finset.mem_powerset_self X, hX⟩⟩
    rw [Finset.mem_filter, Finset.mem_powerset] at hT
    refine ⟨T, hT.1, hT.2, (card_lt_of_minimal f (hfold L f hf) (by omega) (hrel L f hf) T hT.2
      (fun T' hT' => ?_)).le⟩
    by_contra hne
    have := hTmin T' (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hT'.subset.trans hT.1),
      by simpa using hne⟩)
    have := Finset.card_lt_card hT'
    omega

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem solution {τ : Type} [Fintype τ] {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPF : IsPromiseFamily 𝔸 𝔹) (hsym : IsSymmetricFamily 𝔸 𝔹) (hfold : IsFoldedFamily 𝔸 𝔹)
    (hidem : IsIdempotentFamily 𝔸 𝔹) (L₁ L₂ L₃ : ℕ) (hL₁ : Odd L₁) (hL₂ : Odd L₂)
    (hL₃ : Odd L₃) (hPar : ¬ IsPolymorphism 𝔸 𝔹 (Par L₁)) (hAT : ¬ IsPolymorphism 𝔸 𝔹 (AT L₂))
    (hMaj : ¬ IsPolymorphism 𝔸 𝔹 (Maj L₃)) :
    ∃ C : ℕ, ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsPolymorphism 𝔸 𝔹 f → IsCFixing C f :=
  SymBoolPCSP.CFixing.lemma_4_12 𝔸 𝔹 hPF hsym hfold hidem L₁ L₂ L₃ hL₁ hL₂ hL₃ hPar hAT hMaj
