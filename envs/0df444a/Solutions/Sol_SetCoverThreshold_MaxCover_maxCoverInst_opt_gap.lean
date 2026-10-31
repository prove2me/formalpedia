-- Prove2me | solution 1 for SetCoverThreshold.MaxCover.maxCoverInst_opt_gap
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T19:42:51.719407+00:00
-- url     : https://prove2.me/submissions/91316d38-e5f4-4af6-aed5-b9da4a60b2b1

import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_MaxCover_Formula
import Definitions.Def_SetCoverThreshold_MaxCover_ProofSystem
import Definitions.Def_SetCoverThreshold_MaxCover_Instance
import Definitions.Def_SetCoverThreshold_MaxCover_Reduction
import Definitions.Def_SetCoverThreshold_MaxCover_Theorem53
import Theorems.Thm_SetCoverThreshold_MaxCover_gap_claim

set_option autoImplicit false
set_option linter.unusedVariables false

open CookPvsNP SetCoverThreshold.MaxCover Classical

private lemma coverOf_maxCoverInst_eq (φ : Formula5) {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool)
    (T : Finset (Fin (maxCoverInst φ code).sets.length)) :
    let eIdx := (Fintype.equivFin (SetIdx φ code)).symm
    let ePt := Fintype.equivFin (RandString φ ℓ × ((Fin ℓ → Bool) → Fin k))
    let C : Finset (SetIdx φ code) :=
      T.image (fun idx => eIdx (idx.cast List.length_ofFn))
    C.card ≤ T.card ∧
      (coverOf (maxCoverInst φ code) T).card = (coveredMaxCover φ code C).card := by
  intro eIdx ePt C
  refine ⟨Finset.card_image_le, ?_⟩
  have hget : ∀ i : Fin (maxCoverInst φ code).sets.length,
      (maxCoverInst φ code).sets.get i =
        (reductionSet φ code (cubeSystem k (Fin ℓ → Bool)) (eIdx (i.cast List.length_ofFn))).map
          ePt.toEmbedding := by
    intro i
    exact List.get_ofFn _ i
  have hcov : coverOf (maxCoverInst φ code) T = (coveredMaxCover φ code C).map ePt.toEmbedding := by
    ext x
    simp only [coverOf, coveredMaxCover, C, Finset.mem_biUnion, Finset.mem_image,
      exists_exists_and_eq_and, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨i, hiT, hx⟩
      rw [hget i, Finset.mem_map] at hx
      rcases hx with ⟨p, hp, rfl⟩
      exact ⟨p, ⟨i, hiT, hp⟩, rfl⟩
    · rintro ⟨p, ⟨i, hiT, hp⟩, rfl⟩
      refine ⟨i, hiT, ?_⟩
      rw [hget i, Finset.mem_map]
      exact ⟨p, hp, rfl⟩
  rw [hcov, Finset.card_map]

private lemma exists_T_of_C (φ : Formula5) {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool)
    (C : Finset (SetIdx φ code)) :
    ∃ T : Finset (Fin (maxCoverInst φ code).sets.length),
      T.card = C.card ∧
      (coverOf (maxCoverInst φ code) T).card = (coveredMaxCover φ code C).card := by
  let eIdx := Fintype.equivFin (SetIdx φ code)
  let ePt := Fintype.equivFin (RandString φ ℓ × ((Fin ℓ → Bool) → Fin k))
  let emb : SetIdx φ code ↪ Fin (maxCoverInst φ code).sets.length :=
    eIdx.toEmbedding.trans ⟨Fin.cast List.length_ofFn.symm, Fin.cast_injective _⟩
  refine ⟨C.map emb, Finset.card_map _, ?_⟩
  have hget : ∀ s : SetIdx φ code,
      (maxCoverInst φ code).sets.get (Fin.cast List.length_ofFn.symm (eIdx s)) =
        (reductionSet φ code (cubeSystem k (Fin ℓ → Bool)) s).map ePt.toEmbedding := by
    intro s
    simp [maxCoverInst, eIdx, ePt]
  have hcov : coverOf (maxCoverInst φ code) (C.map emb) =
      (coveredMaxCover φ code C).map ePt.toEmbedding := by
    ext x
    simp only [coverOf, coveredMaxCover, Finset.mem_biUnion, Finset.mem_map,
      Function.Embedding.trans_apply, Equiv.toEmbedding_apply, Function.Embedding.coeFn_mk,
      exists_exists_and_eq_and, emb]
    constructor
    · rintro ⟨s, hsC, hx⟩
      rw [hget s, Finset.mem_map] at hx
      rcases hx with ⟨p, hp, rfl⟩
      exact ⟨p, ⟨s, hsC, hp⟩, rfl⟩
    · rintro ⟨p, ⟨s, hsC, hp⟩, rfl⟩
      refine ⟨s, hsC, ?_⟩
      rw [hget s, Finset.mem_map]
      exact ⟨p, hp, rfl⟩
  rw [hcov, Finset.card_map]

theorem solution (hRaz : RazRepetition) :
    (∀ (k ℓ : ℕ) (code : Fin k → Fin ℓ → Bool) (φ : Formula5), φ.toCNF.Satisfiable →
        opt (maxCoverInst φ code) = (maxCoverInst φ code).n) ∧
      (∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ ε' : ℝ, 0 < ε' → ∃ ℓ₀ : ℕ, ∀ ℓ : ℕ, ℓ₀ ≤ ℓ →
        ∀ code : Fin k → Fin ℓ → Bool, IsCode code →
          ∀ φ : Formula5, AtMostFracSat (1 - ε') φ.toCNF →
            (opt (maxCoverInst φ code) : ℝ) ≤
              (1 - Real.exp (-1) + ε) * ((maxCoverInst φ code).n : ℝ)) := by
  obtain ⟨hYes, hNo⟩ := gap_claim hRaz
  constructor
  · intro k ℓ code φ hSat
    obtain ⟨C, hC_card, hC_cov⟩ := hYes k ℓ code φ hSat
    obtain ⟨T, hT_card, hT_cov⟩ := exists_T_of_C φ code C
    apply le_antisymm
    · unfold opt
      apply Finset.sup_le
      intro T' _
      exact Finset.card_le_univ (coverOf (maxCoverInst φ code) T') |>.trans (by simp)
    · have hmem : T ∈ (Finset.univ : Finset (Finset (Fin (maxCoverInst φ code).sets.length))).filter
          (fun T' => T'.card ≤ (maxCoverInst φ code).k) := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hT_card.le.trans hC_card⟩
      have hle : (coverOf (maxCoverInst φ code) T).card ≤ opt (maxCoverInst φ code) :=
        Finset.le_sup (f := fun T' => (coverOf (maxCoverInst φ code) T').card) hmem
      rw [hT_cov, hC_cov, Finset.card_univ] at hle
      exact hle
  · intro ε hε
    obtain ⟨k₀, hk₀⟩ := hNo ε hε
    refine ⟨k₀, fun k hk ε' hε' => ?_⟩
    obtain ⟨ℓ₀, hℓ₀⟩ := hk₀ k hk ε' hε'
    refine ⟨ℓ₀, fun ℓ hℓ code hcode φ hFrac => ?_⟩
    have hsup : opt (maxCoverInst φ code) ≤
        ⌊(1 - Real.exp (-1) + ε) * ((maxCoverInst φ code).n : ℝ)⌋₊ := by
      unfold opt
      apply Finset.sup_le
      intro T hT
      rw [Finset.mem_filter] at hT
      obtain ⟨hC_le, hcov_eq⟩ := coverOf_maxCoverInst_eq φ code T
      have hbound := hℓ₀ ℓ hℓ code hcode φ hFrac _ (hC_le.trans hT.2)
      rw [← hcov_eq] at hbound
      exact Nat.le_floor hbound
    have hnonneg : 0 ≤ (1 - Real.exp (-1) + ε) * ((maxCoverInst φ code).n : ℝ) := by
      have hexp : Real.exp (-1) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        linarith
      positivity
    exact (Nat.cast_le.mpr hsup).trans (Nat.floor_le hnonneg)
