-- Prove2me | solution 1 for SetCoverThreshold.SetCover.scInst_cover_gap
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T19:52:35.058015+00:00
-- url     : https://prove2.me/submissions/c9ad1f21-1308-4a80-983f-400068304500

import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_SetCover_Formula
import Definitions.Def_SetCoverThreshold_SetCover_ProofSystem
import Definitions.Def_SetCoverThreshold_SetCover_PartitionSystem
import Definitions.Def_SetCoverThreshold_SetCover_Instance
import Definitions.Def_SetCoverThreshold_SetCover_Reduction
import Definitions.Def_SetCoverThreshold_SetCover_Theorem44
import Theorems.Thm_SetCoverThreshold_SetCover_lemma_4_1

set_option autoImplicit false
set_option linter.unusedVariables false

open SetCoverThreshold.SetCover Classical

private lemma scInst_coverable (φ : Formula5) {ℓ k m d : ℕ} (code : Fin k → Fin ℓ → Bool)
    (P : φ.RandomString ℓ → PartitionSystem m (2 ^ ℓ) k d) :
    (scInst φ code P).Coverable := by
  intro pt
  let ePt := Fintype.equivFin (φ.Point ℓ m)
  let eIdx := Fintype.equivFin (φ.SetIdx code)
  let rb : φ.Point ℓ m := ePt.symm pt
  let r : φ.RandomString ℓ := rb.1
  let b : Fin m := rb.2
  let zeroBits : Fin ℓ → Bool := fun _ => false
  let i : Fin k := (P r).part b (labelEquiv ℓ zeroBits)
  let q : φ.ProverQuestion code i := ⟨φ.question code r i, by
    intro j
    unfold Formula5.question
    by_cases h : code i j = true <;> simp [h]⟩
  let aBits : Fin ℓ → Fin 3 → Bool := fun j p =>
    if code i j then
      if p = (r j).2 then false else (φ.clause (r j).1 p).1
    else
      false
  have haCan : ∀ j : Fin ℓ, φ.CoordCanonical (q.1 j) (aBits j) := by
    intro j
    change φ.CoordCanonical (φ.question code r i j) (aBits j)
    unfold Formula5.question
    by_cases h : code i j = true
    · simp only [h, ↓reduceIte, Formula5.CoordCanonical, Formula5.ClauseSatBy]
      let p₀ : Fin 3 := (r j).2
      let p₁ : Fin 3 := ⟨(p₀.1 + 1) % 3, Nat.mod_lt _ (by decide)⟩
      have hpne : p₁ ≠ p₀ := by
        rcases p₀ with ⟨v, hv⟩
        intro heq
        have hval := congrArg Fin.val heq
        dsimp [p₁] at hval
        omega
      refine ⟨p₁, ?_⟩
      simp [aBits, h, hpne, p₀]
    · simp [h, Formula5.CoordCanonical, aBits]
  let x : φ.SetIdx code := ⟨i, q, ⟨aBits, haCan⟩⟩
  have hind : φ.inducedAssignment code r i aBits = zeroBits := by
    ext j
    unfold Formula5.inducedAssignment
    by_cases h : code i j = true <;> simp [aBits, zeroBits, h]
  have hmem_sc : rb ∈ φ.scSet code P x := by
    rw [Formula5.scSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, rfl, ?_⟩
    change (P r).part b (labelEquiv ℓ (φ.inducedAssignment code r i aBits)) = i
    rw [hind]
  let idx : Fin (Fintype.card (φ.SetIdx code)) := eIdx x
  refine ⟨(scInst φ code P).sets.get (Fin.cast List.length_ofFn.symm idx), List.get_mem _ _, ?_⟩
  have hget : (scInst φ code P).sets.get (Fin.cast List.length_ofFn.symm idx) =
      (φ.scSet code P x).map ePt.toEmbedding := by
    simp [scInst, eIdx, ePt, idx]
  rw [hget, Finset.mem_map]
  exact ⟨rb, hmem_sc, ePt.apply_symm_apply pt⟩

private lemma exists_C_of_scCover (φ : Formula5) {ℓ k m d : ℕ} (code : Fin k → Fin ℓ → Bool)
    (P : φ.RandomString ℓ → PartitionSystem m (2 ^ ℓ) k d)
    (𝒞 : Finset (φ.SetIdx code)) (hcov : φ.IsSCCover code P 𝒞) :
    ∃ C : Finset (Fin (scInst φ code P).sets.length),
      (scInst φ code P).IsCover C ∧ C.card = 𝒞.card := by
  let eIdx := Fintype.equivFin (φ.SetIdx code)
  let ePt := Fintype.equivFin (φ.Point ℓ m)
  let emb : φ.SetIdx code ↪ Fin (scInst φ code P).sets.length :=
    eIdx.toEmbedding.trans ⟨Fin.cast List.length_ofFn.symm, Fin.cast_injective _⟩
  refine ⟨𝒞.map emb, ?_, Finset.card_map _⟩
  intro pt
  obtain ⟨x, hx𝒞, hxpt⟩ := hcov (ePt.symm pt)
  refine ⟨emb x, Finset.mem_map_of_mem emb hx𝒞, ?_⟩
  have hget : (scInst φ code P).sets.get (emb x) = (φ.scSet code P x).map ePt.toEmbedding := by
    simp [scInst, emb, eIdx, ePt]
  rw [hget, Finset.mem_map]
  exact ⟨ePt.symm pt, hxpt, ePt.apply_symm_apply pt⟩

private lemma exists_scCover_of_C (φ : Formula5) {ℓ k m d : ℕ} (code : Fin k → Fin ℓ → Bool)
    (P : φ.RandomString ℓ → PartitionSystem m (2 ^ ℓ) k d)
    (C : Finset (Fin (scInst φ code P).sets.length)) (hcov : (scInst φ code P).IsCover C) :
    ∃ 𝒞 : Finset (φ.SetIdx code),
      φ.IsSCCover code P 𝒞 ∧ 𝒞.card ≤ C.card := by
  let eIdx := (Fintype.equivFin (φ.SetIdx code)).symm
  let ePt := Fintype.equivFin (φ.Point ℓ m)
  let 𝒞 : Finset (φ.SetIdx code) := C.image (fun idx => eIdx (idx.cast List.length_ofFn))
  refine ⟨𝒞, ?_, Finset.card_image_le⟩
  intro rb
  obtain ⟨idx, hidxC, hpt⟩ := hcov (ePt rb)
  refine ⟨eIdx (idx.cast List.length_ofFn), Finset.mem_image_of_mem _ hidxC, ?_⟩
  have hget : (scInst φ code P).sets.get idx =
      (φ.scSet code P (eIdx (idx.cast List.length_ofFn))).map ePt.toEmbedding :=
    List.get_ofFn _ idx
  rw [hget, Finset.mem_map] at hpt
  rcases hpt with ⟨rb', hrb', heq⟩
  have hrb_eq : rb' = rb := ePt.injective heq
  rwa [← hrb_eq]

theorem solution (hRaz : RazRepetition) (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (φ : Formula5) (ℓ k m d : ℕ) (code : Fin k → Fin ℓ → Bool), IsCode ℓ k code →
        ∀ P : φ.RandomString ℓ → PartitionSystem m (2 ^ ℓ) k d,
          (scInst φ code P).Coverable ∧
          (φ.toCNF.Satisfiable →
              ∃ C : Finset (Fin (scInst φ code P).sets.length),
                (scInst φ code P).IsCover C ∧ C.card ≤ k * φ.numQuestions ℓ) ∧
            ∀ f : ℝ, 0 < f → (1 - f) * k * Real.log m ≤ d →
              (k : ℝ) ^ 2 * (2 : ℝ) ^ (-(c * ℓ)) < 2 * (2 * f) / (k * Real.log m) ^ 2 →
                AtMostFracSat (1 - ε) φ.toCNF →
                  ∀ C : Finset (Fin (scInst φ code P).sets.length),
                    (scInst φ code P).IsCover C →
                      (1 - 2 * f) * k * φ.numQuestions ℓ * Real.log m ≤ C.card := by
  obtain ⟨c, hc, h41⟩ := lemma_4_1 hRaz ε hε
  refine ⟨c, hc, fun φ ℓ k m d code hcode P => ?_⟩
  obtain ⟨hYes, hNo⟩ := h41 φ ℓ k m d code hcode P
  refine ⟨scInst_coverable φ code P, ?_, ?_⟩
  · intro hSat
    obtain ⟨𝒞, h𝒞_cov, h𝒞_card⟩ := hYes hSat
    obtain ⟨C, hC_cov, hC_card⟩ := exists_C_of_scCover φ code P 𝒞 h𝒞_cov
    exact ⟨C, hC_cov, hC_card.le.trans h𝒞_card⟩
  · intro f hf hd hprob hFrac C hC_cov
    obtain ⟨𝒞, h𝒞_cov, h𝒞_card⟩ := exists_scCover_of_C φ code P C hC_cov
    have hlow := hNo f hf hd hprob hFrac 𝒞 h𝒞_cov
    exact hlow.trans (by exact_mod_cast h𝒞_card)
