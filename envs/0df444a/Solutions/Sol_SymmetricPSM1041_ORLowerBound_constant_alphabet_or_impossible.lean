-- Prove2me | solution 1 for SymmetricPSM1041.ORLowerBound.constant_alphabet_or_impossible
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T14:43:42.58482+00:00
-- url     : https://prove2.me/submissions/682bfec8-c600-4c3c-ab20-952430f2e5c4

import Mathlib
import Definitions.Def_SymmetricPSM1041_ORLowerBound_CostsRestrictions
import Theorems.Thm_SymmetricPSM1041_ORLowerBound_agreement_lemma_or

open SymmetricPSM1041.ORLowerBound

theorem solution (K : ℕ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ P : PSM (Fin n),
      (∀ i, (localAlphabet P i).card ≤ K) →
      ¬ (PerfectCorrect P orFunction ∧ SupportPrivate P orFunction) := by
  classical
  have message_mem (n : ℕ) (P : PSM (Fin n)) (i : Fin n)
      (b : Bool) (r : Fin P.seedCount) :
      (P.message i b r).val ∈ localAlphabet P i := by
    simp [localAlphabet]
  by_cases hK : K = 0
  · subst K
    refine ⟨1, le_rfl, ?_⟩
    intro n hn P hcard hprotocol
    let i : Fin n := ⟨0, by omega⟩
    let r : Fin P.seedCount := ⟨0, P.seedCount_pos⟩
    have hnon : (localAlphabet P i).Nonempty :=
      ⟨(P.message i false r).val, message_mem n P i false r⟩
    have := hcard i
    have := Finset.card_pos.mpr hnon
    omega
  obtain ⟨N, hNpos, hagree⟩ := agreement_lemma_or K
  refine ⟨N, hNpos, ?_⟩
  intro n hn P hcard ⟨hc, hp⟩
  let zero : Fin n → Bool := fun _ => false
  let one : Fin n → Bool := fun _ => true
  let char (S : Finset (Fin n)) : Fin n → Bool := fun i => decide (i ∈ S)
  let rstar : Fin P.seedCount := ⟨0, P.seedCount_pos⟩
  let v : Transcript P := transcript P one rstar
  have hnpos : 0 < n := lt_of_lt_of_le hNpos hn
  letI : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
  have hone : orFunction one = true := by
    simp [orFunction, one]
  have hchar (S : Finset (Fin n)) (hS : S.Nonempty) : orFunction (char S) = true := by
    simp [orFunction, char]
    exact ⟨hS.choose, by simp [hS.choose_spec]⟩
  have seed_exists (S : Finset (Fin n)) (hS : S.Nonempty) :
      ∃ r : Fin P.seedCount, transcript P (char S) r = v := by
    have hsupp := hp one (char S) (by rw [hone, hchar S hS])
    have hv : v ∈ transcriptSupport P one := ⟨rstar, rfl⟩
    rw [hsupp] at hv
    exact hv
  let seed (S : Finset (Fin n)) (hS : S.Nonempty) : Fin P.seedCount :=
    (seed_exists S hS).choose
  have seed_spec (S : Finset (Fin n)) (hS : S.Nonempty) :
      transcript P (char S) (seed S hS) = v :=
    (seed_exists S hS).choose_spec
  let label (i : Fin n) (w : Message) (hw : w ∈ localAlphabet P i) : Fin K :=
    Fin.castLE (hcard i) ((localAlphabet P i).equivFin ⟨w, hw⟩)
  have label_injective (i : Fin n) (w₁ w₂ : Message)
      (h₁ : w₁ ∈ localAlphabet P i) (h₂ : w₂ ∈ localAlphabet P i)
      (heq : label i w₁ h₁ = label i w₂ h₂) : w₁ = w₂ := by
    have hfin := Fin.castLE_injective (hcard i) heq
    have hsub := (localAlphabet P i).equivFin.injective hfin
    exact congrArg Subtype.val hsub
  let gamma (S : Finset (Fin n)) (hS : S.Nonempty) (i : Fin n) : Message :=
    (P.message i false (seed S hS)).val
  have gamma_mem (S : Finset (Fin n)) (hS : S.Nonempty) (i : Fin n) :
      gamma S hS i ∈ localAlphabet P i :=
    message_mem n P i false (seed S hS)
  let colors : (S : Finset (Fin n)) → S.Nonempty → (i : Fin n) → i ∈ S → Fin K :=
    fun S hS i _ => label i (gamma S hS i) (gamma_mem S hS i)
  obtain ⟨T, S, hT, hS, hTS, hcolors⟩ := hagree (Fin K) (by simp) n hn colors
  have hgamma (i : Fin n) (hi : i ∈ T) : gamma T hT i = gamma S hS i :=
    label_injective i _ _ _ _ (hcolors i hi)
  have hTsub : T ⊆ S := le_of_lt hTS
  have hdiff : (S \ T).Nonempty := by
    rw [Finset.sdiff_nonempty]
    exact fun hST => hTS.ne (Finset.Subset.antisymm hTsub hST)
  have htranscript : transcript P (char (S \ T)) (seed S hS) =
      transcript P zero (seed T hT) := by
    funext i
    apply Subtype.ext
    by_cases hiT : i ∈ T
    · have hiS : i ∈ S := hTsub hiT
      have hleft : char (S \ T) i = false := by simp [char, hiT]
      simp only [transcript, hleft, zero]
      exact hgamma i hiT |>.symm
    · have hviT : (P.message i false (seed T hT)).val = v i := by
        have hs := congrFun (seed_spec T hT) i
        have hs' := congrArg Subtype.val hs
        simpa [transcript, char, hiT] using hs'
      by_cases hiS : i ∈ S
      · have hleft : char (S \ T) i = true := by simp [char, hiS, hiT]
        have hviS := congrFun (seed_spec S hS) i
        have hviS' := congrArg Subtype.val hviS
        simpa [transcript, hleft, zero, hviT, char, hiS] using hviS'
      · have hleft : char (S \ T) i = false := by simp [char, hiS]
        have hviS := congrFun (seed_spec S hS) i
        have hviS' := congrArg Subtype.val hviS
        simpa [transcript, hleft, zero, hviT, char, hiS] using hviS'
  have hdecode := congrArg P.decode htranscript
  rw [hc (char (S \ T)) (seed S hS), hc zero (seed T hT)] at hdecode
  have hleft : orFunction (char (S \ T)) = true := hchar (S \ T) hdiff
  have hright : orFunction zero = false := by simp [orFunction, zero]
  rw [hleft, hright] at hdecode
  contradiction
