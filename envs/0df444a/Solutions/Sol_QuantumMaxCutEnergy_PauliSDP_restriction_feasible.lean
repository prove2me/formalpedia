-- Prove2me | solution 1 for QuantumMaxCutEnergy.PauliSDP.restriction_feasible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T16:54:47.74082+00:00
-- url     : https://prove2.me/submissions/f311f411-d824-4195-ad36-fc5305f47d46

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutPauliMomentRelaxationModel
import Mathlib
open scoped BigOperators

namespace QMCRestrict

open QuantumMaxCutEnergy.PauliSDP

/-- Extend a word on `s` sites to `n` sites by the identity label. -/
noncomputable def ext {n s : ℕ} (ι : Fin s → Fin n) (P : Word s) : Word n :=
  Function.extend ι P (fun _ => 0)

theorem ext_apply {n s : ℕ} {ι : Fin s → Fin n} (hι : Function.Injective ι)
    (P : Word s) (a : Fin s) : ext ι P (ι a) = P a :=
  hι.extend_apply _ _ a

theorem ext_apply' {n s : ℕ} {ι : Fin s → Fin n} (P : Word s) (i : Fin n)
    (hi : i ∉ Set.range ι) : ext ι P i = 0 := by
  unfold ext
  rw [Function.extend_apply' _ _ _ (by simpa [Set.mem_range] using hi)]

theorem ext_identity {n s : ℕ} {ι : Fin s → Fin n} (hι : Function.Injective ι) :
    ext ι (identityWord s) = identityWord n := by
  funext i
  by_cases hi : i ∈ Set.range ι
  · obtain ⟨a, rfl⟩ := hi
    rw [ext_apply hι]
    rfl
  · rw [ext_apply' _ _ hi]
    rfl

theorem support_ext_card {n s : ℕ} {ι : Fin s → Fin n} (P : Word s) :
    (support (ext ι P)).card ≤ s := by
  have hsub : support (ext ι P) ⊆ (Finset.univ : Finset (Fin s)).image ι := by
    intro i hi
    by_contra hni
    have hr : i ∉ Set.range ι := by
      rintro ⟨a, rfl⟩
      exact hni (Finset.mem_image_of_mem ι (Finset.mem_univ a))
    have h0 : ext ι P i = 0 := ext_apply' P i hr
    have : ext ι P i ≠ 0 := by
      simpa [support] using hi
    exact this h0
  calc (support (ext ι P)).card
      ≤ ((Finset.univ : Finset (Fin s)).image ι).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin s)).card := Finset.card_image_le
    _ = s := by simp

theorem wordProduct_ext {n s : ℕ} {ι : Fin s → Fin n} (hι : Function.Injective ι)
    (P Q : Word s) :
    wordProduct (ext ι P) (ext ι Q) = ext ι (wordProduct P Q) := by
  funext i
  by_cases hi : i ∈ Set.range ι
  · obtain ⟨a, rfl⟩ := hi
    simp only [wordProduct, ext_apply hι]
  · simp only [wordProduct]
    rw [ext_apply' _ _ hi, ext_apply' _ _ hi, ext_apply' _ _ hi]
    rfl

theorem wordPhase_ext {n s : ℕ} {ι : Fin s → Fin n} (hι : Function.Injective ι)
    (P Q : Word s) :
    wordPhase (ext ι P) (ext ι Q) = wordPhase P Q := by
  unfold wordPhase
  symm
  refine Fintype.prod_of_injective ι hι _ _ ?_ ?_
  · intro i hi
    rw [ext_apply' _ _ hi, ext_apply' _ _ hi]
    simp [localPhase]
  · intro a
    rw [ext_apply hι, ext_apply hι]

end QMCRestrict

theorem solution {n k s : ℕ}
    (L : QuantumMaxCutEnergy.PauliSDP.Word n → ℝ)
    (hL : QuantumMaxCutEnergy.PauliSDP.Feasible k L)
    (ι : Fin s → Fin n) (hι : Function.Injective ι) (hs : s ≤ k) :
    QuantumMaxCutEnergy.PauliSDP.Feasible s
      (fun P : QuantumMaxCutEnergy.PauliSDP.Word s =>
        L (Function.extend ι P (fun _ => 0))) := by
  obtain ⟨h1, hpsd⟩ := hL
  refine ⟨?_, ?_⟩
  · show L (QMCRestrict.ext ι (QuantumMaxCutEnergy.PauliSDP.identityWord s)) = 1
    rw [QMCRestrict.ext_identity hι]
    exact h1
  · let emb : QuantumMaxCutEnergy.PauliSDP.Index s s →
        QuantumMaxCutEnergy.PauliSDP.Index n k :=
      fun P => ⟨QMCRestrict.ext ι P.val,
        (QMCRestrict.support_ext_card P.val).trans hs⟩
    have hEq : QuantumMaxCutEnergy.PauliSDP.realGram s
        (fun P : QuantumMaxCutEnergy.PauliSDP.Word s =>
          L (Function.extend ι P (fun _ => 0))) =
        (QuantumMaxCutEnergy.PauliSDP.realGram k L).submatrix emb emb := by
      funext P Q
      show (QuantumMaxCutEnergy.PauliSDP.wordPhase P.val Q.val).re *
          L (QMCRestrict.ext ι (QuantumMaxCutEnergy.PauliSDP.wordProduct P.val Q.val)) =
        (QuantumMaxCutEnergy.PauliSDP.wordPhase (QMCRestrict.ext ι P.val)
            (QMCRestrict.ext ι Q.val)).re *
          L (QuantumMaxCutEnergy.PauliSDP.wordProduct (QMCRestrict.ext ι P.val)
            (QMCRestrict.ext ι Q.val))
      rw [QMCRestrict.wordPhase_ext hι, QMCRestrict.wordProduct_ext hι]
    rw [hEq]
    exact hpsd.submatrix emb
