-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P17.unitaryInvariance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:07:33.652999+00:00
-- url     : https://prove2.me/submissions/bee876b3-44ae-4434-90ab-bc3a2b4ad6d1

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P17
noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate Topology

namespace QAlgorithms.Papers.Independent.Advance50.P17

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P75 (hermitianReal)

variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]
  [Nonempty I] [Nonempty J] [Nonempty K]

theorem s110p17_pre {I' J' : Type} [Fintype I'] [Fintype J'] [DecidableEq I']
    (E : QAlgorithms.Superop I' J') (hE : QAlgorithms.IsChannel E) (V : Matrix I' I' ℂ)
    (hV : Vᴴ * V = 1) : QAlgorithms.IsChannel (E ∘ QAlgorithms.conjSuperop V) := by
  obtain ⟨m, K, hK, hEq⟩ := hE
  refine ⟨m, fun j => K j * V, ?_, ?_⟩
  · unfold QAlgorithms.IsKrausFamily at hK ⊢
    calc ∑ j, (K j * V)ᴴ * (K j * V) = Vᴴ * (∑ j, (K j)ᴴ * K j) * V := by
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hK, Matrix.mul_one, hV]
  · intro ρ
    simp only [Function.comp, hEq, QAlgorithms.krausApply, QAlgorithms.conjSuperop,
      Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem s110p17_post {I' J' : Type} [Fintype I'] [Fintype J'] [DecidableEq I'] [DecidableEq J']
    (E : QAlgorithms.Superop I' J') (hE : QAlgorithms.IsChannel E) (U : Matrix J' J' ℂ)
    (hU : Uᴴ * U = 1) : QAlgorithms.IsChannel (QAlgorithms.conjSuperop U ∘ E) := by
  obtain ⟨m, K, hK, hEq⟩ := hE
  refine ⟨m, fun j => U * K j, ?_, ?_⟩
  · unfold QAlgorithms.IsKrausFamily at hK ⊢
    rw [← hK]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU, Matrix.one_mul]
  · intro ρ
    simp only [Function.comp, hEq, QAlgorithms.krausApply, QAlgorithms.conjSuperop,
      Matrix.conjTranspose_mul, Finset.mul_sum, Finset.sum_mul, Matrix.mul_assoc]

theorem s110p17_le (delta : ProcessDistance) (hm : ProcessMetrics delta)
    (hc : ProcessChaining delta) (E F : FiniteProcess I J)
    (U : Matrix J J ℂ) (hU : Uᴴ * U = 1) (V : Matrix I I ℂ) (hV : Vᴴ * V = 1) :
    delta (QAlgorithms.conjSuperop U ∘ E.val ∘ QAlgorithms.conjSuperop V)
      (QAlgorithms.conjSuperop U ∘ F.val ∘ QAlgorithms.conjSuperop V) ≤ delta E.val F.val := by
  have cV : QAlgorithms.IsChannel (QAlgorithms.conjSuperop V) :=
    ⟨1, fun _ => V, by simp [QAlgorithms.IsKrausFamily, hV],
      fun ρ => by simp [QAlgorithms.krausApply, QAlgorithms.conjSuperop]⟩
  have cU : QAlgorithms.IsChannel (QAlgorithms.conjSuperop U) :=
    ⟨1, fun _ => U, by simp [QAlgorithms.IsKrausFamily, hU],
      fun ρ => by simp [QAlgorithms.krausApply, QAlgorithms.conjSuperop]⟩
  have h1 := hc I I J ⟨_, cV⟩ ⟨_, cV⟩ E F
  have h2 := hc I J J ⟨_, s110p17_pre _ E.2 V hV⟩ ⟨_, s110p17_pre _ F.2 V hV⟩ ⟨_, cU⟩ ⟨_, cU⟩
  have z1 : delta (QAlgorithms.conjSuperop V) (QAlgorithms.conjSuperop V) = 0 :=
    ((hm I I).2.1 ⟨_, cV⟩ ⟨_, cV⟩).mpr rfl
  have z2 : delta (QAlgorithms.conjSuperop U) (QAlgorithms.conjSuperop U) = 0 :=
    ((hm J J).2.1 ⟨_, cU⟩ ⟨_, cU⟩).mpr rfl
  simp only at h1 h2
  rw [z1] at h1; rw [z2] at h2
  linarith

end QAlgorithms.Papers.Independent.Advance50.P17

open QAlgorithms QAlgorithms.Papers.Independent.Advance50.P17

theorem solution {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    [Nonempty I] [Nonempty J]
    (delta : ProcessDistance) (hm : ProcessMetrics delta)
    (hc : ProcessChaining delta) (E F : FiniteProcess I J)
    (U : Matrix.unitaryGroup J ℂ) (V : Matrix.unitaryGroup I ℂ) :
    delta (conjSuperop (U : Matrix J J ℂ) ∘ E.val ∘ conjSuperop (V : Matrix I I ℂ))
      (conjSuperop (U : Matrix J J ℂ) ∘ F.val ∘ conjSuperop (V : Matrix I I ℂ)) =
        delta E.val F.val := by
  have hU : (U : Matrix J J ℂ)ᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp U.2
  have hV : (V : Matrix I I ℂ)ᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp V.2
  have hU' : ((U : Matrix J J ℂ)ᴴ)ᴴ * (U : Matrix J J ℂ)ᴴ = 1 := by
    rw [Matrix.conjTranspose_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.mp U.2
  have hV' : ((V : Matrix I I ℂ)ᴴ)ᴴ * (V : Matrix I I ℂ)ᴴ = 1 := by
    rw [Matrix.conjTranspose_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.mp V.2
  refine le_antisymm (s110p17_le delta hm hc E F _ hU _ hV) ?_
  have h := s110p17_le delta hm hc
    ⟨_, s110p17_post _ (s110p17_pre _ E.2 _ hV) _ hU⟩
    ⟨_, s110p17_post _ (s110p17_pre _ F.2 _ hV) _ hU⟩ _ hU' _ hV'
  have key : ∀ G : Superop I J,
      conjSuperop (U : Matrix J J ℂ)ᴴ ∘ (conjSuperop (U : Matrix J J ℂ) ∘ G ∘
        conjSuperop (V : Matrix I I ℂ)) ∘ conjSuperop (V : Matrix I I ℂ)ᴴ = G := by
    intro G; funext ρ
    simp only [Function.comp, conjSuperop, Matrix.conjTranspose_conjTranspose]
    have hVV : (V : Matrix I I ℂ) * ((V : Matrix I I ℂ)ᴴ * ρ * V) * (V : Matrix I I ℂ)ᴴ = ρ := by
      have := Matrix.mem_unitaryGroup_iff.mp V.2
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (V : Matrix I I ℂ), show (V : Matrix I I ℂ) * (V : Matrix I I ℂ)ᴴ = 1 from this,
        Matrix.one_mul, Matrix.mul_one]
    rw [hVV]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U : Matrix J J ℂ)ᴴ, hU, Matrix.one_mul, Matrix.mul_one]
  simp only [Function.comp_assoc] at h key
  rw [key, key] at h
  exact h

end
