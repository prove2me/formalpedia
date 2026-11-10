-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P55.lemma_3_8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T03:39:23.529398+00:00
-- url     : https://prove2.me/submissions/c2caf82f-5c59-4cf5-9e06-3d942a3a0a91

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P55

noncomputable section

open scoped Classical

open QAlgorithms.Papers.Independent.Intake100.P55 in
theorem solution {R : Type*} [CommRing R] (P : Ground R) (q : ℕ → R)
    (aff : Bool) (n i : ℕ) (hi : BMWIndex n i) :
    ghCrossing P q aff n i false ^ 2 = 1 +
      algebraMap R _ ((↑P.lam⁻¹ : R) * P.z) * ghContraction P q aff n i -
      algebraMap R _ P.z * ghCrossing P q aff n i false ∧
    ghCrossing P q aff n i true ^ 2 = 1 -
      algebraMap R _ ((P.lam : R) * P.z) * ghContraction P q aff n i +
      algebraMap R _ P.z * ghCrossing P q aff n i true := by
  set A := OrdinaryAffineBMW P q aff n
  set G := ghCrossing P q aff n i false with hGdef
  set H := ghCrossing P q aff n i true with hHdef
  set E := ghContraction P q aff n i with hEdef
  have hGH : G * H = 1 := by
    rw [hGdef, hHdef]
    unfold ghCrossing
    rw [← map_mul]
    unfold presentation
    rw [RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.invL (P := P) (q := q) (aff := aff)
      (n := n) i hi), map_one]
  have hHG : H * G = 1 := by
    rw [hGdef, hHdef]
    unfold ghCrossing
    rw [← map_mul]
    unfold presentation
    rw [RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.invR (P := P) (q := q) (aff := aff)
      (n := n) i hi), map_one]
  have hsk : G - H = algebraMap R A P.z * (E - 1) := by
    rw [hGdef, hHdef, hEdef]
    unfold ghCrossing ghContraction
    rw [← map_sub]
    unfold presentation
    rw [RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.skein (P := P) (q := q) (aff := aff)
      (n := n) i hi), map_mul, map_sub, map_one, AlgHom.commutes]
  have hGE : G * E = algebraMap R A (↑P.lam⁻¹ : R) * E := by
    rw [hGdef, hEdef]
    unfold ghCrossing ghContraction
    rw [← map_mul]
    unfold presentation
    rw [RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.untwistL (P := P) (q := q) (aff := aff)
      (n := n) i hi), map_mul, AlgHom.commutes]
  have hc : ∀ (r : R) (x : A), x * algebraMap R A r = algebraMap R A r * x :=
    fun r x => (Algebra.commutes r x).symm
  have hG' : G = H + algebraMap R A P.z * (E - 1) := by rw [← hsk]; abel
  have hH' : H = G - algebraMap R A P.z * (E - 1) := by rw [← hsk]; abel
  refine ⟨?_, ?_⟩
  · calc G ^ 2 = G * G := pow_two G
      _ = G * (H + algebraMap R A P.z * (E - 1)) := by rw [← hG']
      _ = G * H + (G * algebraMap R A P.z) * (E - 1) := by rw [mul_add, mul_assoc]
      _ = 1 + (algebraMap R A P.z * G) * (E - 1) := by rw [hGH, hc]
      _ = 1 + algebraMap R A P.z * (G * E) - algebraMap R A P.z * G := by
          rw [mul_assoc, mul_sub, mul_one, mul_sub]; abel
      _ = 1 + algebraMap R A ((↑P.lam⁻¹ : R) * P.z) * E - algebraMap R A P.z * G := by
          rw [hGE, ← mul_assoc, ← map_mul, mul_comm P.z]
  · have hHE : H * E = algebraMap R A (P.lam : R) * E := by
      have h1 : H * (G * E) = H * (algebraMap R A (↑P.lam⁻¹ : R) * E) := by rw [hGE]
      rw [← mul_assoc, hHG, one_mul, ← mul_assoc, hc, mul_assoc] at h1
      calc H * E = algebraMap R A (P.lam : R) * (algebraMap R A (↑P.lam⁻¹ : R) * (H * E)) := by
            rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
        _ = algebraMap R A (P.lam : R) * E := by rw [← h1]
    calc H ^ 2 = H * H := pow_two H
      _ = H * (G - algebraMap R A P.z * (E - 1)) := by rw [← hH']
      _ = H * G - (H * algebraMap R A P.z) * (E - 1) := by rw [mul_sub, mul_assoc]
      _ = 1 - (algebraMap R A P.z * H) * (E - 1) := by rw [hHG, hc]
      _ = 1 - algebraMap R A P.z * (H * E) + algebraMap R A P.z * H := by
          rw [mul_assoc, mul_sub, mul_one, mul_sub]; abel
      _ = 1 - algebraMap R A ((P.lam : R) * P.z) * E + algebraMap R A P.z * H := by
          rw [hHE, ← mul_assoc, ← map_mul, mul_comm P.z]
