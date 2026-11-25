-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.test_function_periodicity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:36:10.43295+00:00
-- url     : https://prove2.me/submissions/b50cb53e-0083-4785-ac5c-745f337b713b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_JacobianTransformationLaw
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_TestFunctionPeriodicity
import Theorems.Thm_P2M_PI_TwistedEisensteinNonvanishing_W_entB_add__256bd4120105
import Theorems.Thm_P2M_PI_TwistedEisensteinNonvanishing_W_unitV_congr__117095e1432c
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_aym_det_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain Module
noncomputable section
namespace PI.TwistedEisensteinNonvanishing.W
open Loc LocE
section PhiFacts
variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}
end PhiFacts
private theorem algebraMap_integers_injective {E : Type} [Field E] [NumberField E] :
    Function.Injective (algebraMap (𝓞 E) E) := by
  first
    | exact IsFractionRing.injective (𝓞 E) E
    | exact FaithfulSMul.algebraMap_injective (𝓞 E) E
private theorem mul_not_mem_of_not_mem {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {s t : 𝓞 E}
    (hs : s ∉ P.asIdeal) (ht : t ∉ P.asIdeal) : s * t ∉ P.asIdeal :=
  fun h => (P.isPrime.mem_or_mem h).elim hs ht
private theorem one_not_mem_asIdeal {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} : (1 : 𝓞 E) ∉ P.asIdeal :=
  fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
private theorem intAt_add_of_starRing {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {a b : E} (ha : IntAt P a) (hb : IntAt P b) :
    IntAt P (a + b) := by
  obtain ⟨r1, s1, hs1, h1⟩ := ha
  obtain ⟨r2, s2, hs2, h2⟩ := hb
  refine ⟨s2 * r1 + s1 * r2, s1 * s2, mul_not_mem_of_not_mem hs1 hs2, ?_⟩
  simp only [map_add, map_mul]
  rw [← h1, ← h2]
  ring
private theorem intAt_mul_twisted_eisenstein_coset {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {a b : E} (ha : IntAt P a) (hb : IntAt P b) :
    IntAt P (a * b) := by
  obtain ⟨r1, s1, hs1, h1⟩ := ha
  obtain ⟨r2, s2, hs2, h2⟩ := hb
  refine ⟨r1 * r2, s1 * s2, mul_not_mem_of_not_mem hs1 hs2, ?_⟩
  simp only [map_mul]
  rw [← h1, ← h2]
  ring
private theorem intAt_neg_of_starRing {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {a : E} (ha : IntAt P a) : IntAt P (-a) := by
  obtain ⟨r, s, hs, h⟩ := ha
  exact ⟨-r, s, hs, by rw [mul_neg, h, map_neg]⟩
private theorem intAt_natCast_twisted_eisenstein_coset {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} (m : ℕ) : IntAt P (m : E) :=
  ⟨m, 1, one_not_mem_asIdeal, by simp⟩
private theorem mk_mul_redP_eq_of_mul_eq {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {a : E} (r s : 𝓞 E) (hs : s ∉ P.asIdeal)
    (h : algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r) :
    Ideal.Quotient.mk P.asIdeal s * redP P a = Ideal.Quotient.mk P.asIdeal r := by
  haveI : P.asIdeal.IsMaximal := by
    first
      | exact P.isMaximal
      | exact P.isPrime.isMaximal P.ne_bot
  have hs0 : Ideal.Quotient.mk P.asIdeal s ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv hs0
  have hex : ∃ c : 𝓞 E ⧸ P.asIdeal, ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧
      algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk P.asIdeal s * c = Ideal.Quotient.mk P.asIdeal r :=
    ⟨b * Ideal.Quotient.mk P.asIdeal r, r, s, hs, h, by rw [← mul_assoc, hb, one_mul]⟩
  unfold redP
  rw [dif_pos hex]
  obtain ⟨r', s', hs', h', hc⟩ := hex.choose_spec
  have hs0' : Ideal.Quotient.mk P.asIdeal s' ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have key : s * r' = s' * r := algebraMap_integers_injective (by simp only [map_mul]; rw [← h, ← h']; ring)
  apply mul_left_cancel₀ hs0'
  calc Ideal.Quotient.mk P.asIdeal s' * (Ideal.Quotient.mk P.asIdeal s * hex.choose)
      = Ideal.Quotient.mk P.asIdeal s * (Ideal.Quotient.mk P.asIdeal s' * hex.choose) := by ring
    _ = Ideal.Quotient.mk P.asIdeal s * Ideal.Quotient.mk P.asIdeal r' := by rw [hc]
    _ = Ideal.Quotient.mk P.asIdeal s' * Ideal.Quotient.mk P.asIdeal r := by
      rw [← map_mul, ← map_mul, key]
private theorem redP_add_twisted_eisenstein_coset {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {a b : E} (ha : IntAt P a) (hb : IntAt P b) :
    redP P (a + b) = redP P a + redP P b := by
  obtain ⟨r1, s1, hs1, h1⟩ := ha
  obtain ⟨r2, s2, hs2, h2⟩ := hb
  have hs := mul_not_mem_of_not_mem hs1 hs2
  have e3 := mk_mul_redP_eq_of_mul_eq (a := a + b) (s2 * r1 + s1 * r2) (s1 * s2) hs (by
    simp only [map_add, map_mul]
    rw [← h1, ← h2]
    ring)
  have e1 := mk_mul_redP_eq_of_mul_eq r1 s1 hs1 h1
  have e2 := mk_mul_redP_eq_of_mul_eq r2 s2 hs2 h2
  have hs0 : Ideal.Quotient.mk P.asIdeal (s1 * s2) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  apply mul_left_cancel₀ hs0
  rw [e3]
  simp only [map_add, map_mul]
  rw [← e1, ← e2]
  ring
private theorem redP_mul_twisted_eisenstein_coset {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {a b : E} (ha : IntAt P a) (hb : IntAt P b) :
    redP P (a * b) = redP P a * redP P b := by
  obtain ⟨r1, s1, hs1, h1⟩ := ha
  obtain ⟨r2, s2, hs2, h2⟩ := hb
  have hs := mul_not_mem_of_not_mem hs1 hs2
  have e3 := mk_mul_redP_eq_of_mul_eq (a := a * b) (r1 * r2) (s1 * s2) hs (by
    simp only [map_mul]
    rw [← h1, ← h2]
    ring)
  have e1 := mk_mul_redP_eq_of_mul_eq r1 s1 hs1 h1
  have e2 := mk_mul_redP_eq_of_mul_eq r2 s2 hs2 h2
  have hs0 : Ideal.Quotient.mk P.asIdeal (s1 * s2) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  apply mul_left_cancel₀ hs0
  rw [e3]
  simp only [map_mul]
  rw [← e1, ← e2]
  ring
private theorem redP_natCast {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} (m : ℕ) :
    redP P (m : E) = Ideal.Quotient.mk P.asIdeal (m : 𝓞 E) := by
  have e := mk_mul_redP_eq_of_mul_eq (P := P) (a := (m : E)) (m : 𝓞 E) 1 one_not_mem_asIdeal (by simp)
  rwa [map_one, one_mul] at e
private theorem redP_det_twisted_eisenstein_coset {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {r : ℕ} (M : Matrix (Fin r) (Fin r) E)
    (hM : ∀ i j, IntAt P (M i j)) :
    redP P M.det = (Matrix.of fun i j => redP P (M i j)).det := by
  let S : Subring E :=
    { carrier := {a | IntAt P a}
      mul_mem' := fun ha hb => intAt_mul_twisted_eisenstein_coset ha hb
      one_mem' := by simpa using intAt_natCast_twisted_eisenstein_coset (P := P) 1
      add_mem' := fun ha hb => intAt_add_of_starRing ha hb
      zero_mem' := by simpa using intAt_natCast_twisted_eisenstein_coset (P := P) 0
      neg_mem' := fun ha => intAt_neg_of_starRing ha }
  let φ : S →+* 𝓞 E ⧸ P.asIdeal :=
    { toFun := fun a => redP P (a : E)
      map_one' := by simpa using redP_natCast (P := P) 1
      map_mul' := fun a b => redP_mul_twisted_eisenstein_coset a.2 b.2
      map_zero' := by simpa using redP_natCast (P := P) 0
      map_add' := fun a b => redP_add_twisted_eisenstein_coset a.2 b.2 }
  let MS : Matrix (Fin r) (Fin r) S := Matrix.of fun i j => ⟨M i j, hM i j⟩
  have h1 : ((MS.det : S) : E) = M.det := by
    change S.subtype MS.det = M.det
    rw [RingHom.map_det]
    rfl
  have h2 : φ MS.det = (Matrix.of fun i j => redP P (M i j)).det := by
    rw [RingHom.map_det]
    rfl
  rw [← h1, ← h2]
  rfl
end PI.TwistedEisensteinNonvanishing.W
end
end

set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution : PhiPerP := by
  intro E K _ _ _ _ P _ _ ξ k₀ r c' n' c n y ε hε
  have hq : ∀ (x : HomE E (n' + c') (n + c)) (a b : ℕ), entB (qOf P) k₀ c' n' c n 0 0 x a b
      = atN (x (eN E (n' + c') (fIdx k₀ c' n' b))) (fIdx k₀ c n a) := by
    intro x a b
    simp [entB, scE]
  have hq0 : (qOf P : E) ≠ 0 := by
    have h0 : Ideal.absNorm P.asIdeal ≠ 0 := fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
    simp only [qOf]
    exact_mod_cast h0
  have hredq : redP P (qOf P : E) = 0 := by
    rw [redP_natCast, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.absNorm_mem _
  have hεd : ∀ p p', IntAt P (entB (qOf P) k₀ c' n' c n 0 0 ε p p' / (qOf P : E)) := by
    intro p p'
    rw [hq]
    unfold atN
    split_ifs with hi
    · exact hε _ _
    · rw [zero_div]
      simpa using intAt_natCast_twisted_eisenstein_coset (P := P) 0
  have hε1 : ∀ p p', IntAt P (entB (qOf P) k₀ c' n' c n 0 0 ε p p') := by
    intro p p'
    have h := intAt_mul_twisted_eisenstein_coset (intAt_natCast_twisted_eisenstein_coset (P := P) (qOf P)) (hεd p p')
    rwa [mul_div_cancel₀ _ hq0] at h
  have hεr : ∀ p p', redP P (entB (qOf P) k₀ c' n' c n 0 0 ε p p') = 0 := by
    intro p p'
    rw [← mul_div_cancel₀ (entB (qOf P) k₀ c' n' c n 0 0 ε p p') hq0,
      redP_mul_twisted_eisenstein_coset (intAt_natCast_twisted_eisenstein_coset (qOf P)) (hεd p p'), hredq, zero_mul]
  have e : ∀ p p', entB (qOf P) k₀ c' n' c n 0 0 (y + ε) p p'
      = entB (qOf P) k₀ c' n' c n 0 0 y p p' + entB (qOf P) k₀ c' n' c n 0 0 ε p p' :=
    fun p p' => entB_add' _ _ _ _ _ _ y ε p p'
  simp only [PhiQ]
  simp only [e]
  split_ifs with h1 h2 h2
  · apply unitV_congr'
    by_cases hr : n + c < r ∨ n' + c' < r
    · have d1 := aym_det_zero (qOf P) k₀ r c' n' c n (y + ε) hr
      have d2 := aym_det_zero (qOf P) k₀ r c' n' c n y hr
      simp only [AYm, e] at d1 d2
      rw [d1, d2]
    · push_neg at hr
      have hi : ∀ i : Fin r, i.1 < n + c := fun i => by have := i.2; omega
      have hj : ∀ j : Fin r, j.1 < n' + c' := fun j => by have := j.2; omega
      rw [redP_det_twisted_eisenstein_coset (Matrix.of fun s t : Fin r =>
          entB (qOf P) k₀ c' n' c n 0 0 y s.1 t.1 + entB (qOf P) k₀ c' n' c n 0 0 ε s.1 t.1)
          (fun i j => by rw [Matrix.of_apply, ← e]; exact h1.1 _ _ (hi i) (hj j)),
        redP_det_twisted_eisenstein_coset (Matrix.of fun s t : Fin r => entB (qOf P) k₀ c' n' c n 0 0 y s.1 t.1)
          (fun i j => h2.1 _ _ (hi i) (hj j))]
      congr 1
      ext i j
      simp only [Matrix.of_apply]
      rw [redP_add_twisted_eisenstein_coset (h2.1 _ _ (hi i) (hj j)) (hε1 _ _), hεr, add_zero]
  · exfalso
    apply h2
    refine ⟨fun p p' hp hp' => ?_, fun p p' hp hp' hp'' => ?_⟩
    · have h := intAt_add_of_starRing (h1.1 p p' hp hp') (intAt_neg_of_starRing (hε1 p p'))
      rwa [e, add_neg_cancel_right] at h
    · have h := intAt_add_of_starRing (h1.2 p p' hp hp' hp'') (intAt_neg_of_starRing (hεd p p'))
      rwa [e, add_div, add_neg_cancel_right] at h
  · exfalso
    apply h1
    refine ⟨fun p p' hp hp' => by rw [e]; exact intAt_add_of_starRing (h2.1 p p' hp hp') (hε1 p p'),
      fun p p' hp hp' hp'' => ?_⟩
    rw [e, add_div]
    exact intAt_add_of_starRing (h2.2 p p' hp hp' hp'') (hεd p p')
  · rfl
end PI.TwistedEisensteinNonvanishing.W
