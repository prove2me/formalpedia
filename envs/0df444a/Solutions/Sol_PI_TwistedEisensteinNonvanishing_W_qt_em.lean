-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.qt_em
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:00:38.181839+00:00
-- url     : https://prove2.me/submissions/904bc494-5992-494f-bd56-f495efebaf98

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_SumSliceEq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_WeightedSumToGaussSum
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_weighted_sum_to_gauss_sum
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_good_function_mono
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_good_slice
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_add
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_bound
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_div_down
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_mul
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_qpow
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_sub
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_up
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_qE_ne
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_rs_stab
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_sg_transl
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_sum_slice_eq
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_sum_vals
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_weighted_sum_scaling
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_weighted_sum_stable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE Function
variable {E K : Type} [Field E] [NumberField E] [Field K]
variable {P : HeightOneSpectrum (𝓞 E)} (hN : NTAll) (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hK : ((qOf P : ℕ) : K) ≠ 0)
include hN hp hq hK
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (k l : ι) {d : E} (hd : d ≠ 0) (c β : E)
    (hkl : l ≠ k ∨ c = 0) : QT P (em k l d c β) ((qOf P : K) ^ vq P d) := by
  have hq0 := qE_ne P hp
  intro a b
  obtain ⟨gc, hgc⟩ := ia_bound P hN hp hq c
  obtain ⟨gβ, hgβ⟩ := ia_bound P hN hp hq β
  obtain ⟨gd, hgd⟩ := ia_bound P hN hp hq d
  obtain ⟨gi, hgi⟩ := ia_bound P hN hp hq d⁻¹
  obtain ⟨a2, b2, hsc⟩ := weighted_sum_scaling hN hp hq hK hd (a + gc + gβ) b

  have hcl : ∀ t : ι → E, (∀ j, IntAt P ((qOf P : E) ^ a * t j)) →
      IntAt P ((qOf P : E) ^ (a + gc + gβ) * (c * t l + β)) := by
    intro t ht
    have e : (qOf P : E) ^ (a + gc + gβ) * (c * t l + β) =
        (qOf P : E) ^ gβ * (((qOf P : E) ^ gc * c) * ((qOf P : E) ^ a * t l)) +
          (qOf P : E) ^ (a + gc) * ((qOf P : E) ^ gβ * β) := by
      rw [pow_add, pow_add]
      ring
    rw [e]
    exact ia_add P (ia_mul P (ia_qpow P _) (ia_mul P hgc (ht l))) (ia_mul P (ia_qpow P _) hgβ)
  have hcl' : ∀ t : ι → E, (∀ j, j ≠ k → IntAt P ((qOf P : E) ^ a * t j)) →
      IntAt P ((qOf P : E) ^ (a + gc + gβ) * (c * t l + β)) := by
    intro t ht
    rcases hkl with hlk | hc0
    · have e : (qOf P : E) ^ (a + gc + gβ) * (c * t l + β) =
          (qOf P : E) ^ gβ * (((qOf P : E) ^ gc * c) * ((qOf P : E) ^ a * t l)) +
            (qOf P : E) ^ (a + gc) * ((qOf P : E) ^ gβ * β) := by
        rw [pow_add, pow_add]
        ring
      rw [e]
      exact ia_add P (ia_mul P (ia_qpow P _) (ia_mul P hgc (ht l hlk))) (ia_mul P (ia_qpow P _) hgβ)
    · have e : (qOf P : E) ^ (a + gc + gβ) * (c * t l + β) = (qOf P : E) ^ (a + gc) * ((qOf P : E) ^ gβ * β) := by
        rw [hc0, pow_add]
        ring
      rw [e]
      exact ia_mul P (ia_qpow P _) hgβ
  have hupd : ∀ (t : ι → E) (u : E), c * update t k u l = c * t l := by
    intro t u
    rcases hkl with hlk | hc0
    · rw [update_of_ne hlk]
    · rw [hc0, zero_mul, zero_mul]
  refine ⟨a + gc + gβ + gi, b + gd + gc, fun H hH => ?_⟩
  have hgood : Good P (a + gc + gβ + gi) (b + gd + gc) (fun t => H (em k l d c β t)) := by
    refine ⟨fun t ht j => ?_, fun t δ hδ => ?_⟩
    · have hs := hH.1 _ ht
      have hoth : ∀ j, j ≠ k → IntAt P ((qOf P : E) ^ a * t j) := by
        intro j hj
        have := hs j
        rwa [em, update_of_ne hj] at this
      by_cases hj : j = k
      · subst hj
        have hx := hs j
        rw [em, update_self] at hx
        have e : (qOf P : E) ^ (a + gc + gβ + gi) * t j = ((qOf P : E) ^ gi * d⁻¹) *
            ((qOf P : E) ^ (gc + gβ) * ((qOf P : E) ^ a * (d * t j + c * t l + β)) -
              (qOf P : E) ^ (a + gc + gβ) * (c * t l + β)) := by
          rw [pow_add, pow_add, pow_add, pow_add]
          field_simp
          ring
        rw [e]
        exact ia_mul P hgi (ia_sub P (ia_mul P (ia_qpow P _) hx) (hcl' t hoth))
      · exact ia_up P (by omega) (hoth j hj)
    · have e : em k l d c β (t + δ) = em k l d c β t + update δ k (d * δ k + c * δ l) := by
        ext j
        by_cases hj : j = k
        · subst hj
          simp only [em, update_self, Pi.add_apply]
          ring
        · simp only [em, update_of_ne hj, Pi.add_apply]
      show H (em k l d c β (t + δ)) = H (em k l d c β t)
      rw [e]
      apply hH.2
      intro j
      by_cases hj : j = k
      · subst hj
        rw [update_self]
        have e2 : (d * δ j + c * δ l) / (qOf P : E) ^ b = ((qOf P : E) ^ gd * d) * (δ j / (qOf P : E) ^ (b + gd)) +
            ((qOf P : E) ^ gc * c) * (δ l / (qOf P : E) ^ (b + gc)) := by
          rw [pow_add, pow_add]
          field_simp
        rw [e2]
        exact ia_add P (ia_mul P hgd (ia_div_down P hp (by omega) (hδ j)))
          (ia_mul P hgc (ia_div_down P hp (by omega) (hδ l)))
      · rw [update_of_ne hj]
        exact ia_div_down P hp (by omega) (hδ j)
  refine ⟨hgood, ?_⟩
  set N := max (max (a + gc + gβ + gi) (b + gd + gc)) (max (max a2 b2) (a + gc + gβ + b)) with hNdef
  rw [← rs_stab hN hp hq hK (A := N) (B := N) (by omega) (by omega) hgood,
    ← rs_stab hN hp hq hK (A := N) (B := N) (by omega) (by omega) hH]
  have key : ∑ t ∈ Fintype.piFinset (fun _ : ι => valsQ E (qOf P) N N), H (em k l d c β t) =
      (qOf P : K) ^ vq P d * ∑ t ∈ Fintype.piFinset (fun _ : ι => valsQ E (qOf P) N N), H t := by
    have h0 := sum_slice_eq k (fun _ : ι => valsQ E (qOf P) N N) (valsQ E (qOf P) N N) (valsQ E (qOf P) N N)
      (fun t => H (em k l d c β t)) H ((qOf P : K) ^ vq P d) ?_
    · rwa [update_eq_self k (fun _ : ι => valsQ E (qOf P) N N)] at h0
    intro t
    have e1 : ∀ u, em k l d c β (update t k u) = update t k (d * u + (c * t l + β)) := by
      intro u
      rw [em, update_idem, update_self, hupd, add_assoc]
    simp only [e1]
    by_cases hz : ∀ u, H (update t k u) = 0
    · rw [Finset.sum_eq_zero (fun u _ => hz _), Finset.sum_eq_zero (fun u _ => hz _), mul_zero]
    simp only [not_forall] at hz
    obtain ⟨u0, hu0⟩ := hz
    have hs := hH.1 _ hu0
    have hβ' : IntAt P ((qOf P : E) ^ (a + gc + gβ) * (c * t l + β)) := by
      apply hcl'
      intro j hj
      have := hs j
      rwa [update_of_ne hj] at this
    obtain ⟨gψ, eψ⟩ := sg_transl hN hp hq (good_function_mono (by omega) (good_slice hH t k)) hβ'
    obtain ⟨gs, es⟩ := hsc _ gψ
    have s1 : ∑ u ∈ valsQ E (qOf P) N N, H (update t k (d * u + (c * t l + β))) =
        Sg P N N (fun u => H (update t k (d * u + (c * t l + β)))) := sum_vals hp N N _
    have s2 : ∑ u ∈ valsQ E (qOf P) N N, H (update t k u) = Sg P N N (fun u => H (update t k u)) :=
      sum_vals hp N N _
    rw [s1, s2]
    apply weighted_sum_to_gauss_sum hN hp hq hK
    have w1 : W1 P N N (fun u => H (update t k (d * u + (c * t l + β)))) =
        W1 P a2 b2 (fun u => H (update t k (d * u + (c * t l + β)))) :=
      weighted_sum_stable hN hp hq hK (by omega) (by omega) gs
    have w2 : W1 P N N (fun u => H (update t k u)) = W1 P (a + gc + gβ) b (fun u => H (update t k u)) :=
      weighted_sum_stable hN hp hq hK (by omega) (by omega) (good_function_mono (by omega) (good_slice hH t k))
    rw [w1, es, w2]
    unfold W1
    rw [eψ]
  unfold RS
  rw [key]
  ring
end PI.TwistedEisensteinNonvanishing.W
