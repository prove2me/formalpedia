-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.sum_stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:43:14.153989+00:00
-- url     : https://prove2.me/submissions/3a584cb3-0f73-4918-aaf8-14f4ca4cca89

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_WeightedSumScaling
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_SumSliceEq
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_sum_slice_eq
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_good_slice
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_sg_stab


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
include hN hp hq
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {a b A B : ℕ} (hA : a ≤ A) (hB : b ≤ B)
    {H : (ι → E) → K} (hH : Good P a b H) :
    ∑ t ∈ Fintype.piFinset (fun _ : ι => valsQ E (qOf P) A B), H t =
      ((qOf P ^ (B - b) : ℕ) : K) ^ Fintype.card ι *
        ∑ t ∈ Fintype.piFinset (fun _ : ι => valsQ E (qOf P) a b), H t := by
  classical

  have sumV : ∀ (A' B' : ℕ) (φ : E → K), ∑ u ∈ valsQ E (qOf P) A' B', φ u = Sg P A' B' φ := by
    intro A' B' φ
    unfold valsQ Sg
    rw [Finset.sum_image]
    intro i hi j _ hij
    by_cases hq : ((qOf P : ℕ) : E) ^ A' = 0
    · exfalso
      have h2 := pow_eq_zero_iff'.1 hq
      have hq0 : qOf P = 0 := by exact_mod_cast h2.1
      simp [hq0, h2.2] at hi
    · exact_mod_cast (div_left_inj' hq).1 hij
  have hslice : ∀ (S : ι → Finset E) (k : ι),
      ∑ t ∈ Fintype.piFinset (update S k (valsQ E (qOf P) A B)), H t =
        ((qOf P ^ (B - b) : ℕ) : K) * ∑ t ∈ Fintype.piFinset (update S k (valsQ E (qOf P) a b)), H t :=
    fun S k => sum_slice_eq k S _ _ H H _ fun t => by
      rw [sumV, sumV, sg_stab hN hp hq hA hB (good_slice hH t k)]
  have key : ∀ s : Finset ι, ∑ t ∈ Fintype.piFinset (fun _ : ι => valsQ E (qOf P) A B), H t =
      ((qOf P ^ (B - b) : ℕ) : K) ^ s.card * ∑ t ∈ Fintype.piFinset
        (fun i => if i ∈ s then valsQ E (qOf P) a b else valsQ E (qOf P) A B), H t := by
    intro s
    refine Finset.induction_on s (by simp) ?_
    intro k s hk ih
    rw [ih, Finset.card_insert_of_notMem hk, pow_succ, mul_assoc]
    congr 1
    have e1 : (fun i => if i ∈ s then valsQ E (qOf P) a b else valsQ E (qOf P) A B) =
        update (fun i => if i ∈ s then valsQ E (qOf P) a b else valsQ E (qOf P) A B) k
          (valsQ E (qOf P) A B) := by
      funext i
      by_cases h : i = k
      · subst h; simp [hk]
      · simp [h]
    have e2 : (fun i => if i ∈ insert k s then valsQ E (qOf P) a b else valsQ E (qOf P) A B) =
        update (fun i => if i ∈ s then valsQ E (qOf P) a b else valsQ E (qOf P) A B) k
          (valsQ E (qOf P) a b) := by
      funext i
      by_cases h : i = k
      · subst h; simp
      · simp [h]
    rw [e2]
    conv_lhs => rw [e1]
    exact hslice _ k
  simpa using key Finset.univ
end PI.TwistedEisensteinNonvanishing.W
