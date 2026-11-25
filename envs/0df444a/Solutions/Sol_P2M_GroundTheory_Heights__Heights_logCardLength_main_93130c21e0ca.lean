-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_logCardLength_main_93130c21e0ca
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:47:48.500632+00:00
-- url     : https://prove2.me/submissions/a3be6539-0916-4511-9102-69e18376acaf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLogCardLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLogCardLength
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_logCardLength_term_eq_8e0283e60fb9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_logCardLength_term_of_not_5772e4436efb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_logCardLength_length_loc_add_dd1c77339ebc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_logCardLength_length_loc_simple_26bd67a2a4aa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_logCardLength_term_simple_b0525ec75e65

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
noncomputable section
open GroundTheory.Heights₂.Heights.logCardLength
open Module
variable (R : Type) [CommRing R]
variable {R}
namespace GroundTheory.Heights₂.Heights.logCardLength
theorem _root_.solution (n : ℕ) : ∀ (N : Type) [AddCommGroup N] [Module R N] [Finite N], Nat.card N = n →
    FinLoc R N ∧ (Function.support (term R N)).Finite ∧
      Real.log (Nat.card N) = ∑ᶠ m, term R N m := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro N _ _ _ hn
  rcases subsingleton_or_nontrivial N with hN | hN
  · have h0 : ∀ (m : Ideal R) [m.IsPrime],
        Module.length (Localization.AtPrime m) (LocalizedModule m.primeCompl N) = 0 :=
      fun m _ => Module.length_eq_zero
    have ht : ∀ m, term R N m = 0 := by
      intro m
      by_cases hm : m.IsMaximal
      · rw [term_eq, h0]; simp
      · exact term_of_not N m hm
    refine ⟨fun m _ => by rw [h0]; exact ENat.zero_ne_top,
      by rw [show term R N = 0 from funext ht, Function.support_zero]; exact Set.finite_empty, ?_⟩
    rw [Nat.card_of_subsingleton (0 : N)]
    simp [ht]
  · have := isArtinian_of_finite (R := R) (M := N)
    obtain ⟨S, hS⟩ := IsAtomic.exists_atom (Submodule R N)
    rw [← isSimpleModule_iff_isAtom] at hS
    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hS
    have hkill : ∀ a ∈ I, ∀ x : S, a • x = 0 := by
      intro a ha x
      apply e.injective
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (e x)
      rw [map_smul, ← hr, map_zero, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
        Ideal.Quotient.eq_zero_iff_mem]
      exact I.mul_mem_right r ha
    have hcS : Nat.card S = Nat.card (R ⧸ I) := Nat.card_congr e.toEquiv
    have : Finite (N ⧸ S) := Finite.of_surjective _ S.mkQ_surjective
    have hcard : Nat.card N = Nat.card S * Nat.card (N ⧸ S) := S.card_eq_card_quotient_mul_card
    have := IsSimpleModule.nontrivial R S
    have hS1 : 1 < Nat.card S := Finite.one_lt_card
    have hQpos : 0 < Nat.card (N ⧸ S) := Nat.card_pos
    have hlt : Nat.card (N ⧸ S) < n := by
      rw [← hn, hcard]; exact lt_mul_of_one_lt_left hQpos hS1
    obtain ⟨hQf, hQs, hQl⟩ := ih _ hlt (N ⧸ S) rfl
    have hadd : ∀ (m : Ideal R) [m.IsPrime],
        Module.length (Localization.AtPrime m) (LocalizedModule m.primeCompl N) =
          Module.length (Localization.AtPrime m) (LocalizedModule m.primeCompl S) +
            Module.length (Localization.AtPrime m) (LocalizedModule m.primeCompl (N ⧸ S)) :=
      fun m _ => length_loc_add S.subtype S.mkQ S.injective_subtype S.mkQ_surjective
        (LinearMap.exact_subtype_mkQ S) m
    have hSt := term_simple S I hI hkill hcS
    have hterm : ∀ m, term R N m = term R S m + term R (N ⧸ S) m := by
      intro m
      by_cases hm : m.IsMaximal
      · have hQm := hQf m
        rw [term_eq, term_eq, term_eq, hadd, length_loc_simple S I hI hkill m] at *
        split_ifs <;> simp [ENat.toNat_add _ hQm]; ring
      · rw [term_of_not N m hm, term_of_not S m hm, term_of_not _ m hm, add_zero]
    have hSs : (Function.support (term R S)).Finite := by
      refine (Set.finite_singleton I).subset fun m hm => ?_
      by_contra h
      exact hm (by rw [hSt, if_neg (by simpa using h)])
    refine ⟨fun m _ => ?_, ?_, ?_⟩
    · rw [hadd, length_loc_simple S I hI hkill m]
      split_ifs <;> simpa using hQf m
    · exact (hSs.union hQs).subset (by
        rw [show term R N = fun m => term R S m + term R (N ⧸ S) m from funext hterm]
        exact Function.support_add _ _)
    · rw [show term R N = fun m => term R S m + term R (N ⧸ S) m from funext hterm,
        finsum_add_distrib hSs hQs, ← hQl,
        finsum_eq_single _ I (fun m hm => by rw [hSt, if_neg hm]), hSt, if_pos rfl, hcard,
        Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
end GroundTheory.Heights₂.Heights.logCardLength
