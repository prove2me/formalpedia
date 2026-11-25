-- Prove2me | solution 1 for PI.OpWords.opWords_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:08:32.603341+00:00
-- url     : https://prove2.me/submissions/e4e156cc-6232-4e15-b473-293c2cb73918

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_DivideAll
import Theorems.Thm_PI_OpWords_wtLe_span
import Theorems.Thm_PI_OpWords_kappa_ad
import Theorems.Thm_PI_OpWords_divide_all

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.OpWords
namespace PI.OpWords
theorem _root_.solution (hI : KappaInj) (hL : KappaLeft) (hR : KappaRight) (hB : KappaBihom)
    (hE : WtOfEig) (hRB : RBihom) (hRT : RTT) (hTW : TTWt) (hD : DivT) (hV : Vanish)
    (hS : Surj) : Formalism.MainNotions.TestSideCounting.OpBound := by
  intro K _ _ k d c WW Sg hst hspan heig A hA
  have key : ∃ c' : ℕ, c' ≤ c ∧ c' ≤ d ∧ ∃ g ∈ Bihom K k c', kappa K k d A = tt K k ^ (d - c') * g := by
    rcases Nat.lt_or_ge c d with hcd | hdc
    · let W : Submodule K (Pol K k) := WW.map (kappa K k d)
      have hW : W ≤ Bihom K k (c + (d - c)) := by
        have e : c + (d - c) = d := by omega
        rw [e]
        rintro f ⟨A', _, rfl⟩
        exact hB K k d A'
      have hWst : ∀ f ∈ W, ∀ a b, Rop K k a b f ∈ W := by
        rintro f ⟨A', hA', rfl⟩ a b
        rw [← kappa_ad hL hR K k d a b A']
        exact Submodule.mem_map_of_mem (hst A' hA' a b)
      have hWwt : ∀ f ∈ W, WtLe K k c f := by
        have hWeq : W = Submodule.span K (kappa K k d '' Sg) := by
          show WW.map (kappa K k d) = _
          rw [hspan, Submodule.map_span]
        rw [hWeq]
        apply wtLe_span
        rintro f ⟨A', hA', rfl⟩ m hm a
        obtain ⟨ω, hω, hωc⟩ := heig A' hA'
        have h1 : Rop K k a a (kappa K k d A') = (ω a : K) • kappa K k d A' := by
          rw [← kappa_ad hL hR K k d a a A', hω a, map_smul]
        have h2 := hE K k a (ω a) (kappa K k d A') h1 m hm
        rw [h2]
        exact_mod_cast hωc a
      obtain ⟨g, hg, he⟩ := divide_all hV hD hRB hRT hTW K k c (d - c) W hW hWst hWwt _
        (Submodule.mem_map_of_mem hA)
      exact ⟨c, le_rfl, hcd.le, g, hg, he⟩
    · exact ⟨d, hdc, le_rfl, kappa K k d A, hB K k d A, by simp⟩
  obtain ⟨c', hc'c, hc'd, g, hg, he⟩ := key
  have hsurj := hS K k d c' hc'd g hg
  rw [← he] at hsurj
  obtain ⟨B, hB', hBe⟩ := Submodule.mem_map.1 hsurj
  have hAB : B = A := hI K k d hBe
  subst hAB
  have hmono : Wc K k d c' ≤ Wc K k d c := by
    unfold Wc
    apply Submodule.span_mono
    rintro Bx ⟨l, hl, rfl⟩
    exact ⟨l, le_trans hl hc'c, rfl⟩
  exact hmono hB'
end PI.OpWords
