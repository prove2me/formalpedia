-- Prove2me | solution 1 for RepellingPairs.claim_13_case_B
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T11:06:29.750199+00:00
-- url     : https://prove2.me/submissions/2acfca4c-c0f2-410f-b9bf-c72912acfe51

import Mathlib
import Definitions.Def_RepellingPairs_Config
import Definitions.Def_RepellingPairs_PerfectMatching
import Definitions.Def_RepellingPairs_IsGoodPair
import Definitions.Def_Claim13Aux
import Definitions.Def_RepellingPairs_CyclicallyOrdered

section
set_option autoImplicit false

namespace RepellingPairs.Dev.CutCount

open RepellingPairs RepellingPairs.Config
open Classical

variable {n : ℕ}

export RepellingPairs.Claim13Aux (cr ar oa)

theorem segcount_lt (C : PerfectMatching n) (p q p' q' w : Fin n)
    (hsub : ∀ a, (CyclicallyOrdered (C.partner p') p' a q' ∨ CyclicallyOrdered (C.partner p') q' a p') →
      (CyclicallyOrdered (C.partner p) p a q ∨ CyclicallyOrdered (C.partner p) q a p))
    (hw : CyclicallyOrdered (C.partner p) p w q ∨ CyclicallyOrdered (C.partner p) q w p)
    (hnw : ¬ (CyclicallyOrdered (C.partner p') p' w q' ∨ CyclicallyOrdered (C.partner p') q' w p')) :
    segmentCount C p' q' < segmentCount C p q := by
  unfold segmentCount
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨w, by simpa using hw, by simpa using hnw⟩
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact hsub a ha

end RepellingPairs.Dev.CutCount
end

section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace RepellingPairs.Dev.Claim13Key

open RepellingPairs RepellingPairs.Config RepellingPairs.Dev.CutCount

variable {n : ℕ}

theorem hsmall (C C' : PerfectMatching n) (x y : Fin n)
    (hmin : ∀ x₂ y₂, IsGoodPair C C' x₂ y₂ → segmentCount C x y ≤ segmentCount C x₂ y₂)
    (p q w : Fin n) (hg : IsGoodPair C C' p q)
    (hsub : ∀ a, (CyclicallyOrdered (C.partner p) p a q ∨ CyclicallyOrdered (C.partner p) q a p) →
      (CyclicallyOrdered (C.partner x) x a y ∨ CyclicallyOrdered (C.partner x) y a x))
    (hw : CyclicallyOrdered (C.partner x) x w y ∨ CyclicallyOrdered (C.partner x) y w x)
    (hnw : ¬ (CyclicallyOrdered (C.partner p) p w q ∨ CyclicallyOrdered (C.partner p) q w p)) : False := by
  have h1 := hmin p q hg
  have h2 := segcount_lt C x y p q w hsub hw hnw
  omega

export RepellingPairs.Claim13Aux (Ctx13)

end RepellingPairs.Dev.Claim13Key
end

section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace RepellingPairs.Dev.Claim13Key

open RepellingPairs RepellingPairs.Config RepellingPairs.Dev.CutCount

variable {n : ℕ}

export RepellingPairs.Claim13Aux (KD)

end RepellingPairs.Dev.Claim13Key
end

section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace RepellingPairs.Dev.Claim13Key

open RepellingPairs RepellingPairs.Config RepellingPairs.Dev.CutCount

variable {n : ℕ}

set_option maxHeartbeats 8000000 in
theorem key13B (C C' : PerfectMatching n) (x y : Fin n) (s m : ℕ) (e : Fin n)
    (K : Ctx13 C C' x y s m e)
    (hA : ¬ InSegment x (C.partner x) (C'.partner x) (C.partner e))
    (hB : OnDifferentSides e (C.partner e) x (C'.partner e)) : False := by
  obtain ⟨hgood, hmin, hdom, hs, hm0, hmn, hx, hc'x, hy, hcx, hend, hxe, hc'xe, hgap, hCe, hC'e⟩ := K
  have heS : ar n s m e := by
    have := e.2
    unfold ar; omega
  have iCe := C.involutive e
  have hcc : C'.partner e ≠ C.partner e := fun h => hC'e (h ▸ hCe)
  have h1 : C.partner e ≠ x := by
    intro h; apply hcx
    have : e = C.partner x := by rw [← h, C.involutive]
    rw [← this]; exact heS
  have h2 : C'.partner e ≠ x := by
    intro h; apply hc'xe
    rw [← h, C'.involutive]
  have h3 : C.partner e ≠ C.partner x := fun h => hxe (C.involutive.injective h)
  have h4 : C'.partner e ≠ C'.partner x := fun h => hxe (C'.involutive.injective h)
  have h5 := C.ne_self e
  have h5c := C.ne_self e
  have h6 := C'.ne_self e
  have h6' := C'.ne_self e
  have h7 := C.ne_self x
  have h8 := C'.ne_self x
  obtain ⟨hcr, hdf, hsg⟩ := hgood
  have hgood' : IsGoodPair C C' x y := ⟨hcr, hdf, hsg⟩
  have hgap0 := hgap
  simp only [CyclicallyOrdered, InSegment, OnDifferentSides, Config.ChordsCross, Fin.lt_def, Fin.ext_iff, ne_eq, iCe] at hx hc'x hy hcx hend hxe hc'xe hgap hCe hC'e h1 h2 h3 h4 h5 h6 h7 h8 heS hdf hcr hsg
  simp only [ar, oa] at hx hc'x hy hcx hend hxe hc'xe hgap hCe hC'e heS
  clear hcr hsg
  have hAn := hA
  simp only [CyclicallyOrdered, InSegment, OnDifferentSides, Config.ChordsCross, Fin.lt_def, Fin.ext_iff, ne_eq, iCe] at hAn
  have hBn := hB
  simp only [CyclicallyOrdered, InSegment, OnDifferentSides, Config.ChordsCross, Fin.lt_def, Fin.ext_iff, ne_eq, iCe] at hBn
  have hg : IsGoodPair C C' e x := by
    refine ⟨?_, hB, ?_⟩
    · simp only [CyclicallyOrdered, InSegment, OnDifferentSides, Config.ChordsCross, Fin.lt_def, Fin.ext_iff, ne_eq, iCe]
      clear hmin hdom hgood'; grind (splits := 1000)
    · simp only [CyclicallyOrdered, InSegment, OnDifferentSides, Config.ChordsCross, Fin.lt_def, Fin.ext_iff, ne_eq, iCe]
      clear hmin hdom hgood'; grind (splits := 1000)
  refine hsmall C C' x y hmin e x e hg ?_ hgap0 ?_
  · intro a ha
    simp only [CyclicallyOrdered, InSegment, OnDifferentSides, Config.ChordsCross, Fin.lt_def, Fin.ext_iff, ne_eq, iCe] at ha ⊢
    clear hmin hdom hgood'; rcases ha with ((ha|ha|ha|ha)|(ha|ha|ha|ha)) <;> rcases hgap with ((hgap|hgap|hgap|hgap)|(hgap|hgap|hgap|hgap)) <;> grind (splits := 1000)
  · simp only [CyclicallyOrdered, InSegment, OnDifferentSides, Config.ChordsCross, Fin.lt_def, Fin.ext_iff, ne_eq, iCe]
    clear hmin hdom hgood'; grind (splits := 1000)

end RepellingPairs.Dev.Claim13Key
end

section
set_option autoImplicit false

namespace RepellingPairs

theorem chk_claim_13_case_B {n : ℕ} (C C' : PerfectMatching n) (x y : Fin n) (s m : ℕ) (e : Fin n)
    (K : Claim13Aux.Ctx13 C C' x y s m e)
    (hA : ¬ InSegment x (C.partner x) (C'.partner x) (C.partner e))
    (hB : OnDifferentSides e (C.partner e) x (C'.partner e)) : False :=
  RepellingPairs.Dev.Claim13Key.key13B C C' x y s m e K hA hB

end RepellingPairs
end

theorem solution : type_of% @RepellingPairs.chk_claim_13_case_B := @RepellingPairs.chk_claim_13_case_B
