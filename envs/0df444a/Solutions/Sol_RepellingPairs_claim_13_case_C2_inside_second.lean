-- Prove2me | solution 1 for RepellingPairs.claim_13_case_C2_inside_second
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T11:06:29.920133+00:00
-- url     : https://prove2.me/submissions/2cb54ae0-9155-4ceb-926b-faaa2bced6ed

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

end RepellingPairs.Dev.CutCount
end

section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace RepellingPairs.Dev.Claim13Key

open RepellingPairs RepellingPairs.Config RepellingPairs.Dev.CutCount

variable {n : ℕ}

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
set_option maxHeartbeats 8000000 in
theorem key13C2sub2 (C C' : PerfectMatching n) (x y : Fin n) (s m : ℕ) (e u v k : Fin n)
    (K : Ctx13 C C' x y s m e)
    (hA : ¬ InSegment x (C.partner x) (C'.partner x) (C.partner e))
    (hB : ¬ OnDifferentSides e (C.partner e) x (C'.partner e))
    (D : KD C C' e u v k)
    (hk : ¬ OnDifferentSides k (C.partner k) e (C'.partner k))
    (a : Fin n) (ha : CyclicallyOrdered (C.partner k) (C.partner e) a k) :
    (CyclicallyOrdered (C.partner x) x a y ∨ CyclicallyOrdered (C.partner x) y a x) := by
  obtain ⟨hgood, hmin, hdom, hs, hm0, hmn, hx, hc'x, hy, hcx, hend, hxe, hc'xe, hgap, hCe, hC'e⟩ := K
  obtain ⟨huv, huv', hTe, hTce, hTc'e, hk1, hk2, hk3⟩ := D
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
  have hBn := hB
  simp only [CyclicallyOrdered, InSegment, OnDifferentSides, Config.ChordsCross, Fin.lt_def, Fin.ext_iff, ne_eq, iCe] at hAn hBn
  have hk0 : k ≠ e := by
    rintro rfl; exact hTce hk2
  have hk0' : k ≠ C.partner e := by
    rintro rfl; rw [C.involutive] at hk2; exact hTe hk2
  have hk4 := C.ne_self k
  have hk5 := C'.ne_self k
  have hkk := C.involutive k
  have hk6 : C.partner k ≠ C.partner e := fun h => hk0 (C.involutive.injective h)
  have hk7 : C.partner k ≠ e := fun h => hk0' (by rw [← h, C.involutive])
  have hk8 : C'.partner k ≠ C'.partner e := fun h => hk0 (C'.involutive.injective h)
  have hk9 : C'.partner k ≠ e := by
    intro h
    have : C'.partner e = k := by rw [← h, C'.involutive]
    rw [this] at hTc'e; exact hk1 hTc'e
  simp only [oa, ne_eq, Fin.ext_iff, Fin.lt_def] at hk1 hk2 hk3 hk0 hk0' hk4 hk5 hk6 hk7 hk8 hk9 hTe hTce hTc'e huv'
  have hkn : ¬ OnDifferentSides k (C.partner k) e (C'.partner k) := hk
  simp only [CyclicallyOrdered, InSegment, OnDifferentSides, Config.ChordsCross, Fin.lt_def, Fin.ext_iff, ne_eq, iCe] at hkn
  simp only [CyclicallyOrdered, InSegment, OnDifferentSides, Config.ChordsCross, Fin.lt_def, Fin.ext_iff, ne_eq, iCe] at ha ⊢
  clear hmin hdom hgood'; rcases ha with (ha|ha|ha|ha) <;> rcases hgap with ((hgap|hgap|hgap|hgap)|(hgap|hgap|hgap|hgap)) <;> grind (splits := 1000)

end RepellingPairs.Dev.Claim13Key
end

section
set_option autoImplicit false

namespace RepellingPairs

theorem chk_claim_13_case_C2_inside_second {n : ℕ} (C C' : PerfectMatching n) (x y : Fin n) (s m : ℕ) (e u v k : Fin n)
    (K : Claim13Aux.Ctx13 C C' x y s m e)
    (hA : ¬ InSegment x (C.partner x) (C'.partner x) (C.partner e))
    (hB : ¬ OnDifferentSides e (C.partner e) x (C'.partner e))
    (D : Claim13Aux.KD C C' e u v k)
    (hk : ¬ OnDifferentSides k (C.partner k) e (C'.partner k))
    (a : Fin n) (ha : CyclicallyOrdered (C.partner k) (C.partner e) a k) :
    (CyclicallyOrdered (C.partner x) x a y ∨ CyclicallyOrdered (C.partner x) y a x) :=
  RepellingPairs.Dev.Claim13Key.key13C2sub2 C C' x y s m e u v k K hA hB D hk a ha

end RepellingPairs
end

theorem solution : type_of% @RepellingPairs.chk_claim_13_case_C2_inside_second := @RepellingPairs.chk_claim_13_case_C2_inside_second
