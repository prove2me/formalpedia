-- Prove2me | solution 1 for RepellingPairs.claim_13_case_C2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T11:11:48.668497+00:00
-- url     : https://prove2.me/submissions/f9de8e98-ad51-4965-a786-6034a314c24c

import Mathlib
import Definitions.Def_RepellingPairs_Config
import Definitions.Def_RepellingPairs_PerfectMatching
import Definitions.Def_RepellingPairs_IsGoodPair
import Definitions.Def_Claim13Aux
import Theorems.Thm_RepellingPairs_claim_13_case_C2_inside_first
import Theorems.Thm_RepellingPairs_claim_13_case_C2_inside_second
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

namespace RepellingPairs.Dev.Claim13Key

open RepellingPairs RepellingPairs.Config RepellingPairs.Dev.CutCount

variable {n : ℕ}

theorem key13C2sub1 (C C' : PerfectMatching n) (x y : Fin n) (s m : ℕ) (e u v k : Fin n)
    (K : Ctx13 C C' x y s m e)
    (hA : ¬ InSegment x (C.partner x) (C'.partner x) (C.partner e))
    (hB : ¬ OnDifferentSides e (C.partner e) x (C'.partner e))
    (D : KD C C' e u v k)
    (hk : ¬ OnDifferentSides k (C.partner k) e (C'.partner k))
    (a : Fin n) (ha : CyclicallyOrdered (C.partner k) k a (C.partner e)) :
    (CyclicallyOrdered (C.partner x) x a y ∨ CyclicallyOrdered (C.partner x) y a x) :=
  RepellingPairs.claim_13_case_C2_inside_first C C' x y s m e u v k K hA hB D hk a ha

theorem key13C2sub2 (C C' : PerfectMatching n) (x y : Fin n) (s m : ℕ) (e u v k : Fin n)
    (K : Ctx13 C C' x y s m e)
    (hA : ¬ InSegment x (C.partner x) (C'.partner x) (C.partner e))
    (hB : ¬ OnDifferentSides e (C.partner e) x (C'.partner e))
    (D : KD C C' e u v k)
    (hk : ¬ OnDifferentSides k (C.partner k) e (C'.partner k))
    (a : Fin n) (ha : CyclicallyOrdered (C.partner k) (C.partner e) a k) :
    (CyclicallyOrdered (C.partner x) x a y ∨ CyclicallyOrdered (C.partner x) y a x) :=
  RepellingPairs.claim_13_case_C2_inside_second C C' x y s m e u v k K hA hB D hk a ha

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
theorem key13C2cross (C C' : PerfectMatching n) (x y : Fin n) (s m : ℕ) (e u v k : Fin n)
    (K : Ctx13 C C' x y s m e)
    (hA : ¬ InSegment x (C.partner x) (C'.partner x) (C.partner e))
    (hB : ¬ OnDifferentSides e (C.partner e) x (C'.partner e))
    (D : KD C C' e u v k)
    (hk : ¬ OnDifferentSides k (C.partner k) e (C'.partner k)) :
    ChordsCross k (C.partner k) (C.partner e) (C.partner (C.partner e)) := by
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
  simp only [CyclicallyOrdered, InSegment, OnDifferentSides, Config.ChordsCross, Fin.lt_def, Fin.ext_iff, ne_eq, iCe]
  clear hmin hdom hgood'; grind (splits := 1000)

set_option maxHeartbeats 8000000 in
theorem key13C2diff (C C' : PerfectMatching n) (x y : Fin n) (s m : ℕ) (e u v k : Fin n)
    (K : Ctx13 C C' x y s m e)
    (hA : ¬ InSegment x (C.partner x) (C'.partner x) (C.partner e))
    (hB : ¬ OnDifferentSides e (C.partner e) x (C'.partner e))
    (D : KD C C' e u v k)
    (hk : ¬ OnDifferentSides k (C.partner k) e (C'.partner k)) :
    OnDifferentSides k (C.partner k) (C.partner e) (C'.partner k) := by
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
  simp only [CyclicallyOrdered, InSegment, OnDifferentSides, Config.ChordsCross, Fin.lt_def, Fin.ext_iff, ne_eq, iCe]
  clear hmin hdom hgood'; grind (splits := 1000)

set_option maxHeartbeats 8000000 in
theorem key13C2seg (C C' : PerfectMatching n) (x y : Fin n) (s m : ℕ) (e u v k : Fin n)
    (K : Ctx13 C C' x y s m e)
    (hA : ¬ InSegment x (C.partner x) (C'.partner x) (C.partner e))
    (hB : ¬ OnDifferentSides e (C.partner e) x (C'.partner e))
    (D : KD C C' e u v k)
    (hk : ¬ OnDifferentSides k (C.partner k) e (C'.partner k)) :
    InSegment k (C.partner k) (C'.partner k) (C.partner (C.partner e)) ∨ InSegment k (C.partner k) (C'.partner k) (C'.partner (C.partner e)) := by
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
  simp only [CyclicallyOrdered, InSegment, OnDifferentSides, Config.ChordsCross, Fin.lt_def, Fin.ext_iff, ne_eq, iCe]
  clear hmin hdom hgood'; grind (splits := 1000)

set_option maxHeartbeats 8000000 in
theorem key13C2wit (C C' : PerfectMatching n) (x y : Fin n) (s m : ℕ) (e u v k : Fin n)
    (K : Ctx13 C C' x y s m e)
    (hA : ¬ InSegment x (C.partner x) (C'.partner x) (C.partner e))
    (hB : ¬ OnDifferentSides e (C.partner e) x (C'.partner e))
    (D : KD C C' e u v k)
    (hk : ¬ OnDifferentSides k (C.partner k) e (C'.partner k)) :
    ¬ (CyclicallyOrdered (C.partner k) k e (C.partner e) ∨ CyclicallyOrdered (C.partner k) (C.partner e) e k) := by
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
  simp only [CyclicallyOrdered, InSegment, OnDifferentSides, Config.ChordsCross, Fin.lt_def, Fin.ext_iff, ne_eq, iCe]
  clear hmin hdom hgood'; grind (splits := 1000)

theorem key13C2sub (C C' : PerfectMatching n) (x y : Fin n) (s m : ℕ) (e u v k : Fin n)
    (K : Ctx13 C C' x y s m e)
    (hA : ¬ InSegment x (C.partner x) (C'.partner x) (C.partner e))
    (hB : ¬ OnDifferentSides e (C.partner e) x (C'.partner e))
    (D : KD C C' e u v k)
    (hk : ¬ OnDifferentSides k (C.partner k) e (C'.partner k)) :
    ∀ a, (CyclicallyOrdered (C.partner k) k a (C.partner e) ∨ CyclicallyOrdered (C.partner k) (C.partner e) a k) →
      (CyclicallyOrdered (C.partner x) x a y ∨ CyclicallyOrdered (C.partner x) y a x) := by
  intro a ha
  rcases ha with ha | ha
  · exact key13C2sub1 C C' x y s m e u v k K hA hB D hk a ha
  · exact key13C2sub2 C C' x y s m e u v k K hA hB D hk a ha

theorem key13C2 (C C' : PerfectMatching n) (x y : Fin n) (s m : ℕ) (e u v k : Fin n)
    (K : Ctx13 C C' x y s m e)
    (hA : ¬ InSegment x (C.partner x) (C'.partner x) (C.partner e))
    (hB : ¬ OnDifferentSides e (C.partner e) x (C'.partner e))
    (D : KD C C' e u v k)
    (hk : ¬ OnDifferentSides k (C.partner k) e (C'.partner k)) : False := by
  have hg : IsGoodPair C C' k (C.partner e) :=
    ⟨key13C2cross C C' x y s m e u v k K hA hB D hk, key13C2diff C C' x y s m e u v k K hA hB D hk,
      key13C2seg C C' x y s m e u v k K hA hB D hk⟩
  exact hsmall C C' x y K.hmin k (C.partner e) e hg (key13C2sub C C' x y s m e u v k K hA hB D hk) K.hgap
    (key13C2wit C C' x y s m e u v k K hA hB D hk)

end RepellingPairs.Dev.Claim13Key
end

section
set_option autoImplicit false

namespace RepellingPairs

theorem chk_claim_13_case_C2 {n : ℕ} (C C' : PerfectMatching n) (x y : Fin n) (s m : ℕ) (e u v k : Fin n)
    (K : Claim13Aux.Ctx13 C C' x y s m e)
    (hA : ¬ InSegment x (C.partner x) (C'.partner x) (C.partner e))
    (hB : ¬ OnDifferentSides e (C.partner e) x (C'.partner e))
    (D : Claim13Aux.KD C C' e u v k)
    (hk : ¬ OnDifferentSides k (C.partner k) e (C'.partner k)) : False :=
  RepellingPairs.Dev.Claim13Key.key13C2 C C' x y s m e u v k K hA hB D hk

end RepellingPairs
end

theorem solution : type_of% @RepellingPairs.chk_claim_13_case_C2 := @RepellingPairs.chk_claim_13_case_C2
