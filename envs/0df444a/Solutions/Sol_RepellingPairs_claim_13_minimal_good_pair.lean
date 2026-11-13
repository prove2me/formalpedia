-- Prove2me | solution 1 for RepellingPairs.claim_13_minimal_good_pair
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T11:11:49.575811+00:00
-- url     : https://prove2.me/submissions/1f44022d-5ef3-44f7-8ca4-0a0847cb0821

import Mathlib
import Definitions.Def_RepellingPairs_Config
import Definitions.Def_RepellingPairs_PerfectMatching
import Definitions.Def_RepellingPairs_IsGoodPair
import Definitions.Def_Claim13Aux
import Theorems.Thm_RepellingPairs_claim_13_case_C1
import Theorems.Thm_RepellingPairs_claim_13_case_B
import Theorems.Thm_RepellingPairs_claim_13_case_C2

section
set_option autoImplicit false

namespace RepellingPairs.Dev.CutCount

open RepellingPairs RepellingPairs.Config
open Classical

variable {n : ℕ}

export RepellingPairs.Claim13Aux (cr ar oa)

/-- the same count from the outside -/
noncomputable def cr' (C : PerfectMatching n) (S : Fin n → Prop) : ℕ :=
  (Finset.univ.filter fun a => ¬ S a ∧ S (C.partner a)).card

theorem cr'_eq (C : PerfectMatching n) (S : Fin n → Prop) : cr' C S = cr C S := by
  unfold cr' cr
  apply Finset.card_bij (fun a _ => C.partner a)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rw [C.involutive a]; exact ⟨ha.2, ha.1⟩
  · intro a _ b _ h
    exact C.involutive.injective h
  · intro b hb
    refine ⟨C.partner b, ?_, C.involutive b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    rw [C.involutive b]; exact ⟨hb.2, hb.1⟩

theorem sum_cross (C : PerfectMatching n) (S : Fin n → Prop) :
    (∑ x : Fin n, (if (S x ↔ S (C.partner x)) then 0 else 1)) = 2 * cr C S := by
  have h1 : (∑ x : Fin n, (if (S x ↔ S (C.partner x)) then 0 else 1)) =
      (∑ x : Fin n, (if S x ∧ ¬ S (C.partner x) then 1 else 0)) +
      (∑ x : Fin n, (if ¬ S x ∧ S (C.partner x) then 1 else 0)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases h1 : S x <;> by_cases h2 : S (C.partner x) <;> simp [h1, h2]
  rw [h1]
  have h2 : (∑ x : Fin n, (if S x ∧ ¬ S (C.partner x) then 1 else 0)) = cr C S := by
    unfold cr; rw [Finset.sum_boole]; simp
  have h3 : (∑ x : Fin n, (if ¬ S x ∧ S (C.partner x) then 1 else 0)) = cr' C S := by
    unfold cr'; rw [Finset.sum_boole]; simp
  rw [h2, h3, cr'_eq]; ring

theorem dist_eq_cr (C : PerfectMatching n) (i j : Fin n) :
    Config.dist C.config i j = cr C (fun a => onSide i j a = true) := by
  have key : 2 * Config.dist C.config i j =
      ∑ x : Fin n, (if (onSide i j x = true ↔ onSide i j (C.partner x) = true) then 0 else 1) := by
    unfold Config.dist PerfectMatching.config
    set g : Fin n → Sym2 (Fin n) := fun x => s(x, C.partner x) with hg
    have hs : ((Finset.univ.image g).val.map (chordCross i j)).sum =
        ∑ c ∈ Finset.univ.image g, chordCross i j c := rfl
    rw [hs]
    have hfib := Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Fin n)))
      (t := Finset.univ.image g) (g := g)
      (fun x _ => Finset.mem_image_of_mem g (Finset.mem_univ x)) (fun x => chordCross i j (g x))
    have hF : ∀ c ∈ Finset.univ.image g,
        (∑ x ∈ Finset.univ.filter (fun x => g x = c), chordCross i j (g x)) = 2 * chordCross i j c := by
      intro c hc
      obtain ⟨x0, _, rfl⟩ := Finset.mem_image.1 hc
      have hfil : Finset.univ.filter (fun x => g x = g x0) = {x0, C.partner x0} := by
        ext x
        simp only [hg, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, Sym2.eq_iff]
        constructor
        · rintro (⟨h, _⟩ | ⟨h, _⟩)
          · exact Or.inl h
          · exact Or.inr h
        · rintro (h | h)
          · exact Or.inl ⟨h, by rw [h]⟩
          · exact Or.inr ⟨h, by rw [h, C.involutive x0]⟩
      rw [hfil, Finset.sum_pair (Ne.symm (C.ne_self x0))]
      have : g (C.partner x0) = g x0 := by
        simp only [hg, C.involutive x0, Sym2.eq_swap]
      rw [this]; ring
    have h2 : ∑ c ∈ Finset.univ.image g, 2 * chordCross i j c = ∑ x : Fin n, chordCross i j (g x) :=
      (Finset.sum_congr rfl hF).symm.trans hfib
    rw [Finset.mul_sum, h2]
    apply Finset.sum_congr rfl
    intro x _
    simp only [hg, chordCross, Sym2.lift_mk]
    by_cases h1 : onSide i j x = true <;> by_cases h2 : onSide i j (C.partner x) = true <;>
      simp_all
  have h0 := sum_cross C (fun a => onSide i j a = true)
  have h : 2 * Config.dist C.config i j = 2 * cr C (fun a => onSide i j a = true) := by
    rw [key, ← h0]
    apply Finset.sum_congr rfl
    intro x _
    congr
  omega

theorem cr_eq_sum (C : PerfectMatching n) (S : Fin n → Prop) :
    cr C S = ∑ a : Fin n, (if S a ∧ ¬ S (C.partner a) then 1 else 0) := by
  unfold cr; rw [Finset.sum_boole]; simp

/-- adding one point `e` to a set changes the count by `±1` -/
theorem add_point (C : PerfectMatching n) (S S' : Fin n → Prop) (e : Fin n)
    (hS : ∀ a, S a ↔ S' a ∨ a = e) (he : ¬ S' e) :
    cr C S + (if S' (C.partner e) then 1 else 0) = cr C S' + (if S' (C.partner e) then 0 else 1) := by
  have hne : C.partner e ≠ e := C.ne_self e
  have hee' : C.partner (C.partner e) = e := C.involutive e
  have hSe : S e := (hS e).2 (Or.inr rfl)
  have hSe' : S (C.partner e) ↔ S' (C.partner e) := by rw [hS (C.partner e)]; simp [hne]
  generalize he' : C.partner e = e' at hne hee' hSe' ⊢
  rw [cr_eq_sum, cr_eq_sum]
  have split : ∀ f : Fin n → ℕ, ∑ a : Fin n, f a =
      f e + f e' + ∑ a ∈ (Finset.univ.erase e).erase e', f a := by
    intro f
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ e), ← Finset.add_sum_erase _ _
      (Finset.mem_erase.2 ⟨hne, Finset.mem_univ e'⟩)]
    ring
  rw [split, split (fun a => if S' a ∧ ¬ S' (C.partner a) then 1 else 0)]
  have hrest : ∑ a ∈ (Finset.univ.erase e).erase e', (if S a ∧ ¬ S (C.partner a) then 1 else 0) =
      ∑ a ∈ (Finset.univ.erase e).erase e', (if S' a ∧ ¬ S' (C.partner a) then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro a ha
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at ha
    have h1 : S a ↔ S' a := by rw [hS a]; simp [ha.2]
    have h2 : S (C.partner a) ↔ S' (C.partner a) := by
      rw [hS (C.partner a)]
      have : C.partner a ≠ e := by
        intro h; apply ha.1; rw [← he', ← h, C.involutive a]
      simp [this]
    simp only [h1, h2]
  rw [hrest]
  simp only [he', hee', hSe, he, hSe', not_true_eq_false, false_and, if_false, and_false, true_and]
  by_cases h : S' e' <;> simp [h] <;> omega

/-- strict inequality from an injection with a missing point (outside form) -/
theorem cr_lt (C C' : PerfectMatching n) (S : Fin n → Prop)
    (h : ∀ a, ¬ S a → S (C.partner a) → S (C'.partner a))
    (e : Fin n) (he : ¬ S e) (he1 : S (C'.partner e)) (he2 : ¬ S (C.partner e)) :
    cr C S < cr C' S := by
  rw [← cr'_eq, ← cr'_eq]
  unfold cr'
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨e, by simp [he, he1], by simp [he, he2]⟩
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ⟨ha.1, h a ha.1 ha.2⟩

theorem onSide_iff (i j a : Fin n) : onSide i j a = true ↔
    (i.val ≤ j.val ∧ i.val < a.val ∧ a.val ≤ j.val) ∨
      (j.val < i.val ∧ (i.val < a.val ∨ a.val ≤ j.val)) := by
  unfold onSide
  split_ifs with h <;> simp only [decide_eq_true_eq, Fin.le_def, Fin.lt_def] at h ⊢ <;> omega

theorem cr_congr (C : PerfectMatching n) (S T : Fin n → Prop) (h : ∀ a, S a ↔ T a) :
    cr C S = cr C T := by
  have : S = T := funext fun a => propext (h a)
  rw [this]

theorem dom_arc (C C' : PerfectMatching n) (h : Config.Dominates C.config C'.config)
    (S : Fin n → Prop) (s m : ℕ) (hs : s ≤ n) (hm : m < n)
    (hS : ∀ a, S a ↔ ar n s m a) : cr C' S ≤ cr C S := by
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · have h0 : ∀ D : PerfectMatching n, cr D S = 0 := by
      intro D
      unfold cr
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro a _ ha
      have := (hS a).1 ha.1
      unfold ar at this; omega
    rw [h0, h0]
  · have hn : 0 < n := by omega
    let i : Fin n := ⟨if s = 0 then n - 1 else s - 1, by split_ifs <;> omega⟩
    let j : Fin n := ⟨if s + m - 1 < n then s + m - 1 else s + m - 1 - n, by split_ifs <;> omega⟩
    have hij : ∀ a, S a ↔ (fun a => onSide i j a = true) a := by
      intro a
      show _ ↔ onSide i j a = true
      rw [onSide_iff, hS a]
      unfold ar
      simp only [i, j]
      split_ifs <;> omega
    rw [cr_congr C S _ hij, cr_congr C' S _ hij, ← dist_eq_cr, ← dist_eq_cr]
    exact h i j

theorem oa_ar (u v : Fin n) (huv : u ≠ v) :
    ∃ s m : ℕ, s ≤ n ∧ m < n ∧ ∀ a, oa u v a ↔ ar n s m a := by
  refine ⟨u.val + 1, if u.val < v.val then v.val - u.val - 1 else v.val + n - u.val - 1, by omega, ?_, ?_⟩
  · have := u.2; have := v.2
    have : u.val ≠ v.val := fun h => huv (Fin.ext h)
    split_ifs <;> omega
  · intro a
    have : u.val ≠ v.val := fun h => huv (Fin.ext h)
    have := a.2
    unfold oa ar
    split_ifs <;> omega

theorem cr_compl (C : PerfectMatching n) (S : Fin n → Prop) :
    cr C (fun a => ¬ S a) = cr C S := by
  rw [← cr'_eq C S]
  unfold cr cr'
  simp only [not_not]

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

theorem onSide_ar (i j : Fin n) :
    ∃ s m : ℕ, s ≤ n ∧ m < n ∧ (∀ a, (onSide i j a = true) ↔ ar n s m a) ∧
      (m = 0 → ∀ a, ¬ (onSide i j a = true)) := by
  refine ⟨i.val + 1, if i.val < j.val then j.val - i.val else if j.val < i.val then j.val + n - i.val else 0,
    by omega, ?_, ?_, ?_⟩
  · have := i.2; have := j.2
    split_ifs <;> omega
  · intro a
    have := a.2
    rw [onSide_iff]
    unfold ar
    split_ifs <;> omega
  · intro hm a
    have := a.2
    rw [onSide_iff]
    split_ifs at hm <;> omega

end RepellingPairs.Dev.CutCount
end

section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace RepellingPairs.Dev.Claim13Key

open RepellingPairs RepellingPairs.Config RepellingPairs.Dev.CutCount

variable {n : ℕ}

theorem exists_k (C C' : PerfectMatching n)
    (hdom : ∀ s m, s ≤ n → m < n → cr C' (ar n s m) ≤ cr C (ar n s m))
    (u v e : Fin n) (huv : u ≠ v)
    (he : ¬ oa u v e) (hce : ¬ oa u v (C.partner e)) (hc'e : oa u v (C'.partner e)) :
    ∃ k, ¬ oa u v k ∧ oa u v (C.partner k) ∧ ¬ oa u v (C'.partner k) := by
  by_contra hno
  push_neg at hno
  obtain ⟨s, m, hs, hm, hS⟩ := oa_ar u v huv
  have hle := hdom s m hs hm
  have h1 : cr C' (oa u v) ≤ cr C (oa u v) := by
    rw [cr_congr C' (oa u v) _ hS, cr_congr C (oa u v) _ hS]; exact hle
  have h2 := cr_lt C C' (oa u v) (fun a ha hCa => hno a ha hCa) e he hc'e hce
  omega

theorem oa_flip (e ce c : Fin n) (h1 : ce ≠ e) (h2 : c ≠ e) (h3 : c ≠ ce) (h : ¬ oa e ce c) :
    oa ce e c := by
  simp only [oa, Fin.lt_def, ne_eq, Fin.ext_iff] at *
  omega

theorem oa_ends (u v : Fin n) : ¬ oa u v u ∧ ¬ oa u v v := by
  simp only [oa, Fin.lt_def]
  omega

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

theorem key13C1 (C C' : PerfectMatching n) (x y : Fin n) (s m : ℕ) (e u v k : Fin n)
    (K : Ctx13 C C' x y s m e)
    (hA : ¬ InSegment x (C.partner x) (C'.partner x) (C.partner e))
    (hB : ¬ OnDifferentSides e (C.partner e) x (C'.partner e))
    (D : KD C C' e u v k)
    (hk : OnDifferentSides k (C.partner k) e (C'.partner k)) : False :=
  RepellingPairs.claim_13_case_C1 C C' x y s m e u v k K hA hB D hk

theorem key13B (C C' : PerfectMatching n) (x y : Fin n) (s m : ℕ) (e : Fin n)
    (K : Ctx13 C C' x y s m e)
    (hA : ¬ InSegment x (C.partner x) (C'.partner x) (C.partner e))
    (hB : OnDifferentSides e (C.partner e) x (C'.partner e)) : False :=
  RepellingPairs.claim_13_case_B C C' x y s m e K hA hB

theorem key13C2 (C C' : PerfectMatching n) (x y : Fin n) (s m : ℕ) (e u v k : Fin n)
    (K : Ctx13 C C' x y s m e)
    (hA : ¬ InSegment x (C.partner x) (C'.partner x) (C.partner e))
    (hB : ¬ OnDifferentSides e (C.partner e) x (C'.partner e))
    (D : KD C C' e u v k)
    (hk : ¬ OnDifferentSides k (C.partner k) e (C'.partner k)) : False :=
  RepellingPairs.claim_13_case_C2 C C' x y s m e u v k K hA hB D hk

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
theorem key13A (C C' : PerfectMatching n) (x y : Fin n) (s m : ℕ) (e : Fin n)
    (K : Ctx13 C C' x y s m e)
    (hA : InSegment x (C.partner x) (C'.partner x) (C.partner e)) : False := by
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
  have hg : IsGoodPair C C' x e := by
    refine ⟨?_, ?_, Or.inl hA⟩
    · simp only [CyclicallyOrdered, InSegment, OnDifferentSides, Config.ChordsCross, Fin.lt_def, Fin.ext_iff, ne_eq, iCe]
      clear hmin hdom hgood'; grind (splits := 1000)
    · simp only [CyclicallyOrdered, InSegment, OnDifferentSides, Config.ChordsCross, Fin.lt_def, Fin.ext_iff, ne_eq, iCe]
      clear hmin hdom hgood'; grind (splits := 1000)
  refine hsmall C C' x y hmin x e e hg ?_ hgap0 ?_
  · intro a ha
    simp only [CyclicallyOrdered, InSegment, OnDifferentSides, Config.ChordsCross, Fin.lt_def, Fin.ext_iff, ne_eq, iCe] at ha ⊢
    clear hmin hdom hgood'; grind (splits := 1000)
  · simp only [CyclicallyOrdered, InSegment, OnDifferentSides, Config.ChordsCross, Fin.lt_def, Fin.ext_iff, ne_eq, iCe]
    clear hmin hdom hgood'; grind (splits := 1000)

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
theorem key13C (C C' : PerfectMatching n) (x y : Fin n) (s m : ℕ) (e : Fin n)
    (K : Ctx13 C C' x y s m e)
    (hA : ¬ InSegment x (C.partner x) (C'.partner x) (C.partner e))
    (hB : ¬ OnDifferentSides e (C.partner e) x (C'.partner e)) : False := by
  have hdom := K.hdom
  have hCe := K.hCe
  have hC'e := K.hC'e
  have h5c := C.ne_self e
  have h6' := C'.ne_self e
  have hcc : C'.partner e ≠ C.partner e := fun h => hC'e (h ▸ hCe)
  obtain ⟨u, v, huv, huv', hTe, hTce, hTc'e⟩ : ∃ u v : Fin n, u ≠ v ∧
      ((u = e ∧ v = C.partner e) ∨ (u = C.partner e ∧ v = e)) ∧ ¬ oa u v e ∧
      ¬ oa u v (C.partner e) ∧ oa u v (C'.partner e) := by
    by_cases hh : oa e (C.partner e) (C'.partner e)
    · exact ⟨e, C.partner e, fun h => h5c h.symm, Or.inl ⟨rfl, rfl⟩, (oa_ends _ _).1,
        (oa_ends _ _).2, hh⟩
    · exact ⟨C.partner e, e, h5c, Or.inr ⟨rfl, rfl⟩, (oa_ends _ _).2, (oa_ends _ _).1,
        oa_flip e (C.partner e) (C'.partner e) h5c h6' hcc hh⟩
  obtain ⟨k, hk1, hk2, hk3⟩ := exists_k C C' hdom u v e huv hTe hTce hTc'e
  have hk0 : k ≠ e := by
    rintro rfl; exact hTce hk2
  have hk0' : k ≠ C.partner e := by
    rintro rfl; rw [C.involutive] at hk2; exact hTe hk2
  have D : KD C C' e u v k := ⟨huv, huv', hTe, hTce, hTc'e, hk1, hk2, hk3⟩
  by_cases hk : OnDifferentSides k (C.partner k) e (C'.partner k)
  · exact key13C1 C C' x y s m e u v k K hA hB D hk
  · exact key13C2 C C' x y s m e u v k K hA hB D hk

end RepellingPairs.Dev.Claim13Key
end

section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace RepellingPairs.Dev.Claim13Key

open RepellingPairs RepellingPairs.Config RepellingPairs.Dev.CutCount

variable {n : ℕ}

theorem key13 (C C' : PerfectMatching n) (x y : Fin n) (s m : ℕ) (e : Fin n)
    (K : Ctx13 C C' x y s m e) : False := by
  by_cases hA : InSegment x (C.partner x) (C'.partner x) (C.partner e)
  · exact key13A C C' x y s m e K hA
  by_cases hB : OnDifferentSides e (C.partner e) x (C'.partner e)
  · exact key13B C C' x y s m e K hA hB
  exact key13C C C' x y s m e K hA hB

end RepellingPairs.Dev.Claim13Key
end

section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace RepellingPairs.Dev.Claim13Key

open RepellingPairs RepellingPairs.Config RepellingPairs.Dev.CutCount

variable {n : ℕ}

theorem ar_norm (s m : ℕ) (hs : s ≤ n) (hn : 0 < n) :
    ∃ s' : ℕ, s' < n ∧ ∀ a, ar n s m a ↔ ar n s' m a := by
  by_cases h : s < n
  · exact ⟨s, h, fun a => Iff.rfl⟩
  · refine ⟨0, hn, fun a => ?_⟩
    have := a.2
    unfold ar; omega

theorem end_split (s m : ℕ) (hs : s < n) (hm0 : 0 < m) (hmn : m < n) (e : Fin n)
    (hend : e.val = s ∨ e.val = s + m - 1 ∨ e.val + n = s + m - 1) :
    ∃ s' : ℕ, s' < n ∧ (∀ a, ar n s m a ↔ ar n s' (m - 1) a ∨ a = e) ∧ ¬ ar n s' (m - 1) e := by
  have he := e.2
  by_cases h : e.val = s
  · refine ⟨if s + 1 < n then s + 1 else 0, by split_ifs <;> omega, ?_, ?_⟩
    · intro a
      have := a.2
      simp only [Fin.ext_iff]
      unfold ar
      split_ifs <;> omega
    · unfold ar
      split_ifs <;> omega
  · refine ⟨s, hs, ?_, ?_⟩
    · intro a
      have := a.2
      simp only [Fin.ext_iff]
      unfold ar
      omega
    · unfold ar
      omega

theorem end_gap (s m : ℕ) (x y cx c'x : Fin n) (hs : s < n) (hm0 : 0 < m) (hmn : m < n)
    (hx : ar n s m x) (hc'x : ar n s m c'x) (hy : ¬ ar n s m y) (hcx : ¬ ar n s m cx)
    (hdf : OnDifferentSides x cx y c'x)
    (hxend : ¬ (x.val = s ∨ x.val = s + m - 1 ∨ x.val + n = s + m - 1)) :
    ∃ e : Fin n, (e.val = s ∨ e.val = s + m - 1 ∨ e.val + n = s + m - 1) ∧ e ≠ x ∧ e ≠ c'x ∧
      (CyclicallyOrdered cx x e y ∨ CyclicallyOrdered cx y e x) := by
  let s0 : Fin n := ⟨s, hs⟩
  let t : Fin n := ⟨if s + m - 1 < n then s + m - 1 else s + m - 1 - n, by split_ifs <;> omega⟩
  by_cases hc : (CyclicallyOrdered cx x s0 y ∨ CyclicallyOrdered cx y s0 x) ∧ s0 ≠ x ∧ s0 ≠ c'x
  · exact ⟨s0, Or.inl rfl, hc.2.1, hc.2.2, hc.1⟩
  · refine ⟨t, ?_, ?_, ?_, ?_⟩
    · simp only [t]; split_ifs <;> omega
    all_goals
      simp only [t, s0, ar, CyclicallyOrdered, OnDifferentSides, Fin.lt_def, Fin.ext_iff, ne_eq] at *
      grind (splits := 1000)

theorem core13 (C C' : PerfectMatching n) (x y : Fin n)
    (hgood : IsGoodPair C C' x y)
    (hmin : ∀ x₂ y₂, IsGoodPair C C' x₂ y₂ → segmentCount C x y ≤ segmentCount C x₂ y₂)
    (hdom : ∀ s m, s ≤ n → m < n → cr C' (ar n s m) ≤ cr C (ar n s m)) :
    ∀ m s : ℕ, s < n → 0 < m → m < n → ar n s m x → ar n s m (C'.partner x) →
      ¬ ar n s m y → ¬ ar n s m (C.partner x) → cr C' (ar n s m) + 2 ≤ cr C (ar n s m) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro s hs hm0 hmn hx hc'x hy hcx
  by_cases hxend : x.val = s ∨ x.val = s + m - 1 ∨ x.val + n = s + m - 1
  · -- base case: `x` is an end of the arc
    obtain ⟨s', hs', hS, hnx⟩ := end_split s m hs hm0 hmn x hxend
    have hCx' : ¬ ar n s' (m - 1) (C.partner x) := fun h => hcx ((hS _).2 (Or.inl h))
    have hC'x' : ar n s' (m - 1) (C'.partner x) := by
      rcases (hS _).1 hc'x with h | h
      · exact h
      · exact absurd h (C'.ne_self x)
    have h1 := add_point C (ar n s m) (ar n s' (m - 1)) x hS hnx
    have h2 := add_point C' (ar n s m) (ar n s' (m - 1)) x hS hnx
    have h3 := hdom s' (m - 1) hs'.le (by omega)
    simp only [hCx', hC'x', if_true, if_false] at h1 h2
    omega
  · obtain ⟨e, hend, hxe, hc'xe, hgap⟩ :=
      end_gap s m x y (C.partner x) (C'.partner x) hs hm0 hmn hx hc'x hy hcx hgood.2.1 hxend
    obtain ⟨s', hs', hS, hne⟩ := end_split s m hs hm0 hmn e hend
    have hxS' : ar n s' (m - 1) x := by
      rcases (hS x).1 hx with h | h
      · exact h
      · exact absurd h.symm hxe
    have hc'xS' : ar n s' (m - 1) (C'.partner x) := by
      rcases (hS _).1 hc'x with h | h
      · exact h
      · exact absurd h.symm hc'xe
    have hyS' : ¬ ar n s' (m - 1) y := fun h => hy ((hS y).2 (Or.inl h))
    have hcxS' : ¬ ar n s' (m - 1) (C.partner x) := fun h => hcx ((hS _).2 (Or.inl h))
    have hm1 : 0 < m - 1 := by
      have := hxS'
      unfold ar at this; omega
    have ih' := ih (m - 1) (by omega) s' hs' hm1 (by omega) hxS' hc'xS' hyS' hcxS'
    have key : ∀ _ : ar n s m (C.partner e), ar n s m (C'.partner e) := by
      intro hCe
      by_contra hC'e
      exact key13 C C' x y s m e ⟨hgood, hmin, hdom, hs, hm0, hmn, hx, hc'x, hy, hcx, hend, hxe,
        hc'xe, hgap, hCe, hC'e⟩
    have a1 : ar n s' (m - 1) (C.partner e) → ar n s' (m - 1) (C'.partner e) := by
      intro h
      have := key ((hS _).2 (Or.inl h))
      rcases (hS _).1 this with h' | h'
      · exact h'
      · exact absurd h' (C'.ne_self e)
    have h1 := add_point C (ar n s m) (ar n s' (m - 1)) e hS hne
    have h2 := add_point C' (ar n s m) (ar n s' (m - 1)) e hS hne
    by_cases h5 : ar n s' (m - 1) (C.partner e) <;> by_cases h6 : ar n s' (m - 1) (C'.partner e) <;>
      simp only [h5, h6, if_true, if_false] at h1 h2 <;> first | omega | exact absurd (a1 h5) h6

end RepellingPairs.Dev.Claim13Key
end

section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace RepellingPairs.Dev.Claim13

open RepellingPairs RepellingPairs.Config RepellingPairs.Dev.CutCount RepellingPairs.Dev.Claim13Key

variable {n : ℕ}

theorem finish (C C' : PerfectMatching n) (x y : Fin n)
    (hgood : IsGoodPair C C' x y)
    (hmin : ∀ x₂ y₂, IsGoodPair C C' x₂ y₂ → segmentCount C x y ≤ segmentCount C x₂ y₂)
    (hdom : ∀ s m, s ≤ n → m < n → cr C' (ar n s m) ≤ cr C (ar n s m))
    (R : Fin n → Prop) (hR : ∃ s m, s ≤ n ∧ m < n ∧ ∀ a, R a ↔ ar n s m a)
    (hx : R x) (hc'x : R (C'.partner x)) (hy : ¬ R y) (hcx : ¬ R (C.partner x)) :
    cr C' R + 2 ≤ cr C R := by
  obtain ⟨s, m, hs, hm, hRar⟩ := hR
  have hn : 0 < n := Fin.pos x
  obtain ⟨s2, hs2, hn2⟩ := ar_norm s m hs hn
  have hm0 : 0 < m := by
    have := (hRar x).1 hx
    unfold ar at this; omega
  have key := core13 C C' x y hgood hmin hdom m s2 hs2 hm0 hm ((hn2 x).1 ((hRar x).1 hx))
    ((hn2 _).1 ((hRar _).1 hc'x)) (fun h => hy ((hRar y).2 ((hn2 y).2 h)))
    (fun h => hcx ((hRar _).2 ((hn2 _).2 h)))
  rw [cr_congr C R (ar n s2 m) (fun a => (hRar a).trans (hn2 a)),
    cr_congr C' R (ar n s2 m) (fun a => (hRar a).trans (hn2 a))]
  exact key

end RepellingPairs.Dev.Claim13

namespace RepellingPairs

open RepellingPairs.Dev.Claim13 RepellingPairs.Dev.CutCount RepellingPairs.Config

theorem chk_claim_13_minimal_good_pair {n : ℕ} (C C' : PerfectMatching n)
    (h : Config.StrictlyDominates C.config C'.config) (x y : Fin n)
    (hgood : IsGoodPair C C' x y)
    (hmin : ∀ x₂ y₂, IsGoodPair C C' x₂ y₂ → segmentCount C x y ≤ segmentCount C x₂ y₂)
    (i j : Fin n) (hi : BarBetween x y (C.partner x) i)
    (hj : BarBetween (C.partner x) (C'.partner x) x j) :
    Config.dist C'.config i j + 2 ≤ Config.dist C.config i j := by
  obtain ⟨hdomC, _⟩ := h
  have hdom : ∀ s m, s ≤ n → m < n → cr C' (ar n s m) ≤ cr C (ar n s m) :=
    fun s m hs hm => dom_arc C C' hdomC (ar n s m) s m hs hm (fun a => Iff.rfl)
  rw [dist_eq_cr, dist_eq_cr]
  have hdf := hgood.2.1
  have hmem : (onSide i j x = true ∧ onSide i j (C'.partner x) = true ∧ ¬ onSide i j y = true ∧
        ¬ onSide i j (C.partner x) = true) ∨
      (¬ onSide i j x = true ∧ ¬ onSide i j (C'.partner x) = true ∧ onSide i j y = true ∧
        onSide i j (C.partner x) = true) := by
    have hi' := hi
    have hj' := hj
    simp only [BarBetween, BarOnClockwiseSegment, ← Bool.not_eq_true, onSide_iff, Fin.le_def,
      Fin.lt_def] at hi' hj' ⊢
    simp only [OnDifferentSides, CyclicallyOrdered, Fin.lt_def] at hdf
    grind (splits := 1000)
  rcases hmem with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · obtain ⟨s, m, hs, hm, hSar, _⟩ := onSide_ar i j
    exact finish C C' x y hgood hmin hdom (fun a => onSide i j a = true) ⟨s, m, hs, hm, hSar⟩
      h1 h2 h3 h4
  · have hij : i ≠ j := by
      rintro rfl
      simp only [onSide_iff] at h3
      omega
    have hcomp : ∀ a, (¬ onSide i j a = true) ↔ onSide j i a = true := by
      intro a
      simp only [onSide_iff]
      have : i.val ≠ j.val := fun h => hij (Fin.ext h)
      omega
    obtain ⟨s, m, hs, hm, hTar, _⟩ := onSide_ar j i
    have := finish C C' x y hgood hmin hdom (fun a => ¬ onSide i j a = true)
      ⟨s, m, hs, hm, fun a => (hcomp a).trans (hTar a)⟩ h1 h2 (not_not.2 h3) (not_not.2 h4)
    rw [cr_compl C' (fun a => onSide i j a = true), cr_compl C (fun a => onSide i j a = true)] at this
    exact this

end RepellingPairs
end

theorem solution : type_of% @RepellingPairs.chk_claim_13_minimal_good_pair := @RepellingPairs.chk_claim_13_minimal_good_pair
