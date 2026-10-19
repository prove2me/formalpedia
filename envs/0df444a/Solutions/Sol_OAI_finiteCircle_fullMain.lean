-- Prove2me | solution 1 for OAI.finiteCircle_fullMain
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T17:09:29.392208+00:00
-- url     : https://prove2.me/submissions/8e1bcddb-b856-42a9-874f-1198765afba6

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Main.lean:L139-L139
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.finiteCircle_fullMain.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_finiteCircle_fullMain) verbatim and is proved by it.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Fourier
import Definitions.Def_OAI_Combinatorics_FiniteCircle_DyadicShifts
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TreeBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Translations
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Distortion
import Definitions.Def_OAI_Combinatorics_FiniteCircle_BlockMatching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_OffsetRecovery
import Definitions.Def_OAI_Combinatorics_FiniteCircle_RandomCodes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Codes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Lower
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Windows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Partitions
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Histograms
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Separation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Main
import Theorems.Thm_OAI_FiniteCircle_StandingPrimes_excluded_alphabet_bound
import Theorems.Thm_OAI_FiniteCircle_StandingPrimes_mask_alphabet_bound
import Theorems.Thm_OAI_FiniteCircle_StandingPrimes_mask_alphabet_ge
import Theorems.Thm_OAI_FiniteCircle_StrongLocal_offsetLocal
import Theorems.Thm_OAI_FiniteCircle_all_length_inversion
import Theorems.Thm_OAI_FiniteCircle_anchor_deficit_lower
import Theorems.Thm_OAI_FiniteCircle_distortion_upper
import Theorems.Thm_OAI_FiniteCircle_excluded_binary_distortion
import Theorems.Thm_OAI_FiniteCircle_exists_power_parameters
import Theorems.Thm_OAI_FiniteCircle_exists_strongLocal
import Theorems.Thm_OAI_FiniteCircle_histogram_embedding_step
import Theorems.Thm_OAI_FiniteCircle_mask_binary_distortion
import Theorems.Thm_OAI_FiniteCircle_offset_deficit_lower
import Theorems.Thm_OAI_FiniteCircle_primeInterval_card_cubic
import Theorems.Thm_OAI_FiniteCircle_recursive_length_bound

-- ---- from OAI.Combinatorics.FiniteCircle.Edit ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

namespace EditStep
variable {α β : Type*} {x y : List α}

theorem append_left (h : EditStep x y) (u : List α) : EditStep (u ++ x) (u ++ y) := by
  cases h with
  | insert p q a => simpa only [List.append_assoc] using EditStep.insert (u ++ p) q a
  | delete p q a => simpa only [List.append_assoc] using EditStep.delete (u ++ p) q a
  | substitute p q a b =>
    simpa only [List.append_assoc] using EditStep.substitute (u ++ p) q a b

theorem append_right (h : EditStep x y) (v : List α) : EditStep (x ++ v) (y ++ v) := by
  cases h with
  | insert p q a => simpa only [List.append_assoc, List.cons_append] using EditStep.insert p (q ++ v) a
  | delete p q a => simpa only [List.append_assoc, List.cons_append] using EditStep.delete p (q ++ v) a
  | substitute p q a b =>
    simpa only [List.append_assoc, List.cons_append] using EditStep.substitute p (q ++ v) a b

theorem map (h : EditStep x y) (f : α → β) : EditStep (x.map f) (y.map f) := by
  cases h with
  | insert u v a => simpa using EditStep.insert (u.map f) (v.map f) (f a)
  | delete u v a => simpa using EditStep.delete (u.map f) (v.map f) (f a)
  | substitute u v a b => simpa using EditStep.substitute (u.map f) (v.map f) (f a) (f b)
end EditStep

namespace EditScript
variable {α β : Type*} {n m : ℕ} {x y z : List α}

theorem append_left (h : EditScript n x y) (u : List α) : EditScript n (u ++ x) (u ++ y) := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (h.append_left u) ih

theorem append_right (h : EditScript n x y) (v : List α) : EditScript n (x ++ v) (y ++ v) := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (h.append_right v) ih

theorem map (h : EditScript n x y) (f : α → β) : EditScript n (x.map f) (y.map f) := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (h.map f) ih

theorem of_sublist {z x : List α} (h : z <+ x) : EditScript (x.length - z.length) x z := by
  induction h with
  | slnil => exact .nil []
  | @cons l₁ l₂ a h ih =>
    have hl := h.length_le
    simpa only [List.nil_append, List.length_cons, show l₂.length + 1 - l₁.length = l₂.length - l₁.length + 1 by omega]
      using EditScript.cons (EditStep.delete [] l₂ a) ih
  | cons_cons a h ih =>
    simpa using ih.append_left [a]

theorem of_length_eq {x y : List α} (h : x.length = y.length) : EditScript x.length x y := by
  induction x generalizing y with
  | nil =>
    have : y = [] := List.length_eq_zero_iff.mp h.symm
    subst y
    exact .nil []
  | cons a x ih =>
    cases y with
    | nil => simp at h
    | cons b y =>
      have ht : x.length = y.length := by simpa using h
      exact .cons (.substitute [] x a b) ((ih ht).append_left [b])
end EditScript

theorem editDistance_map_le {α β : Type*} (f : α → β) (x y : List α) :
    editDistance (x.map f) (y.map f) ≤ editDistance x y :=
  editDistance_le_of_script ((editDistance_spec x y).map f)

theorem editDistance_map_eq {α β : Type*} (f : α → β) (g : β → α) (hg : Function.LeftInverse g f)
    (x y : List α) : editDistance (x.map f) (y.map f) = editDistance x y := by
  apply Nat.le_antisymm (editDistance_map_le f x y)
  have hgf : ∀ a, g (f a) = a := hg
  simpa [List.map_map, Function.comp_def, hgf] using
    editDistance_map_le g (x.map f) (y.map f)

theorem EditStep.encode_script {α : Type*} {w : ℕ} (c : α → Fin w → Bool) {x y : List α}
    (h : EditStep x y) : EditScript w (encode c x) (encode c y) := by
  cases h with
  | insert u v a =>
    simpa only [encode_append, encode_cons, List.length_ofFn, List.nil_append, List.append_assoc] using
      ((EditScript.insertAll (List.ofFn (c a))).append_right (encode c v)).append_left (encode c u)
  | delete u v a =>
    simpa only [encode_append, encode_cons, List.length_ofFn, List.nil_append, List.append_assoc] using
      ((EditScript.deleteAll (List.ofFn (c a))).append_right (encode c v)).append_left (encode c u)
  | substitute u v a b =>
    simpa only [encode_append, encode_cons, List.length_ofFn, List.append_assoc] using
      ((EditScript.of_length_eq (x := List.ofFn (c a)) (y := List.ofFn (c b)) (by simp)).append_right
        (encode c v)).append_left (encode c u)

theorem EditScript.encode_script {α : Type*} {w n : ℕ} (c : α → Fin w → Bool) {x y : List α}
    (h : EditScript n x y) : EditScript (w * n) (encode c x) (encode c y) := by
  induction h with
  | nil => simp only [Nat.mul_zero]; exact .nil _
  | @cons n x y z h _ ih =>
    simpa only [Nat.mul_add, Nat.mul_one, Nat.add_comm] using (h.encode_script c).trans ih

theorem editDistance_encode_le {α : Type*} {w : ℕ} (c : α → Fin w → Bool) (x y : List α) :
    editDistance (encode c x) (encode c y) ≤ w * editDistance x y :=
  editDistance_le_of_script ((editDistance_spec x y).encode_script c)

theorem lcs_encode_ge {α : Type*} {w : ℕ} (c : α → Fin w → Bool) (x y : List α) :
    w * lcs x y ≤ lcs (encode c x) (encode c y) := by
  obtain ⟨z, hx, hy, hz⟩ := lcs_exists x y
  rw [← hz]
  have he :=
    le_lcs (hx.flatMap (fun a => List.ofFn (c a))) (hy.flatMap (fun a => List.ofFn (c a)))
  change (encode c z).length ≤ lcs (encode c x) (encode c y) at he
  simpa only [length_encode] using he

theorem deficit_encode_le {α : Type*} {w : ℕ} (c : α → Fin w → Bool) (x y : List α) :
    deficit (encode c x) (encode c y) ≤ w * deficit x y := by
  simp only [deficit, length_encode]
  calc
    w * x.length - lcs (encode c x) (encode c y) ≤ w * x.length - w * lcs x y :=
      Nat.sub_le_sub_left (lcs_encode_ge c x y) _
    _ = w * (x.length - lcs x y) := (Nat.mul_sub _ _ _).symm

theorem sublist_common_large {α : Type*} {x y z : List α} (hx : x <+ z) (hy : y <+ z) :
    ∃ u : List α, u <+ x ∧ u <+ y ∧ x.length + y.length ≤ u.length + z.length := by
  induction z generalizing x y with
  | nil =>
    have : x = [] := List.sublist_nil.mp hx
    have : y = [] := List.sublist_nil.mp hy
    subst x; subst y
    exact ⟨[], .slnil, .slnil, le_rfl⟩
  | cons a z ih =>
    cases hx with
    | cons _ hx =>
      cases hy with
      | cons _ hy =>
        obtain ⟨u, hux, huy, hlen⟩ := ih hx hy
        exact ⟨u, hux, huy, by simp only [List.length_cons]; omega⟩
      | cons_cons _ hy =>
        obtain ⟨u, hux, huy, hlen⟩ := ih hx hy
        exact ⟨u, hux, huy.cons a, by simp only [List.length_cons]; omega⟩
    | cons_cons _ hx =>
      cases hy with
      | cons _ hy =>
        obtain ⟨u, hux, huy, hlen⟩ := ih hx hy
        exact ⟨u, hux.cons a, huy, by simp only [List.length_cons]; omega⟩
      | cons_cons _ hy =>
        obtain ⟨u, hux, huy, hlen⟩ := ih hx hy
        exact ⟨a :: u, hux.cons_cons a, huy.cons_cons a, by simp only [List.length_cons]; omega⟩

theorem lcs_triangle {α : Type*} (x y z : List α) : lcs x y + lcs y z ≤ y.length + lcs x z := by
  obtain ⟨a, hax, hay, ha⟩ := lcs_exists x y
  obtain ⟨b, hby, hbz, hb⟩ := lcs_exists y z
  obtain ⟨u, hua, hub, hlen⟩ := sublist_common_large hay hby
  have hle := le_lcs (hua.trans hax) (hub.trans hbz)
  omega

theorem unequalDeficit_triangle {α : Type*} (x y z : List α) :
    unequalDeficit x z ≤ unequalDeficit x y + unequalDeficit y z := by
  have hxy := lcs_le_length_left x y
  have hyx := lcs_le_length_right x y
  have hyz := lcs_le_length_left y z
  have hzy := lcs_le_length_right y z
  have hxz := lcs_le_length_left x z
  have hzx := lcs_le_length_right x z
  have ht := lcs_triangle x y z
  simp only [unequalDeficit]
  omega

theorem EditStep.unequalDeficit_le {α : Type*} {x y : List α} (h : EditStep x y) :
    unequalDeficit x y ≤ 1 := by
  cases h with
  | insert u v a =>
    have hs : u ++ v <+ u ++ a :: v := (List.Sublist.refl v).cons a |>.append_left u
    have hl := le_lcs (List.Sublist.refl (u ++ v)) hs
    simp only [unequalDeficit, List.length_append, List.length_cons]
    simp only [List.length_append] at hl
    omega
  | delete u v a =>
    have hs : u ++ v <+ u ++ a :: v := (List.Sublist.refl v).cons a |>.append_left u
    have hl := le_lcs hs (List.Sublist.refl (u ++ v))
    simp only [unequalDeficit, List.length_append, List.length_cons]
    simp only [List.length_append] at hl
    omega
  | substitute u v a b =>
    have ha : u ++ v <+ u ++ a :: v := (List.Sublist.refl v).cons a |>.append_left u
    have hb : u ++ v <+ u ++ b :: v := (List.Sublist.refl v).cons b |>.append_left u
    have hl := le_lcs ha hb
    simp only [unequalDeficit, List.length_append, List.length_cons]
    simp only [List.length_append] at hl
    omega

theorem EditScript.unequalDeficit_le {α : Type*} {n : ℕ} {x y : List α} (h : EditScript n x y) :
    unequalDeficit x y ≤ n := by
  induction h with
  | nil => simp
  | cons h hs ih =>
    exact (unequalDeficit_triangle _ _ _).trans ((Nat.add_le_add h.unequalDeficit_le ih).trans_eq (Nat.add_comm _ _))

theorem unequalDeficit_le_editDistance {α : Type*} (x y : List α) :
    unequalDeficit x y ≤ editDistance x y := (editDistance_spec x y).unequalDeficit_le

theorem editDistance_le_two_unequalDeficit {α : Type*} (x y : List α) :
    editDistance x y ≤ 2 * unequalDeficit x y := by
  obtain ⟨z, hx, hy, hz⟩ := lcs_exists x y
  have hscript := (EditScript.of_sublist hx).trans (EditScript.of_sublist hy).symm
  have hlenx := hx.length_le
  have hleny := hy.length_le
  exact (editDistance_le_of_script hscript).trans (by simp only [unequalDeficit]; omega)

theorem lcs_map_ge {α β : Type*} (f : α → β) (x y : List α) :
    lcs x y ≤ lcs (x.map f) (y.map f) := by
  obtain ⟨z, hx, hy, hz⟩ := lcs_exists x y
  have h := le_lcs (hx.map f) (hy.map f)
  simpa only [List.length_map, hz] using h

theorem lcs_map_eq {α β : Type*} (f : α → β) (hf : Function.Injective f) (x y : List α) :
    lcs (x.map f) (y.map f) = lcs x y := by
  apply Nat.le_antisymm _ (lcs_map_ge f x y)
  obtain ⟨z, hx, hy, hz⟩ := lcs_exists (x.map f) (y.map f)
  obtain ⟨u, hux, hu⟩ := List.sublist_map_iff.mp hx
  obtain ⟨v, hvy, hv⟩ := List.sublist_map_iff.mp hy
  have huv : u = v := List.map_injective_iff.mpr hf (hu.symm.trans hv)
  subst v
  have h := le_lcs hux hvy
  rw [← hz, hu, List.length_map]
  exact h

theorem lcs_append_replicate {α : Type*} [DecidableEq α] (x y : List α) (b : α)
    (hx : b ∉ x) (hy : b ∉ y) (n m : ℕ) :
    lcs (x ++ List.replicate n b) (y ++ List.replicate m b) = lcs x y + min n m := by
  let p : α → Bool := fun a => decide (a ≠ b)
  have hp (l : List α) (h : b ∉ l) : l.filter p = l := by
    apply List.filter_eq_self.mpr
    intro a ha
    exact decide_eq_true (by rintro rfl; exact h ha)
  have hnp (l : List α) (h : b ∉ l) : l.filter (fun a => !p a) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    have hab : a ≠ b := by rintro rfl; exact h ha
    simp [p, hab]
  have hpb : p b = false := by simp [p]
  have hnpb : (!p b) = true := by simp [hpb]
  apply Nat.le_antisymm
  · obtain ⟨z, hzx, hzy, hz⟩ := lcs_exists (x ++ List.replicate n b) (y ++ List.replicate m b)
    have hxt : z.filter p <+ x := by
      simpa only [List.filter_append, hp x hx, List.filter_replicate, hpb, Bool.false_eq_true, ↓reduceIte, List.append_nil] using hzx.filter p
    have hyt : z.filter p <+ y := by
      simpa only [List.filter_append, hp y hy, List.filter_replicate, hpb, Bool.false_eq_true, ↓reduceIte, List.append_nil] using hzy.filter p
    have hxn : (z.filter (fun a => !p a)).length ≤ n := by
      have h := (hzx.filter (fun a => !p a)).length_le
      simpa only [List.filter_append, hnp x hx, List.filter_replicate, hnpb, ↓reduceIte, List.nil_append, List.length_replicate] using h
    have hyn : (z.filter (fun a => !p a)).length ≤ m := by
      have h := (hzy.filter (fun a => !p a)).length_le
      simpa only [List.filter_append, hnp y hy, List.filter_replicate, hnpb, ↓reduceIte, List.nil_append, List.length_replicate] using h
    have hl := le_lcs hxt hyt
    have hs := List.length_eq_length_filter_add (l := z) p
    omega
  · obtain ⟨z, hzx, hzy, hz⟩ := lcs_exists x y
    have hn : List.replicate (min n m) b <+ List.replicate n b :=
      (List.replicate_sublist_replicate b).mpr (min_le_left _ _)
    have hm : List.replicate (min n m) b <+ List.replicate m b :=
      (List.replicate_sublist_replicate b).mpr (min_le_right _ _)
    have h := le_lcs (hzx.append hn) (hzy.append hm)
    simpa only [List.length_append, List.length_replicate, hz] using h

theorem lcs_freshPad {α : Type*} (n : ℕ) (x y : List α) :
    lcs (freshPad n x) (freshPad n y) = lcs x y + (n - max x.length y.length) := by
  classical
  unfold freshPad
  rw [lcs_append_replicate _ _ none (by simp) (by simp)]
  rw [lcs_map_eq some (Option.some_injective _)]
  congr 1
  omega

theorem deficit_freshPad {α : Type*} {n : ℕ} {x y : List α}
    (hx : x.length ≤ n) (hy : y.length ≤ n) :
    deficit (freshPad n x) (freshPad n y) = unequalDeficit x y := by
  have hl := lcs_le_length_left x y
  have hr := lcs_le_length_right x y
  simp only [deficit, length_freshPad hx, lcs_freshPad, unequalDeficit]
  omega

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.Primes ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

theorem prime_array (h : ℕ) (hh : 1000000 ≤ h) :
    ∃ p : ℕ → ℕ → ℕ,
      (∀ l k : Fin h, Nat.Prime (p (l.val+1) k) ∧ h^3 < p (l.val+1) k ∧ p (l.val+1) k ≤ 2*h^3) ∧
      Function.Injective (fun lk : Fin h × Fin h => p (lk.1.val+1) lk.2) ∧
      (∀ l k, ¬(1 ≤ l ∧ l ≤ h ∧ k < h) → p l k = 1) := by
  classical
  obtain ⟨s,hs,hcard⟩ := Finset.exists_subset_card_eq (primeInterval_card_cubic h hh)
  let e : (Fin h × Fin h) ≃ s := Fintype.equivOfCardEq (by simp [hcard, pow_two])
  let p : ℕ → ℕ → ℕ := fun l k => if hl : 1 ≤ l ∧ l ≤ h then
    if hk : k < h then (e (⟨l-1,by omega⟩,⟨k,hk⟩)).val else 1 else 1
  have hep (l k : Fin h) : p (l.val+1) k = (e (l,k)).val := by
    simp only [p, show 1 ≤ l.val+1 ∧ l.val+1 ≤ h by omega, dite_true, k.isLt]
    rfl
  refine ⟨p, ?_, ?_, ?_⟩
  · intro l k
    rw [hep]
    have he := hs (e (l,k)).property
    obtain ⟨he,hprime⟩ := Finset.mem_filter.mp he
    have hv := Finset.mem_Ioc.mp he
    exact ⟨hprime,hv.1,hv.2⟩
  · intro x y he
    simp only [hep] at he
    exact e.injective (Subtype.ext he)
  · intro l k hn
    dsimp [p]
    split_ifs with hl hk
    · exact False.elim (hn ⟨hl.1,hl.2,hk⟩)
    · rfl
    · rfl

 theorem standingPrimes_exists (h : ℕ) (hh : 1000000 ≤ h) :
    ∃ p, StandingPrimes h p := by
  obtain ⟨p,hp,hi,ho⟩ := prime_array h hh
  exact ⟨p,⟨hp,hi,ho⟩⟩

namespace StandingPrimes
variable {h : ℕ} {p : ℕ → ℕ → ℕ} (hp : StandingPrimes h p)
include hp

 theorem atLevel (l : ℕ) (hl : 1 ≤ l) (hlh : l ≤ h) (k : Fin h) :
    Nat.Prime (p l k) ∧ h^3 < p l k ∧ p l k ≤ 2*h^3 := by
  have ht := hp.inside ⟨l-1,by omega⟩ k
  simpa only [show l-1+1=l by omega] using ht

 theorem positive (l : ℕ) (k : Fin h) : 0 < p l k := by
  by_cases hl : 1 ≤ l ∧ l ≤ h
  · exact (hp.atLevel l hl.1 hl.2 k).1.pos
  · rw [hp.outside l k (by omega)]
    norm_num

 theorem period_pos (l : ℕ) : 0 < period h p l :=
  Finset.prod_pos (fun k _ => hp.positive l k)

 theorem circle_pos : 0 < circleSize h p := by
  apply Nat.mul_pos (by norm_num)
  exact Finset.prod_pos (fun l _ => hp.period_pos (l.val+1))

 theorem maskPrimes : MaskPrimes h p := by
  exact ⟨fun l k => (hp.inside l k).1, hp.inj, fun l k => ⟨(hp.inside l k).2.1.le,(hp.inside l k).2.2⟩⟩

 theorem excludedPrimes (hh : 2 ≤ h) : ExcludedPrimes h p := by
  refine ⟨fun l k => (hp.inside l k).1, hp.inj, fun l k => ⟨(hp.inside l k).2.1, ?_⟩⟩
  apply (hp.inside l k).2.2.trans
  have hh2 : 2 ≤ h^2 := by nlinarith
  calc
    2*h^3 ≤ h^2*h^3 := Nat.mul_le_mul_right _ hh2
    _ = h^5 := by ring

end StandingPrimes

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.Distortion ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

 theorem upperRates_finite {α X : Type*} [Finite X] (word : X → List α) (f : X → RealL1) :
    (upperRates word f).Finite := by
  apply (Set.finite_range (fun z : X×X => ‖f z.1-f z.2‖/(editDistance (word z.1) (word z.2):ℝ))).subset
  rintro r ⟨x,y,_,rfl⟩
  exact ⟨(x,y),rfl⟩

 theorem lowerRates_finite {α X : Type*} [Finite X] (word : X → List α) (f : X → RealL1) :
    (lowerRates word f).Finite := by
  apply (Set.finite_range (fun z : X×X => (editDistance (word z.1) (word z.2):ℝ)/‖f z.1-f z.2‖)).subset
  rintro r ⟨x,y,_,rfl⟩
  exact ⟨(x,y),rfl⟩

 theorem distortion_nonneg {α X : Type*} (word : X → List α) (f : X → RealL1) :
    0 ≤ distortion word f := by
  apply mul_nonneg
  · apply Real.sSup_nonneg
    rintro r ⟨x,y,_,rfl⟩
    positivity
  · apply Real.sSup_nonneg
    rintro r ⟨x,y,_,rfl⟩
    positivity

 theorem finite_l1_embedding (X : Type*) [Fintype X] : ∃ f : X → RealL1, Function.Injective f := by
  classical
  let e : X → ℕ := fun x => (Fintype.equivFin X x).val
  have he : Function.Injective e := fun x y h => (Fintype.equivFin X).injective (Fin.ext h)
  refine ⟨fun x => lp.single 1 (e x) (1:ℝ), ?_⟩
  intro x y h
  by_contra hxy
  have hne : e x ≠ e y := fun h => hxy (he h)
  have ht := congrArg (fun f : RealL1 => f (e x)) h
  simp only [lp.single_apply_self, lp.single_apply, Pi.single_eq_of_ne hne] at ht
  norm_num at ht

 theorem optimalDistortion_lower {α X : Type*} [Fintype X] (word : X → List α) (D : ℝ)
    (hD : ∀ f : X → RealL1, Function.Injective f → D ≤ distortion word f) :
    D ≤ optimalDistortion word := by
  apply le_csInf
  · obtain ⟨f,hf⟩ := finite_l1_embedding X
    exact ⟨distortion word f,f,hf,rfl⟩
  · rintro b ⟨f,hf,rfl⟩
    exact hD f hf

 theorem optimalDistortion_le {α X : Type*} (word : X → List α)
    (f : X → RealL1) (hf : Function.Injective f) :
    optimalDistortion word ≤ distortion word f := by
  apply csInf_le
  · refine ⟨0,?_⟩
    rintro b ⟨g,_,rfl⟩
    exact distortion_nonneg word g
  · exact ⟨f,hf,rfl⟩

 theorem finiteL1_sub (M : ℕ) (v w : Fin M → ℝ) :
    finiteL1 M v-finiteL1 M w=finiteL1 M (v-w) := by
  unfold finiteL1
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact (lp.single_sub (E:=fun _ : ℕ=>ℝ) 1 i.val (v i) (w i)).symm

 theorem finiteL1_norm (M : ℕ) (v : Fin M → ℝ) : ‖finiteL1 M v‖=∑ i, |v i| := by
  classical
  let g : ℕ → ℝ := fun i => if hi : i<M then v ⟨i,hi⟩ else 0
  have he : finiteL1 M v = ∑ i ∈ Finset.range M, lp.single 1 i (g i) := by
    unfold finiteL1
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    simp [g]
  rw [he]
  have ht := lp.norm_sum_single (E:=fun _ : ℕ=>ℝ) (p:=1) (by norm_num) g (Finset.range M)
  simpa [g,← Fin.sum_univ_eq_sum_range] using ht

 theorem finiteL1_norm_sub (M : ℕ) (v w : Fin M → ℝ) :
    ‖finiteL1 M v-finiteL1 M w‖=∑ i, |v i-w i| := by
  rw [finiteL1_sub,finiteL1_norm]
  rfl

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.Parameters ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem StandingPrimes.small_prime {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 2 ≤ h) (l : ℕ) (hl : 1≤l) (hlh : l≤h) (k : Fin h) :
    p l k ≤ h^4 := by
  apply (hp.atLevel l hl hlh k).2.2.trans
  calc
    2*h^3 ≤ h*h^3 := Nat.mul_le_mul_right _ hh
    _ = h^4 := by ring

 theorem StandingPrimes.period_bound {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 2 ≤ h) (l : ℕ) (hl : 1≤l) (hlh : l≤h) :
    period h p l ≤ h^(4*h) := by
  calc
    _ ≤ ∏ _k : Fin h, h^4 := Finset.prod_le_prod' (fun k _ => hp.small_prime hh l hl hlh k)
    _ = _ := by simp [← pow_mul]

 theorem StandingPrimes.circle_bound {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 2 ≤ h) : circleSize h p ≤ h^(5*h^2) := by
  calc
    _ ≤ h*(∏ _l : Fin h, h^(4*h)) := Nat.mul_le_mul hh
      (Finset.prod_le_prod' (fun l _ => hp.period_bound hh (l.val+1) (by omega) (by omega)))
    _ = h^(4*h^2+1) := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]; ring
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by nlinarith)

 theorem StandingPrimes.tags_bound {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 2 ≤ h) (l : ℕ) (hl : 1≤l) (hlh : l≤h) :
    (maskTags h p l).length ≤ h^5 := by
  rw [length_maskTags]
  calc
    _ ≤ ∑ _k : Fin h, h^4 := Finset.sum_le_sum (fun k _ => hp.small_prime hh l hl hlh k)
    _ = _ := by simp; ring

 theorem StandingPrimes.mask_length_bound {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 3≤h) :
    maskLength h p (h^(2*h)) (circleSize h p) h ≤ h^(13*h^2) := by
  have ht := recursive_length_bound h (circleSize h p) (period h p)
    (fun l => (maskTags h p l).length) (maskLength h p (h^(2*h)) (circleSize h p)) hh rfl
    (fun _ => rfl) (hp.period_bound (by omega)) (hp.tags_bound (by omega)) h (le_refl _)
  calc
    _ ≤ circleSize h p*h^(8*h*h) := ht
    _ ≤ h^(5*h^2)*h^(8*h*h) := Nat.mul_le_mul_right _ (hp.circle_bound (by omega))
    _ = _ := by ring

 theorem StandingPrimes.excluded_length_bound {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 3≤h) :
    excludedLength h p (h^(2*h)) (circleSize h p) h ≤ h^(13*h^2) := by
  have ht := recursive_length_bound h (circleSize h p) (period h p)
    (fun _ => h) (excludedLength h p (h^(2*h)) (circleSize h p)) hh rfl
    (fun l => by simp only [excludedLength,length_excludedTags]) (hp.period_bound (by omega))
    (fun _ _ _ => le_self_pow₀ (by omega) (by norm_num)) h (le_refl _)
  calc
    _ ≤ circleSize h p*h^(8*h*h) := ht
    _ ≤ h^(5*h^2)*h^(8*h*h) := Nat.mul_le_mul_right _ (hp.circle_bound (by omega))
    _ = _ := by ring

 theorem StandingPrimes.excluded_alphabet_ge {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 1≤h) (l : ℕ) :
    2≤Fintype.card (ExcludedAlphabet h (circleSize h p) l) := by
  induction l with
  | zero =>
    change 2≤Fintype.card (Fin (circleSize h p) × Bool)
    rw [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
    have ht := hp.circle_pos
    omega
  | succ l ih =>
    change 2≤Fintype.card (Fin h × ExcludedAlphabet h (circleSize h p) l)
    rw [Fintype.card_prod,Fintype.card_fin]
    nlinarith

 theorem StandingPrimes.mask_length_pos {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 1≤h) {R : ℕ} (hR : 0<R) (l : ℕ) :
    0 < maskLength h p R (circleSize h p) l := by
  induction l with
  | zero => exact hp.circle_pos
  | succ l ih =>
    have hT : h≤(maskTags h p (l+1)).length := by
      rw [length_maskTags]
      calc
        _ = ∑ _k : Fin h, 1 := by simp
        _ ≤ _ := Finset.sum_le_sum (fun k _ => hp.positive _ k)
    exact Nat.mul_pos (Nat.mul_pos hR (hp.period_pos _)) (Nat.mul_pos (by omega) ih)

 theorem StandingPrimes.excluded_length_pos {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 1≤h) {R : ℕ} (hR : 0<R) (l : ℕ) :
    0<excludedLength h p R (circleSize h p) l := by
  induction l with
  | zero => exact hp.circle_pos
  | succ l ih =>
    simp only [excludedLength,length_excludedTags]
    exact Nat.mul_pos (Nat.mul_pos hR (hp.period_pos _)) (Nat.mul_pos (by omega) ih)

 theorem logarithmic_width_bound {h A w : ℕ} (hh : 100000000≤h) (hA : 0<A)
    (hAb : A≤h^(6*h^2)) (hw : (w:ℝ)≤67108928*Real.log (2*(A:ℝ))) :
    w≤h^(7*h^2) := by
  have hn : Real.log (2*(A:ℝ))≤2*A := by
    have ht := Real.log_le_sub_one_of_pos (show 0<2*(A:ℝ) by positivity)
    linarith
  have hwr : (w:ℝ)≤67108928*(2*A) := hw.trans (mul_le_mul_of_nonneg_left hn (by norm_num))
  have hwn : w≤67108928*(2*A) := by exact_mod_cast hwr
  calc
    _ ≤ 67108928*(2*A) := hwn
    _ ≤ h*(h*h^(6*h^2)) := Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) hAb)
    _ = h^(6*h^2+2) := by ring
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by nlinarith)

 theorem coded_length_cap {h A w L : ℕ} (hh : 100000000≤h) (hA : 0<A)
    (hAb : A≤h^(6*h^2)) (hw : (w:ℝ)≤67108928*Real.log (2*(A:ℝ)))
    (hL : L≤h^(13*h^2)) : w*L≤h^(32*h^2) := by
  calc
    _ ≤ h^(7*h^2)*h^(13*h^2) := Nat.mul_le_mul (logarithmic_width_bound hh hA hAb hw) hL
    _ = h^(20*h^2) := by ring
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.Codes ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

theorem StrongLocal.anchorLocal {α : Type*} {w : ℕ} {c : α → Fin w → Bool}
    (hc : StrongLocal c) : AnchorLocal (1/1048576) c := by
  intro a b is js his hjs hlen hsize hli hlj hbits
  apply hc a b is js his hjs hlen
  · have hh : (w : ℝ) ≤ 16*is.length := by nlinarith
    exact_mod_cast hh
  · convert hli using 1; ring
  · convert hlj using 1; ring
  · exact hbits

theorem strongLocal_substitutionBounds {α : Type*} [Fintype α] {w : ℕ}
    {c : α → Fin w → Bool} (hw : 0 < w)
    (hwidth : (w : ℝ) ≤ 67108928*Real.log (2*Fintype.card α)) (hc : StrongLocal c) :
    SubstitutionBounds (1/2097152) 67108928 c := by
  refine ⟨hw, hwidth, ?_, editDistance_encode_le c⟩
  intro L x y hx hy
  refine ⟨?_, deficit_encode_le c x y⟩
  have hh := anchor_deficit_lower hw (by norm_num : (0 : ℝ) ≤ 1/1048576)
    (by norm_num : (1 : ℝ)/1048576 ≤ 1/10) hc.anchorLocal x y (hx.trans hy.symm)
  convert hh using 1; norm_num

theorem SubstitutionBounds.weaken {α : Type*} [Fintype α] {w : ℕ}
    {c : α → Fin w → Bool} {a b C : ℝ} (hc : SubstitutionBounds a C c)
    (hba : b ≤ a) : SubstitutionBounds b C c := by
  refine ⟨hc.1,hc.2.1,?_,hc.2.2.2⟩
  intro L x y hx hy
  obtain ⟨hl,hu⟩ := hc.2.2.1 L x y hx hy
  refine ⟨?_,hu⟩
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hba
    (Nat.cast_nonneg w)) (Nat.cast_nonneg (deficit x y))).trans hl

theorem offsetLocal_substitutionBounds {α : Type*} [Fintype α] {w : ℕ}
    {c : α → Fin w → Bool} (hw : 12 ≤ w) (hd : 8 ∣ w)
    (hwidth : (w : ℝ) ≤ 67108928 * Real.log (2*Fintype.card α))
    (hc : OffsetLocal (1/1048576) c) : SubstitutionBounds (1/268435456) 67108928 c := by
  refine ⟨by omega,hwidth,?_,editDistance_encode_le c⟩
  intro L x y hx hy
  refine ⟨?_,deficit_encode_le c x y⟩
  have he : (8 : ℝ)*(w/8 : ℕ) = w := by exact_mod_cast (Nat.mul_div_cancel' hd)
  have hw0 : (0 : ℝ) < w := by exact_mod_cast (show 0<w by omega)
  have hfit : 2*(1/33554432 : ℝ)*w < (1/1048576 : ℝ)*(w/8 : ℕ) := by
    linarith only [he,hw0]
  have hh := offset_deficit_lower hw (by norm_num : (1 : ℝ)/1048576 ≤ 1)
    (by norm_num : (0 : ℝ) ≤ 1/33554432) (by norm_num : (1 : ℝ)/33554432 ≤ 1)
    hfit hc x y (hx.trans hy.symm)
  apply le_trans _ hh
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (by norm_num : (1 : ℝ)/268435456 ≤ (1/33554432)/(4+32*(1/33554432)))
    (Nat.cast_nonneg w)) (Nat.cast_nonneg (deficit x y))

theorem two_codes : TwoCodes (1/268435456) 67108928 (1/1048576) (1/1048576) := by
  intro α _ hA
  obtain ⟨w, c, hw, hd, hwidth, hc⟩ := exists_strongLocal α hA
  have hwp : 0 < w := by omega
  have hd8 : 8 ∣ w := dvd_trans (by norm_num : 8 ∣ 64) hd
  have ho := hc.offsetLocal hwp hd8
  have hbo := offsetLocal_substitutionBounds (by omega) hd8 hwidth ho
  have hba := (strongLocal_substitutionBounds hwp hwidth hc).weaken
    (by norm_num : (1 : ℝ)/268435456 ≤ 1/2097152)
  exact ⟨⟨w,c,hbo,ho⟩,⟨w,c,hba,hc.anchorLocal⟩⟩

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.Lower ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

 theorem lowerCap_ge (n : ℕ) : n≤lowerCap n := by
  by_cases hn : n=0
  · subst n; exact Nat.zero_le _
  have hn1 : 1≤n := by omega
  exact (le_self_pow₀ hn1 (by norm_num) : n≤n^4).trans
    (le_self_pow₀ (one_le_pow₀ hn1) (by simp [hn]) : n^4≤(n^4)^(32*(n^4)^2))

 theorem lower_parameter (d : ℕ) (hd : lowerCap 1000000≤d) :
    ∃ q : ℕ, 500000≤q ∧ lowerCap (2*q)≤d ∧ d<lowerCap (2*(q+1)) := by
  classical
  let P := fun q : ℕ => lowerCap (2*q)≤d
  let q := Nat.findGreatest P d
  have h0 : 500000≤d := by have := lowerCap_ge 1000000; omega
  have hp : P 500000 := hd
  have hq : 500000≤q := by
    by_contra hn
    have ht := Nat.findGreatest_is_greatest (P:=P) (show q<500000 by omega) h0
    exact ht hp
  refine ⟨q,hq,Nat.findGreatest_spec h0 hp,?_⟩
  by_contra hn
  have hnext : P (q+1) := by dsimp [P]; omega
  have hb : q+1≤d := by have := lowerCap_ge (2*(q+1)); dsimp [P] at hnext; omega
  exact Nat.findGreatest_is_greatest (P:=P) (show q<q+1 by omega) hb hnext

 theorem mask_witness_parameter {q d : ℕ} (hq : 500000≤q) (hd0 : 2≤d)
    (hl : lowerCap (2*q)≤d) (hu : d<lowerCap (2*(q+1))) :
    MaskWitness (1/268435456) 67108928 (1/1048576) (1/8192) d := by
  classical
  let n := 2*q
  let h := n^4
  have hn : 1000000≤n := by dsimp [n]; omega
  have hh : 100000000≤h := by
    exact (show 100000000≤1000000^4 by norm_num).trans (Nat.pow_le_pow_left hn 4)
  obtain ⟨p,hp⟩ := standingPrimes_exists h (by omega)
  obtain ⟨w,c,hc,ho⟩ := (two_codes (MaskAlphabet h p h) (hp.mask_alphabet_ge (by omega) h)).1
  let L := maskLength h p (h^(2*h)) (circleSize h p) h
  have hL : 0<L := hp.mask_length_pos (by omega) (pow_pos (by omega) _) h
  have hcap : w*L≤lowerCap n := coded_length_cap hh
    (by have := hp.mask_alphabet_ge (by omega) h; omega)
    (hp.mask_alphabet_bound (by omega)) hc.2.1 (hp.mask_length_bound (by omega))
  refine ⟨h,by omega,p,hp.maskPrimes,w,c,hc,ho,w*L,Nat.mul_pos hc.1 hL,hcap.trans hl,?_,?_⟩
  · intro v
    simp only [length_encode,length_maskWord,L]
  · exact (all_length_inversion hq hd0 hu).trans
      (mask_binary_distortion hn (show n^4=4*(4*q^4) by dsimp [n]; ring) hp c hc)

 theorem excluded_witness_parameter {q d : ℕ} (hq : 500000≤q) (hd0 : 2≤d)
    (hl : lowerCap (2*q)≤d) (hu : d<lowerCap (2*(q+1))) :
    ExcludedWitness (1/268435456) 67108928 (1/1048576) (1/8192) d := by
  classical
  let n := 2*q
  let h := n^4
  have hn : 1000000≤n := by dsimp [n]; omega
  have hh : 100000000≤h := by
    exact (show 100000000≤1000000^4 by norm_num).trans (Nat.pow_le_pow_left hn 4)
  obtain ⟨p,hp⟩ := standingPrimes_exists h (by omega)
  obtain ⟨w,c,hc,ho⟩ := (two_codes (ExcludedAlphabet h (circleSize h p) h)
    (hp.excluded_alphabet_ge (by omega) h)).2
  let L := excludedLength h p (h^(2*h)) (circleSize h p) h
  have hL : 0<L := hp.excluded_length_pos (by omega) (pow_pos (by omega) _) h
  have hcap : w*L≤lowerCap n := coded_length_cap hh
    (by have := hp.excluded_alphabet_ge (by omega) h; omega)
    (hp.excluded_alphabet_bound (by omega)) hc.2.1 (hp.excluded_length_bound (by omega))
  refine ⟨h,by omega,p,hp.excludedPrimes (by omega),w,c,hc,ho,w*L,Nat.mul_pos hc.1 hL,hcap.trans hl,?_,?_⟩
  · intro v
    simp only [length_encode,length_excludedWord,L]
  · exact (all_length_inversion hq hd0 hu).trans
      (excluded_binary_distortion hn (show n^4=4*(4*q^4) by dsimp [n]; ring) hp c hc)

 theorem both_witnesses {d : ℕ} (hd : lowerCap 1000000≤d) :
    MaskWitness (1/268435456) 67108928 (1/1048576) (1/8192) d ∧
    ExcludedWitness (1/268435456) 67108928 (1/1048576) (1/8192) d := by
  obtain ⟨q,hq,hl,hu⟩ := lower_parameter d hd
  have hd0 : 2≤d := by have := lowerCap_ge 1000000; omega
  exact ⟨mask_witness_parameter hq hd0 hl hu,excluded_witness_parameter hq hd0 hl hu⟩

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.UpperParameters ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

theorem log_add_one_le_dyadic_count (n : ℕ) :
    Real.log ((n:ℝ)+1) ≤ Nat.log 2 n + 1 := by
  have hpow : n+1 ≤ 2^(Nat.log 2 n + 1) :=
    Nat.succ_le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) n)
  have hlog := Real.log_le_log (by positivity : (0:ℝ) < (n:ℝ)+1)
    (show (n:ℝ)+1 ≤ (2:ℝ)^(Nat.log 2 n+1) by exact_mod_cast hpow)
  rw [Real.log_pow] at hlog
  have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hc : (0:ℝ) ≤ Nat.log 2 n + 1 := by positivity
  push_cast at hlog
  nlinarith

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.Upper ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

theorem one_letter_embedding {α : Type*} [Fintype α] :
    ∃ M : ℕ, ∃ F : List.Vector α 1 → Fin M → ℝ, ∀ x y,
      (deficit x.val y.val : ℝ) ≤ coordDist F x y ∧
      coordDist F x y ≤ 2 * deficit x.val y.val := by
  classical
  let X := List.Vector α 1
  let : DecidableEq X := Classical.decEq X
  let e := Fintype.equivFin X
  let F : X → Fin (Fintype.card X) → ℝ := fun x i => if e.symm i = x then 1 else 0
  have he (x y : X) : coordDist F x y = if x = y then 0 else 2 := by
    unfold coordDist
    rw [← e.sum_comp (fun i => |F x i - F y i|)]
    simp only [F, Equiv.symm_apply_apply]
    by_cases h : x = y
    · simp [h]
    · rw [ite_eq_right h]
      have hh (i : X) : |(if i = x then (1:ℝ) else 0) - (if i = y then 1 else 0)| =
          (if i = x then 1 else 0) + (if i = y then 1 else 0) := by
        split_ifs <;> simp_all
      simp_rw [hh]
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      norm_num
  have hd (x y : X) : deficit x.val y.val = if x = y then 0 else 1 := by
    by_cases h : x = y
    · simp [h, deficit]
    · rw [ite_eq_right h]
      have hx : x.val.length = 1 := x.property
      have hy : y.val.length = 1 := y.property
      have hu := lcs_le_length_left x.val y.val
      have h0 : lcs x.val y.val = 0 := by
        by_contra hc
        have hl : lcs x.val y.val = 1 := by omega
        obtain ⟨z, hz, hw, heq⟩ := lcs_exists x.val y.val
        have hzx : z = x.val := hz.eq_of_length (by omega)
        have hzy : z = y.val := hw.eq_of_length (by omega)
        exact h (Subtype.ext (hzx.symm.trans hzy))
      simp [deficit, hx, h0]
  refine ⟨Fintype.card X, F, fun x y => ?_⟩
  rw [he, hd]
  split_ifs <;> norm_num

theorem histogram_factor_le {b m n : ℕ} (hmn : m ≤ n) {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    16 * ((Nat.log 2 m : ℝ)+1) * ((b:ℝ) + 16 * Real.log ((m:ℝ)+1) * Λ) ≤
      512 * ((Nat.log 2 n : ℝ)+1)^2 * ((b:ℝ)+Λ) := by
  let K : ℝ := (Nat.log 2 n : ℝ)+1
  have hK : 1 ≤ K := by dsimp [K]; linarith [Nat.cast_nonneg (α := ℝ) (Nat.log 2 n)]
  have hK0 : 0 ≤ K := by linarith
  have hl : Real.log ((m:ℝ)+1) ≤ K :=
    (log_add_one_le_dyadic_count m).trans (by
      dsimp [K]
      exact_mod_cast Nat.add_le_add_right (Nat.log_mono_right hmn) 1)
  have hmK : (Nat.log 2 m : ℝ)+1 ≤ K := by
    dsimp [K]
    exact_mod_cast Nat.add_le_add_right (Nat.log_mono_right hmn) 1
  have hn : (0:ℝ) ≤ b := Nat.cast_nonneg b
  have hl0 : 0 ≤ Real.log ((m:ℝ)+1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) m])
  calc
    _ ≤ 16*K*((b:ℝ)+16*K*Λ) := by gcongr
    _ ≤ 512*K^2*((b:ℝ)+Λ) := by
      have hKb : K*(b:ℝ) ≤ K^2*b := mul_le_mul_of_nonneg_right (by nlinarith only [hK] : K ≤ K^2) hn
      have hKΛ : 0 ≤ K^2*Λ := mul_nonneg (sq_nonneg K) hΛ
      nlinarith only [hKb, hKΛ, mul_nonneg (sq_nonneg K) hn]

theorem power_length_embedding {α : Type*} [Fintype α] (a : α) {b H : ℕ} (hb : 2 ≤ b) :
    ∃ M : ℕ, ∃ F : List.Vector α (b^H) → Fin M → ℝ, ∀ x y,
      (deficit x.val y.val : ℝ) ≤ coordDist F x y ∧
      coordDist F x y ≤ (b * (1024 * ((Nat.log 2 (b^H) : ℝ)+1)^2)^H) * deficit x.val y.val := by
  let n := b^H
  let B : ℝ := 1024 * ((Nat.log 2 n : ℝ)+1)^2
  have hb0 : 0 < b := by omega
  have hbR : (2:ℝ) ≤ b := by exact_mod_cast hb
  have hB : 1 ≤ B := by
    have h : (1:ℝ) ≤ (Nat.log 2 n : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) (Nat.log 2 n)]
    dsimp [B]
    nlinarith
  have hB0 : 0 ≤ B := by linarith
  have all (k : ℕ) (hk : k ≤ H) :
      ∃ M : ℕ, ∃ F : List.Vector α (b^k) → Fin M → ℝ, ∀ x y,
        (deficit x.val y.val : ℝ) ≤ coordDist F x y ∧
        coordDist F x y ≤ ((b:ℝ)*B^k) * deficit x.val y.val := by
    induction k with
    | zero =>
      obtain ⟨M, F, hF⟩ := one_letter_embedding (α := α)
      refine ⟨M, F, fun x y => ⟨(hF x y).1, ?_⟩⟩
      simpa using (hF x y).2.trans (mul_le_mul_of_nonneg_right hbR (Nat.cast_nonneg _))
    | succ k ih =>
      obtain ⟨M, F, hF⟩ := ih (by omega)
      have hΛ : (0:ℝ) ≤ (b:ℝ)*B^k := by positivity
      obtain ⟨M', F', hF'⟩ := histogram_embedding_step a (pow_pos hb0 k) b F ((b:ℝ)*B^k)
        hΛ (fun x y => (hF x y).1) (fun x y => (hF x y).2)
      have hmn : b^k ≤ n := Nat.pow_le_pow_right hb0 (by omega)
      have hfactor := histogram_factor_le (b := b) hmn hΛ
      have hΛb : (b:ℝ) ≤ (b:ℝ)*B^k := by
        exact le_mul_of_one_le_right (Nat.cast_nonneg b) (one_le_pow₀ hB)
      have hfac : 16 * ((Nat.log 2 (b^k) : ℝ)+1) *
          ((b:ℝ)+16*Real.log (((b^k : ℕ):ℝ)+1)*((b:ℝ)*B^k)) ≤ (b:ℝ)*B^(k+1) := by
        calc
          _ ≤ 512*((Nat.log 2 n : ℝ)+1)^2*((b:ℝ)+(b:ℝ)*B^k) := hfactor
          _ ≤ 512*((Nat.log 2 n : ℝ)+1)^2*(2*((b:ℝ)*B^k)) := by gcongr; linarith
          _ = _ := by dsimp [B]; rw [pow_succ]; ring
      rw [pow_succ']
      refine ⟨M', F', fun x y => ⟨(hF' x y).1, ?_⟩⟩
      exact (hF' x y).2.trans (mul_le_mul_of_nonneg_right hfac (Nat.cast_nonneg _))
  exact all H le_rfl

theorem uniform_upper_of_log_large {α : Type*} [Fintype α] {d : ℕ}
    (hd : 16 ≤ Real.log d) :
    ∃ M : ℕ, ∃ F : Words α d → Fin M → ℝ, ∀ x y,
      (editDistance x.val y.val : ℝ) ≤ coordDist F x y ∧
      coordDist F x y ≤ Real.exp (32 * exponentScale d) * editDistance x.val y.val := by
  obtain ⟨b, H, hb, _, hdn, hbound⟩ := exists_power_parameters hd
  obtain ⟨M, G, hG⟩ := power_length_embedding (α := Option α) none (H := H) hb
  let pad : Words α d → List.Vector (Option α) (b^H) := fun x =>
    ⟨freshPad (b^H) x.val, length_freshPad (x.property.trans hdn)⟩
  let F : Words α d → Fin M → ℝ := fun x i => 2 * G (pad x) i
  have he (x y : Words α d) : coordDist F x y = 2*coordDist G (pad x) (pad y) := by
    simp only [coordDist, F, ← mul_sub, abs_mul, show |(2:ℝ)| = 2 by norm_num, Finset.mul_sum]
  have hpad (x y : Words α d) : deficit (pad x).val (pad y).val = unequalDeficit x.val y.val :=
    deficit_freshPad (x.property.trans hdn) (y.property.trans hdn)
  refine ⟨M, F, fun x y => ⟨?_, ?_⟩⟩
  · rw [he]
    have h := (hG (pad x) (pad y)).1
    rw [hpad] at h
    have he := editDistance_le_two_unequalDeficit x.val y.val
    exact (by exact_mod_cast he : (editDistance x.val y.val : ℝ) ≤ 2*(unequalDeficit x.val y.val:ℝ)).trans (by linarith)
  · rw [he]
    have h := (hG (pad x) (pad y)).2
    rw [hpad] at h
    have hq : (unequalDeficit x.val y.val:ℝ) ≤ editDistance x.val y.val :=
      by exact_mod_cast unequalDeficit_le_editDistance x.val y.val
    have hB : 0 ≤ (b:ℝ)*(1024*((Nat.log 2 (b^H):ℝ)+1)^2)^H := by positivity
    calc
      _ ≤ 2*((b:ℝ)*(1024*((Nat.log 2 (b^H):ℝ)+1)^2)^H) * unequalDeficit x.val y.val := by linarith
      _ ≤ 2*((b:ℝ)*(1024*((Nat.log 2 (b^H):ℝ)+1)^2)^H) * editDistance x.val y.val := by gcongr
      _ ≤ Real.exp (32*exponentScale d) * editDistance x.val y.val := by
        gcongr
        dsimp [exponentScale]
        nlinarith only [hbound, hB]

theorem uniform_upper : ∃ d₀ : ℕ, UniformUpper 32 d₀ := by
  refine ⟨⌈Real.exp 16⌉₊, fun α _ _ d hd => ?_⟩
  have hdexp : Real.exp 16 ≤ (d:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hd)
  have hlog : 16 ≤ Real.log d := by
    have h := Real.log_le_log (Real.exp_pos 16) hdexp
    simpa only [Real.log_exp] using h
  exact uniform_upper_of_log_large hlog

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.Main ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

theorem upperRates_sup_nonneg {α X : Type*} (word : X → List α) (f : X → RealL1) :
    0 ≤ sSup (upperRates word f) := by
  apply Real.sSup_nonneg
  rintro r ⟨x,y,_,rfl⟩
  positivity

 theorem lowerRates_sup_nonneg {α X : Type*} (word : X → List α) (f : X → RealL1) :
    0 ≤ sSup (lowerRates word f) := by
  apply Real.sSup_nonneg
  rintro r ⟨x,y,_,rfl⟩
  positivity

 theorem distortion_isometry_restrict {α β X Y : Type*} [Finite Y]
    (wordX : X → List α) (wordY : Y → List β) (g : X → Y) (hg : Function.Injective g)
    (he : ∀ x y, editDistance (wordY (g x)) (wordY (g y)) = editDistance (wordX x) (wordX y))
    (f : Y → RealL1) : distortion wordX (f ∘ g) ≤ distortion wordY f := by
  have hu : sSup (upperRates wordX (f ∘ g)) ≤ sSup (upperRates wordY f) := by
    apply Real.sSup_le _ (upperRates_sup_nonneg wordY f)
    rintro r ⟨x,y,hxy,rfl⟩
    apply le_csSup (upperRates_finite wordY f).bddAbove
    exact ⟨g x,g y,fun h => hxy (hg h),by simp only [Function.comp_apply,he]⟩
  have hl : sSup (lowerRates wordX (f ∘ g)) ≤ sSup (lowerRates wordY f) := by
    apply Real.sSup_le _ (lowerRates_sup_nonneg wordY f)
    rintro r ⟨x,y,hxy,rfl⟩
    apply le_csSup (lowerRates_finite wordY f).bddAbove
    exact ⟨g x,g y,fun h => hxy (hg h),by simp only [Function.comp_apply,he]⟩
  exact mul_le_mul hu hl (lowerRates_sup_nonneg wordX (f ∘ g)) (upperRates_sup_nonneg wordY f)

 theorem optimalDistortion_isometry_mono {α β X Y : Type*} [Fintype Y]
    (wordX : X → List α) (wordY : Y → List β) (g : X → Y) (hg : Function.Injective g)
    (he : ∀ x y, editDistance (wordY (g x)) (wordY (g y)) = editDistance (wordX x) (wordX y)) :
    optimalDistortion wordX ≤ optimalDistortion wordY := by
  apply optimalDistortion_lower
  intro f hf
  exact (optimalDistortion_le wordX (f ∘ g) (hf.comp hg)).trans
    (distortion_isometry_restrict wordX wordY g hg he f)

 theorem words_nontrivial (α : Type*) [Nonempty α] {d : ℕ} (hd : 1≤d) : Nontrivial (Words α d) := by
  classical
  let a : α := Classical.ofNonempty
  refine ⟨⟨⟨[],by simp⟩,⟨[a],by simpa using hd⟩,?_⟩⟩
  intro he
  have ht := congrArg (fun x : Words α d => x.val.length) he
  simp at ht

 theorem binary_alphabet_embedding (α : Type*) [Fintype α] (hα : 2≤Fintype.card α) :
    ∃ (f : Bool → α) (g : α → Bool), Function.LeftInverse g f := by
  classical
  let : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp hα
  obtain ⟨a,b,hab⟩ := exists_pair_ne α
  refine ⟨fun t => cond t b a,fun x => decide (x=b),?_⟩
  intro t
  cases t <;> simp [hab]

 theorem setDistortion_le_E (α : Type*) [Fintype α] (hα : 2≤Fintype.card α)
    {S : Set (List Bool)} {d : ℕ} (hS : ∀ x∈S, x.length≤d) : setDistortion S≤E α d := by
  classical
  let : Fintype (Words α d) := Fintype.ofFinite _
  obtain ⟨f,g,hgf⟩ := binary_alphabet_embedding α hα
  let e : S → Words α d := fun x => ⟨x.val.map f,by simpa using hS x.val x.property⟩
  have he : Function.Injective e := by
    intro x y hxy
    exact Subtype.ext (hgf.injective.list_map (congrArg Subtype.val hxy))
  apply optimalDistortion_isometry_mono (fun x : S => x.val) (fun x : Words α d => x.val) e he
  intro x y
  exact editDistance_map_eq f g hgf x.val y.val

 theorem maskWitness_lower_E {a C δ c : ℝ} {d : ℕ} (hw : MaskWitness a C δ c d)
    (α : Type*) [Fintype α] (hα : 2≤Fintype.card α) : Real.exp (c*exponentScale d)≤E α d := by
  rcases hw with ⟨h,_,p,_,w,code,_,_,n,_,hnd,hlen,hD⟩
  apply hD.trans (setDistortion_le_E α hα _)
  rintro x ⟨v,rfl⟩
  exact (hlen v).le.trans hnd

 theorem uniformUpper_E {C : ℝ} {d₀ : ℕ} (hu : UniformUpper C d₀)
    (α : Type) [Fintype α] (hα : 2≤Fintype.card α) {d : ℕ} (hd : d₀≤d) (hd1 : 1≤d) :
    E α d≤Real.exp (C*exponentScale d) := by
  classical
  let : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp hα
  let : Nontrivial (Words α d) := words_nontrivial α hd1
  obtain ⟨M,F,hF⟩ := hu α hα d hd
  let f : Words α d → RealL1 := fun x => finiteL1 M (F x)
  have hb := distortion_upper (fun x : Words α d => x.val) Subtype.val_injective
    f (Real.exp (C*exponentScale d)) 1 (Real.exp_pos _).le
    (fun x y => by simpa only [f,finiteL1_norm_sub] using (hF x y).2)
    (fun x y => by simpa only [f,one_mul,finiteL1_norm_sub] using (hF x y).1)
  exact (optimalDistortion_le (fun x : Words α d => x.val) f hb.1).trans (by simpa only [mul_one] using hb.2)

 theorem alphabetSupremum_bounds {d : ℕ} {lo hi : ℝ}
    (hb : ∀ A : ℕ, 2≤A → lo≤E (Fin A) d ∧ E (Fin A) d≤hi) :
    lo≤alphabetSupremum d ∧ alphabetSupremum d≤hi := by
  have hne : {r : ℝ | ∃ A : ℕ, 2≤A ∧ r=E (Fin A) d}.Nonempty := ⟨_,2,by norm_num,rfl⟩
  have hub : BddAbove {r : ℝ | ∃ A : ℕ, 2≤A ∧ r=E (Fin A) d} := by
    refine ⟨hi,?_⟩
    rintro r ⟨A,hA,rfl⟩
    exact (hb A hA).2
  refine ⟨(hb 2 (by norm_num)).1.trans (le_csSup hub ⟨2,by norm_num,rfl⟩),?_⟩
  apply csSup_le hne
  rintro r ⟨A,hA,rfl⟩
  exact (hb A hA).2

theorem full_main : FullMain := by
  obtain ⟨u,hu⟩ := uniform_upper
  let d₀ := max u (lowerCap 1000000)
  have hlow {d : ℕ} (hd : d₀≤d) : lowerCap 1000000≤d := (le_max_right _ _).trans hd
  have hu' : UniformUpper 32 d₀ := by
    intro α _ hα d hd
    exact hu α hα d ((le_max_left _ _).trans hd)
  have hb : ∀ (α : Type) [Fintype α], 2≤Fintype.card α → ∀ d : ℕ, d₀≤d →
      Real.exp ((1/8192)*exponentScale d)≤E α d ∧ E α d≤Real.exp (32*exponentScale d) := by
    intro α _ hα d hd
    have hd1 : 1≤d := by have := lowerCap_ge 1000000; have := hlow hd; omega
    exact ⟨maskWitness_lower_E (both_witnesses (hlow hd)).1 α hα,
      uniformUpper_E hu' α hα hd hd1⟩
  refine ⟨1/8192,32,1/268435456,67108928,1/1048576,1/1048576,d₀,
    by norm_num,by norm_num,by norm_num,by norm_num,by norm_num,by norm_num,
    two_codes,hu',hb,?_⟩
  intro d hd
  have hw := both_witnesses (hlow hd)
  refine ⟨hw.1,hw.2,?_⟩
  exact alphabetSupremum_bounds (fun A hA => hb (Fin A) (by simpa using hA) d hd)

end FiniteCircle

theorem finiteCircle_fullMain : FiniteCircle.FullMain := FiniteCircle.full_main

end OAI

-- ---- mission target ----
open OAI

namespace OAI
theorem _root_.solution : FiniteCircle.FullMain := by
  first
    | exact OAI.finiteCircle_fullMain
    | (apply OAI.finiteCircle_fullMain <;> assumption)
    | (intros; apply OAI.finiteCircle_fullMain <;> assumption)
end OAI
