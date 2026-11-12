-- Prove2me | solution 2 for Puder.tendsto_card_primitivityRank_eq_rpow_rhoStair
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T20:52:06.001029+00:00
-- url     : https://prove2.me/submissions/aba77fa5-b0f2-4d6d-88e7-cc18e2d5ef28

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvPuder
import Theorems.Thm_Puder_isAlgExt_zpowers_of_mem_crit
import Theorems.Thm_Puder_setOf_isAlgExt_finite_of_fg
import Theorems.Thm_Puder_limsup_sum_ncard_crit_rpow_le_rhoStair
import Definitions.Def_StrongConvPuderAlg
import Definitions.Def_StrongConvPuderCore
import Theorems.Thm_Puder_isFreeFactor_of_le_of_mem_of_traverses
import Theorems.Thm_Puder_isPrimitiveIn_of_ncard_traverses_eq_one
import Theorems.Thm_Puder_tendsto_card_primitivityRank_eq_rpow_of_sqrt_lt

namespace Puder.Q284Fin

/-- `Crit(w)` is finite: critical subgroups are algebraic extensions of `⟨w⟩` (Claim 3.1), of which there are
finitely many (Takahasi). -/
theorem crit_finite {d : ℕ} (w : FreeGroup (Fin d)) : (Puder.Crit w).Finite :=
  (Puder.setOf_isAlgExt_finite_of_fg (Subgroup.zpowers w)
      ⟨{w}, by rw [Finset.coe_singleton, ← Subgroup.zpowers_eq_closure]⟩).subset
    fun _ hJ => Puder.isAlgExt_zpowers_of_mem_crit hJ

end Puder.Q284Fin


section
open Filter Topology
namespace Puder.T85
/-! Puder Theorem 8.5, clause m ∈ {1, …, k}, from Corollary 4.5, the finiteness of Crit (Claim 3.1 and
Takahasi), the case 2m - 1 > √(2k-1), and π = m for the two words x₀²x₁²⋯ and x₀³x₁²⋯ (proved directly). -/
/-- The endpoint of the walk spelled by a letter sequence. -/
noncomputable def word {k t : ℕ} (i : Fin t → Fin k ⊕ Fin k) : FreeGroup (Fin k) :=
  StrongConv.wordFree (List.ofFn fun j => some (i j))

/-- `b_{k,m}(t)`: the number of words of length `t` with primitivity rank `m`. -/
noncomputable def b (k m t : ℕ) : ℝ :=
  ((Finset.univ.filter fun i : Fin t → Fin k ⊕ Fin k => primitivityRank (word i) = m).card : ℝ)

/-- `x_0^2 x_1^2 ⋯ x_{m-1}^2` spelled letter by letter (length `2m`). -/
def sEven (k m : ℕ) (hm : m ≤ k) : Fin (2 * m) → Fin k ⊕ Fin k :=
  fun j => Sum.inl ⟨(j : ℕ) / 2, by omega⟩

/-- `x_0^3 x_1^2 ⋯ x_{m-1}^2` spelled letter by letter (length `2m + 1`), for `1 ≤ m`. -/
def sOdd (k m : ℕ) (hm : m ≤ k) (hm1 : 1 ≤ m) : Fin (2 * m + 1) → Fin k ⊕ Fin k :=
  fun j => Sum.inl ⟨((j : ℕ) - 1) / 2, by omega⟩

end Puder.T85
end

section
namespace Puder.T85.PartX
open FreeGroup
theorem crit_nonempty {k : ℕ} (w : FreeGroup (Fin k)) (m : ℕ) (h : primitivityRank w = m) :
    (Crit w).Nonempty := by
  classical
  have hex : ∃ r : ℕ, ∃ J : Subgroup (FreeGroup (Fin k)), w ∈ J ∧ HasRank J r ∧
      ¬ IsPrimitiveIn J w := by
    by_contra hne
    push Not at hne
    have htop : primitivityRank w = ⊤ := by
      unfold primitivityRank
      simp only [iInf_eq_top]
      intro r hr
      obtain ⟨J, h1, h2, h3⟩ := hr
      exact absurd h3 (not_not.mpr (hne r J h1 h2))
    rw [htop] at h
    exact ENat.top_ne_natCast m h
  have hval : primitivityRank w = (Nat.find hex : ℕ∞) := by
    unfold primitivityRank
    apply le_antisymm
    · exact iInf₂_le (Nat.find hex) (Nat.find_spec hex)
    · exact le_iInf₂ fun r hr => by exact_mod_cast Nat.find_min' hex hr
  obtain ⟨J, hw, hr, hnp⟩ := Nat.find_spec hex
  exact ⟨J, hw, hnp, Nat.find hex, hr, hval.symm⟩

end Puder.T85.PartX
end

section
open Filter Topology
namespace Puder.T85
/-! ## Part X: primitivity ranks (stubs) -/
alias crit_nonempty := Puder.T85.PartX.crit_nonempty

end Puder.T85
end

section
namespace Puder.T85.PartX
open FreeGroup
theorem primitivityRank_le {k : ℕ} (w : FreeGroup (Fin k)) (J : Subgroup (FreeGroup (Fin k)))
    (r : ℕ) (hw : w ∈ J) (hr : HasRank J r) (hnp : ¬ IsPrimitiveIn J w) :
    primitivityRank w ≤ r :=
  iInf₂_le r ⟨J, hw, hr, hnp⟩

theorem word_snoc {k t : ℕ} (i : Fin (t + 1) → Fin k ⊕ Fin k) :
    word i = word (fun j : Fin t => i j.castSucc) *
      StrongConv.wordFree [some (i (Fin.last t))] := by
  unfold word StrongConv.wordFree
  rw [List.ofFn_succ']
  simp [List.concat_eq_append, List.map_append, List.prod_append]

theorem word_zero {k : ℕ} (i : Fin 0 → Fin k ⊕ Fin k) : word i = 1 := by
  simp [word, StrongConv.wordFree]

theorem sEven_succ (k n : ℕ) (h : n + 1 ≤ k) :
    word (sEven k (n + 1) h) = word (sEven k n (by omega)) * (of ⟨n, by omega⟩ * of ⟨n, by omega⟩) := by
  have e1 := word_snoc (t := 2 * n + 1) (sEven k (n + 1) h)
  have e2 := word_snoc (t := 2 * n) (fun j : Fin (2 * n + 1) => sEven k (n + 1) h j.castSucc)
  rw [e1, e2, mul_assoc]
  congr 1
  all_goals
    simp only [StrongConv.wordFree, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, sEven]
    congr 1 <;> exact congrArg FreeGroup.of (Fin.ext (by simp <;> omega))

theorem sOdd_succ (k n : ℕ) (h : n + 1 ≤ k) (h1 : 1 ≤ n) :
    word (sOdd k (n + 1) h (by omega)) =
      word (sOdd k n (by omega) h1) * (of ⟨n, by omega⟩ * of ⟨n, by omega⟩) := by
  have e1 := word_snoc (t := 2 * n + 1 + 1) (sOdd k (n + 1) h (by omega))
  have e2 := word_snoc (t := 2 * n + 1) (fun j : Fin (2 * n + 1 + 1) => sOdd k (n + 1) h (by omega) j.castSucc)
  rw [e1, e2, mul_assoc]
  congr 1
  all_goals
    simp only [StrongConv.wordFree, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, sOdd]
    congr 1 <;> exact congrArg FreeGroup.of (Fin.ext (by simp <;> omega))

theorem sOdd_one (k : ℕ) (h : 1 ≤ k) :
    word (sOdd k 1 h le_rfl) = (of ⟨0, by omega⟩) ^ 3 := by
  rw [word_snoc, word_snoc, word_snoc, word_zero]
  simp only [StrongConv.wordFree, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, one_mul, sOdd, pow_succ, pow_zero]
  rfl


/-! ## π = m for the two words, proved directly -/

/-- A positive word: the letters `f 0, f 1, …`, all with exponent `+1`. -/
def posW {k t : ℕ} (f : Fin t → Fin k) : List (Fin k × Bool) := List.ofFn fun j => (f j, true)

theorem posW_pos {k t : ℕ} (f : Fin t → Fin k) : ∀ a ∈ posW f, a.2 = true := by
  intro a ha
  simp only [posW, List.mem_ofFn] at ha
  obtain ⟨j, rfl⟩ := ha
  rfl

theorem reduce_pos {k : ℕ} (L : List (Fin k × Bool)) (h : ∀ a ∈ L, a.2 = true) : reduce L = L := by
  rw [← isReduced_iff_reduce_eq]
  unfold FreeGroup.IsReduced
  induction L with
  | nil => exact List.IsChain.nil
  | cons a L ih =>
    cases L with
    | nil => exact List.IsChain.singleton a
    | cons b L =>
      refine List.IsChain.cons_cons (fun _ => ?_) (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))
      rw [h a (by simp), h b (by simp)]

theorem toWord_mk_posW {k t : ℕ} (f : Fin t → Fin k) : (mk (posW f)).toWord = posW f := by
  rw [toWord_mk, reduce_pos _ (posW_pos f)]

theorem word_inl {k t : ℕ} (f : Fin t → Fin k) : word (fun j => Sum.inl (f j)) = mk (posW f) := by
  unfold word StrongConv.wordFree posW
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.map_cons, List.prod_cons, ih (fun j => f j.succ),
      ← List.singleton_append, ← mul_mk]
    rfl

theorem mk_take_succ {k : ℕ} (L : List (Fin k × Bool)) (i : ℕ) (h : i < L.length) :
    mk (L.take (i + 1)) = mk (L.take i) * mk [L[i]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, mul_mk]
  rfl

theorem mk_single_pos {k : ℕ} (a : Fin k × Bool) (h : a.2 = true) : mk [a] = of a.1 := by
  obtain ⟨x, b⟩ := a
  simp only at h
  subst h
  rfl

theorem traverses_iff_pos {k : ℕ} (J : Subgroup (FreeGroup (Fin k))) (w : FreeGroup (Fin k))
    (L : List (Fin k × Bool)) (hL : w.toWord = L) (hpos : ∀ a ∈ L, a.2 = true)
    (i : ℕ) (g : FreeGroup (Fin k)) (x : Fin k) :
    Traverses J w i g x ↔ ∃ h : i < L.length, L[i].1 = x ∧ mk (L.take i) * g⁻¹ ∈ J := by
  constructor
  · rintro ⟨p, s, b, hw, hp, hJ⟩
    rw [hL] at hw
    subst hw
    have hb : b = true := hpos (x, b) (by simp)
    subst hb hp
    refine ⟨by simp, by simp, ?_⟩
    simpa using hJ
  · rintro ⟨h, hx, hJ⟩
    refine ⟨L.take i, L.drop (i + 1), true, ?_, by simp; omega, by simpa using hJ⟩
    rw [hL]
    have e : L[i] = (x, true) := Prod.ext hx (hpos _ (List.getElem_mem h))
    conv_lhs => rw [← List.take_append_drop i L, List.drop_eq_getElem_cons h, e]

end Puder.T85.PartX
end

section
namespace Puder.T85.PartX
open FreeGroup

theorem mem_of_mul_mem {k : ℕ} {J : Subgroup (FreeGroup (Fin k))} {P y : FreeGroup (Fin k)}
    (hP : P ∈ J) (h : P * y ∈ J) : y ∈ J :=
  (Subgroup.mul_mem_cancel_left J hP).1 h

theorem mem_of_conj_mem {k : ℕ} {J : Subgroup (FreeGroup (Fin k))} {P y : FreeGroup (Fin k)}
    (hP : P ∈ J) (h : P * y * P⁻¹ ∈ J) : y ∈ J := by
  have : y = P⁻¹ * (P * y * P⁻¹) * P := by group
  rw [this]
  exact mul_mem (mul_mem (inv_mem hP) h) hP

/-- A letter whose occurrences are at most two consecutive positions `i, i + 1`, read from a coset
`J`-prefix, lies in `J` when `w` is not primitive in `J`. -/
theorem of_mem_two {k : ℕ} (J : Subgroup (FreeGroup (Fin k))) (hJ : J.FG) (w : FreeGroup (Fin k))
    (hw : w ∈ J) (hnp : ¬ IsPrimitiveIn J w) (L : List (Fin k × Bool)) (hL : w.toWord = L)
    (hpos : ∀ a ∈ L, a.2 = true) (i : ℕ) (hi : i < L.length)
    (hblock : ∀ j (hj : j < L.length), L[j].1 = L[i].1 → j = i ∨ j = i + 1)
    (hpre : mk (L.take i) ∈ J) : of L[i].1 ∈ J := by
  by_contra hx
  apply hnp
  apply isPrimitiveIn_of_ncard_traverses_eq_one J hJ w hw 1 L[i].1
  have : {j | Traverses J w j 1 L[i].1} = {i} := by
    ext j
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, traverses_iff_pos J w L hL hpos, inv_one,
      mul_one]
    constructor
    · rintro ⟨hj, hjx, hjJ⟩
      rcases hblock j hj hjx with rfl | rfl
      · rfl
      · exfalso
        apply hx
        rw [mk_take_succ L i hi, mk_single_pos _ (hpos _ (List.getElem_mem hi))] at hjJ
        exact mem_of_mul_mem hpre hjJ
    · rintro rfl
      exact ⟨hi, rfl, hpre⟩
  rw [this, Set.ncard_singleton]

/-- The same for a block of three consecutive occurrences. -/
theorem of_mem_three {k : ℕ} (J : Subgroup (FreeGroup (Fin k))) (hJ : J.FG) (w : FreeGroup (Fin k))
    (hw : w ∈ J) (hnp : ¬ IsPrimitiveIn J w) (L : List (Fin k × Bool)) (hL : w.toWord = L)
    (hpos : ∀ a ∈ L, a.2 = true) (i : ℕ) (hi : i + 2 < L.length)
    (h1 : L[i + 1].1 = L[i].1)
    (hblock : ∀ j (hj : j < L.length), L[j].1 = L[i].1 → j = i ∨ j = i + 1 ∨ j = i + 2)
    (hpre : mk (L.take i) ∈ J) : of L[i].1 ∈ J := by
  by_contra hx
  apply hnp
  set x := L[i].1 with hxdef
  set P := mk (L.take i) with hPdef
  have e1 : mk (L.take (i + 1)) = P * of x := by
    rw [mk_take_succ L i (by omega), mk_single_pos _ (hpos _ (List.getElem_mem _))]
  have e2 : mk (L.take (i + 2)) = P * of x * of x := by
    rw [mk_take_succ L (i + 1) (by omega), mk_single_pos _ (hpos _ (List.getElem_mem _)), e1, h1]
  by_cases hx2 : of x * of x ∈ J
  · apply isPrimitiveIn_of_ncard_traverses_eq_one J hJ w hw (P * of x) x
    have : {j | Traverses J w j (P * of x) x} = {i + 1} := by
      ext j
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, traverses_iff_pos J w L hL hpos]
      constructor
      · rintro ⟨hj, hjx, hjJ⟩
        rcases hblock j hj hjx with rfl | rfl | rfl
        · exfalso
          apply hx
          have : P * (P * of x)⁻¹ = P * (of x)⁻¹ * P⁻¹ := by group
          rw [this] at hjJ
          exact inv_mem_iff.1 (mem_of_conj_mem hpre hjJ)
        · rfl
        · exfalso
          apply hx
          rw [e2] at hjJ
          have : P * of x * of x * (P * of x)⁻¹ = P * of x * P⁻¹ := by group
          rw [this] at hjJ
          exact mem_of_conj_mem hpre hjJ
      · rintro rfl
        refine ⟨by omega, h1, ?_⟩
        rw [e1, mul_inv_cancel]
        exact one_mem J
    rw [this, Set.ncard_singleton]
  · apply isPrimitiveIn_of_ncard_traverses_eq_one J hJ w hw 1 x
    have : {j | Traverses J w j 1 x} = {i} := by
      ext j
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, traverses_iff_pos J w L hL hpos, inv_one,
        mul_one]
      constructor
      · rintro ⟨hj, hjx, hjJ⟩
        rcases hblock j hj hjx with rfl | rfl | rfl
        · rfl
        · exfalso
          apply hx
          rw [e1] at hjJ
          exact mem_of_mul_mem hpre hjJ
        · exfalso
          apply hx2
          rw [e2, mul_assoc] at hjJ
          exact mem_of_mul_mem hpre hjJ
      · rintro rfl
        exact ⟨by omega, rfl, hpre⟩
    rw [this, Set.ncard_singleton]

/-- Every prefix of `w` lies in `J`, when each letter occurrence either repeats the previous letter
or starts a block of two or three occurrences of its letter. -/
theorem pre_mem {k : ℕ} (J : Subgroup (FreeGroup (Fin k))) (hJ : J.FG) (w : FreeGroup (Fin k))
    (hw : w ∈ J) (hnp : ¬ IsPrimitiveIn J w) (L : List (Fin k × Bool)) (hL : w.toWord = L)
    (hpos : ∀ a ∈ L, a.2 = true)
    (hcase : ∀ i (hi : i < L.length),
      (∃ i' : ℕ, ∃ h' : i' < L.length, i = i' + 1 ∧ L[i'].1 = L[i].1) ∨
      (∀ j (hj : j < L.length), L[j].1 = L[i].1 → j = i ∨ j = i + 1) ∨
      (∃ h2 : i + 2 < L.length, L[i + 1].1 = L[i].1 ∧
        ∀ j (hj : j < L.length), L[j].1 = L[i].1 → j = i ∨ j = i + 1 ∨ j = i + 2)) :
    ∀ i, i ≤ L.length → mk (L.take i) ∈ J := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    cases i with
    | zero => exact one_mem J
    | succ i =>
      have hpre := ih i (by omega) (by omega)
      have hlt : i < L.length := by omega
      rw [mk_take_succ L i hlt, mk_single_pos _ (hpos _ (List.getElem_mem hlt))]
      refine mul_mem hpre ?_
      rcases hcase i hlt with ⟨i', h', rfl, he⟩ | hb | ⟨h2, h1, hb⟩
      · have hp' := ih i' (by omega) (by omega)
        have := mk_take_succ L i' h'
        rw [mk_single_pos _ (hpos _ (List.getElem_mem h')), he] at this
        rw [this] at hpre
        exact mem_of_mul_mem hp' hpre
      · exact of_mem_two J hJ w hw hnp L hL hpos i hlt hb hpre
      · exact of_mem_three J hJ w hw hnp L hL hpos i h2 h1 hb hpre

theorem letter_mem {k : ℕ} (J : Subgroup (FreeGroup (Fin k))) (L : List (Fin k × Bool))
    (hpos : ∀ a ∈ L, a.2 = true) (h : ∀ i, i ≤ L.length → mk (L.take i) ∈ J)
    (i : ℕ) (hi : i < L.length) : of L[i].1 ∈ J := by
  have := h (i + 1) hi
  rw [mk_take_succ L i hi, mk_single_pos _ (hpos _ (List.getElem_mem hi))] at this
  exact mem_of_mul_mem (h i hi.le) this

end Puder.T85.PartX
end

section
namespace Puder.T85.PartX
open FreeGroup

/-- The subgroup generated by the first `m` generators. -/
def Hm (k m : ℕ) : Subgroup (FreeGroup (Fin k)) := Subgroup.closure (of '' {j : Fin k | (j : ℕ) < m})

theorem letters_lt_of_mem {k m : ℕ} {h : FreeGroup (Fin k)} (hh : h ∈ Hm k m) :
    ∀ a ∈ h.toWord, (a.1 : ℕ) < m := by
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    intro a ha
    rw [toWord_of, List.mem_singleton] at ha
    subst ha
    exact hj
  | one => simp
  | mul x y _ _ hx hy =>
    intro a ha
    rw [toWord_mul] at ha
    rcases List.mem_append.1 (reduce.red.sublist.subset ha) with h | h
    · exact hx a h
    · exact hy a h
  | inv x _ hx =>
    intro a ha
    rw [toWord_inv] at ha
    simp only [invRev, List.mem_reverse, List.mem_map] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    exact hx b hb

theorem mem_of_letters_lt {k m : ℕ} (L : List (Fin k × Bool)) (hL : ∀ a ∈ L, (a.1 : ℕ) < m) :
    mk L ∈ Hm k m := by
  induction L with
  | nil => exact one_mem _
  | cons a L ih =>
    rw [← List.singleton_append, ← mul_mk]
    refine mul_mem ?_ (ih fun b hb => hL b (List.mem_cons_of_mem _ hb))
    have ha : of a.1 ∈ Hm k m := Subgroup.subset_closure ⟨a.1, hL a (by simp), rfl⟩
    obtain ⟨x, b⟩ := a
    cases b
    · have : mk [(x, false)] = (of x)⁻¹ := by rw [of, inv_mk]; rfl
      rw [this]
      exact inv_mem ha
    · exact ha

theorem mem_Hm_iff {k m : ℕ} (g : FreeGroup (Fin k)) : g ∈ Hm k m ↔ ∀ a ∈ g.toWord, (a.1 : ℕ) < m :=
  ⟨letters_lt_of_mem, fun h => by rw [← mk_toWord (x := g)]; exact mem_of_letters_lt _ h⟩

/-- The inclusion `F_m → F_k`. -/
noncomputable def incl {k m : ℕ} (hm : m ≤ k) : FreeGroup (Fin m) →* FreeGroup (Fin k) :=
  FreeGroup.map (Fin.castLE hm)

theorem incl_injective {k m : ℕ} (hm : m ≤ k) : Function.Injective (incl hm) :=
  FreeGroup.map_injective (Fin.castLE_injective hm)

theorem incl_range {k m : ℕ} (hm : m ≤ k) : (incl hm).range = Hm k m := by
  rw [MonoidHom.range_eq_map, ← FreeGroup.closure_range_of, MonoidHom.map_closure, Hm]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
    exact ⟨Fin.castLE hm j, j.isLt, by simp [incl]⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨_, ⟨⟨j, hj⟩, rfl⟩, by simp [incl]⟩

/-- `F_m ≃ Hm k m`. -/
noncomputable def E {k m : ℕ} (hm : m ≤ k) : FreeGroup (Fin m) ≃* Hm k m :=
  (MonoidHom.ofInjective (incl_injective hm)).trans (MulEquiv.subgroupCongr (incl_range hm))

theorem E_apply {k m : ℕ} (hm : m ≤ k) (x : FreeGroup (Fin m)) :
    (E hm x : FreeGroup (Fin k)) = incl hm x := rfl

/-- The basis `x_0, …, x_{m-1}` of `Hm k m`. -/
noncomputable def bx {k m : ℕ} (hm : m ≤ k) : FreeGroupBasis (Fin m) (Hm k m) :=
  FreeGroupBasis.ofRepr (E hm).symm

theorem hasRank_Hm {k m : ℕ} (hm : m ≤ k) : HasRank (Hm k m) m := ⟨bx hm⟩

theorem bx_lift_E {k m : ℕ} (hm : m ≤ k) {G : Type} [Group G] (F : Fin m → G)
    (x : FreeGroup (Fin m)) : (bx hm).lift F (E hm x) = FreeGroup.lift F x := by
  show FreeGroup.lift F ((E hm).symm (E hm x)) = _
  rw [MulEquiv.symm_apply_apply]

/-! Basis restriction (as in the accepted Claim 3.1 proof). -/
open Classical in
noncomputable def BB {d : ℕ} {ι : Type} {J : Subgroup (FreeGroup (Fin d))} (b : FreeGroupBasis ι J)
    (S : Set ι) : FreeGroupBasis ({i // i ∈ S} ⊕ {i // i ∉ S}) J :=
  b.reindex (Equiv.sumCompl (· ∈ S)).symm

noncomputable def ff {d : ℕ} {ι : Type} {J : Subgroup (FreeGroup (Fin d))} (b : FreeGroupBasis ι J)
    (S : Set ι) : FreeGroup {i // i ∈ S} →* FreeGroup (Fin d) :=
  J.subtype.comp ((BB b S).repr.symm.toMonoidHom.comp (FreeGroup.map Sum.inl))

theorem ff_apply {d : ℕ} {ι : Type} {J : Subgroup (FreeGroup (Fin d))} (b : FreeGroupBasis ι J)
    (S : Set ι) (x : FreeGroup {i // i ∈ S}) :
    ff b S x = ((BB b S).repr.symm (FreeGroup.map Sum.inl x) : FreeGroup (Fin d)) := rfl

theorem ff_of {d : ℕ} {ι : Type} {J : Subgroup (FreeGroup (Fin d))} (b : FreeGroupBasis ι J)
    (S : Set ι) (s : {i // i ∈ S}) : ff b S (FreeGroup.of s) = (b s : FreeGroup (Fin d)) := by
  rw [ff_apply, FreeGroup.map.of]
  rfl

theorem ff_injective {d : ℕ} {ι : Type} {J : Subgroup (FreeGroup (Fin d))} (b : FreeGroupBasis ι J)
    (S : Set ι) : Function.Injective (ff b S) := by
  intro x y h
  rw [ff_apply, ff_apply] at h
  exact FreeGroup.map_injective Sum.inl_injective
    ((BB b S).repr.symm.injective (Subtype.val_injective h))

theorem ff_range {d : ℕ} {ι : Type} {J : Subgroup (FreeGroup (Fin d))} (b : FreeGroupBasis ι J)
    (S : Set ι) :
    (ff b S).range = Subgroup.closure ((fun i => (b i : FreeGroup (Fin d))) '' S) := by
  rw [MonoidHom.range_eq_map, ← FreeGroup.closure_range_of, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    exact ⟨s.1, s.2, (ff_of b S s).symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨_, ⟨⟨i, hi⟩, rfl⟩, ff_of b S ⟨i, hi⟩⟩

/-- Claim 3.3(4) applied to `Hm k m ≤ J`: `m ≤ rank J`. -/
theorem rank_ge {k m : ℕ} (hm : m ≤ k) (J : Subgroup (FreeGroup (Fin k))) (r : ℕ)
    (hr : HasRank J r) (hle : ∀ j : Fin k, (j : ℕ) < m → of j ∈ J) : m ≤ r := by
  have hHJ : Hm k m ≤ J := by
    rw [Hm, Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    exact hle j hj
  have hff : IsFreeFactor (Hm k m) J := by
    refine isFreeFactor_of_le_of_mem_of_traverses _ J hHJ ?_
    intro g _ hg
    rw [mem_Hm_iff]
    intro a ha
    obtain ⟨i, hi⟩ := List.getElem_of_mem ha
    obtain ⟨hlt, rfl⟩ := hi
    obtain ⟨h, hh, j, hj⟩ := hg i
      (if g.toWord[i].2 then mk (g.toWord.take i) else mk (g.toWord.take i) * (of g.toWord[i].1)⁻¹)
      g.toWord[i].1 ⟨g.toWord.take i, g.toWord.drop (i + 1), g.toWord[i].2, by
        rw [← List.drop_eq_getElem_cons hlt, List.take_append_drop], by simp; omega,
        by rw [mul_inv_cancel]; exact one_mem J⟩
    obtain ⟨p, s, b, hw, -, -⟩ := hj
    exact letters_lt_of_mem hh (g.toWord[i].1, b) (by rw [hw]; simp)
  obtain ⟨ι, b, S, hS⟩ := hff
  obtain ⟨bJ⟩ := hr
  have eι : ι ≃ Fin r := Equiv.ofFreeGroupEquiv (b.repr.symm.trans bJ.repr)
  have : Finite ι := Finite.of_equiv _ eι.symm
  have e1 : FreeGroup {i // i ∈ S} ≃* Hm k m :=
    (MonoidHom.ofInjective (ff_injective b S)).trans
      (MulEquiv.subgroupCongr ((ff_range b S).trans hS.symm))
  have eS : {i // i ∈ S} ≃ Fin m := Equiv.ofFreeGroupEquiv (e1.trans (E hm).symm)
  have h1 := Finite.card_subtype_le (fun i => i ∈ S)
  rw [Nat.card_congr eS, Nat.card_congr eι, Nat.card_fin, Nat.card_fin] at h1
  exact h1

end Puder.T85.PartX
end

section
namespace Puder.T85.PartX
open FreeGroup

theorem fg_of_hasRank {k r : ℕ} {J : Subgroup (FreeGroup (Fin k))} (hr : HasRank J r) : J.FG := by
  obtain ⟨bJ⟩ := hr
  exact (Group.fg_iff_subgroup_fg J).1
    (Group.fg_of_surjective (f := bJ.repr.symm.toMonoidHom) bJ.repr.symm.surjective)

/-- The lower bound `m ≤ π(w)` for a positive word whose letters come in blocks. -/
theorem le_primitivityRank {k m : ℕ} (hm : m ≤ k) (w : FreeGroup (Fin k))
    (L : List (Fin k × Bool)) (hL : w.toWord = L) (hpos : ∀ a ∈ L, a.2 = true)
    (hcase : ∀ i (hi : i < L.length),
      (∃ i' : ℕ, ∃ h' : i' < L.length, i = i' + 1 ∧ L[i'].1 = L[i].1) ∨
      (∀ j (hj : j < L.length), L[j].1 = L[i].1 → j = i ∨ j = i + 1) ∨
      (∃ h2 : i + 2 < L.length, L[i + 1].1 = L[i].1 ∧
        ∀ j (hj : j < L.length), L[j].1 = L[i].1 → j = i ∨ j = i + 1 ∨ j = i + 2))
    (hall : ∀ j : Fin k, (j : ℕ) < m → ∃ i : ℕ, ∃ hi : i < L.length, L[i].1 = j) :
    (m : ℕ∞) ≤ primitivityRank w := by
  unfold primitivityRank
  refine le_iInf₂ fun r hr => ?_
  obtain ⟨J, hwJ, hrJ, hnp⟩ := hr
  have hpre := pre_mem J (fg_of_hasRank hrJ) w hwJ hnp L hL hpos hcase
  exact_mod_cast rank_ge hm J r hrJ fun j hj => by
    obtain ⟨i, hi, he⟩ := hall j hj
    rw [← he]
    exact letter_mem J L hpos hpre i hi

theorem le_primitivityRank_sEven (k m : ℕ) (hm : m ≤ k) :
    (m : ℕ∞) ≤ primitivityRank (word (sEven k m hm)) := by
  let fe : Fin (2 * m) → Fin k := fun j => ⟨(j : ℕ) / 2, by omega⟩
  have hw : word (sEven k m hm) = mk (posW fe) := word_inl fe
  have hlen : (posW fe).length = 2 * m := by simp [posW]
  have hget : ∀ j (hj : j < (posW fe).length), (((posW fe)[j].1 : Fin k) : ℕ) = j / 2 := by
    intro j hj; simp [posW, fe]
  refine le_primitivityRank hm _ (posW fe) (by rw [hw, toWord_mk_posW]) (posW_pos fe) ?_ ?_
  · intro i hi
    rcases Nat.even_or_odd' i with ⟨c, hc | hc⟩
    · right; left
      intro j hj hji
      rw [Fin.ext_iff, hget, hget] at hji
      omega
    · left
      exact ⟨i - 1, by omega, by omega, by rw [Fin.ext_iff, hget, hget]; omega⟩
  · intro j hj
    exact ⟨2 * j, by omega, by rw [Fin.ext_iff, hget]; omega⟩

theorem le_primitivityRank_sOdd (k m : ℕ) (hm : m ≤ k) (hm1 : 1 ≤ m) :
    (m : ℕ∞) ≤ primitivityRank (word (sOdd k m hm hm1)) := by
  let fo : Fin (2 * m + 1) → Fin k := fun j => ⟨((j : ℕ) - 1) / 2, by omega⟩
  have hw : word (sOdd k m hm hm1) = mk (posW fo) := word_inl fo
  have hlen : (posW fo).length = 2 * m + 1 := by simp [posW]
  have hget : ∀ j (hj : j < (posW fo).length), (((posW fo)[j].1 : Fin k) : ℕ) = (j - 1) / 2 := by
    intro j hj; simp only [posW, List.getElem_ofFn, fo]
  refine le_primitivityRank hm _ (posW fo) (by rw [hw, toWord_mk_posW]) (posW_pos fo) ?_ ?_
  · intro i hi
    rcases Nat.even_or_odd' i with ⟨c, hc | hc⟩
    · rcases Nat.eq_zero_or_pos c with h0 | h0
      · right; right
        refine ⟨by omega, by rw [Fin.ext_iff, hget, hget]; omega, ?_⟩
        intro j hj hji
        rw [Fin.ext_iff, hget, hget] at hji
        omega
      · left
        exact ⟨i - 1, by omega, by omega, by rw [Fin.ext_iff, hget, hget]; omega⟩
    · rcases Nat.eq_zero_or_pos c with h0 | h0
      · left
        exact ⟨i - 1, by omega, by omega, by rw [Fin.ext_iff, hget, hget]; omega⟩
      · right; left
        intro j hj hji
        rw [Fin.ext_iff, hget, hget] at hji
        omega
  · intro j hj
    exact ⟨2 * j + 1, by omega, by rw [Fin.ext_iff, hget]; omega⟩

end Puder.T85.PartX
end

section
namespace Puder.T85.PartX
open FreeGroup

theorem incl_posW {k m t : ℕ} (hm : m ≤ k) (f : Fin t → Fin m) :
    incl hm (mk (posW f)) = mk (posW fun j => Fin.castLE hm (f j)) := by
  rw [incl, map.mk]
  congr 1
  simp [posW, List.map_ofFn, Function.comp_def]

theorem incl_sEven (k m : ℕ) (hm : m ≤ k) :
    incl hm (word (sEven m m le_rfl)) = word (sEven k m hm) := by
  rw [show word (sEven m m le_rfl) = mk (posW fun j : Fin (2 * m) => (⟨(j : ℕ) / 2, by omega⟩ : Fin m))
    from word_inl _, incl_posW]
  exact (word_inl _).symm

theorem incl_sOdd (k m : ℕ) (hm : m ≤ k) (hm1 : 1 ≤ m) :
    incl hm (word (sOdd m m le_rfl hm1)) = word (sOdd k m hm hm1) := by
  rw [show word (sOdd m m le_rfl hm1) =
      mk (posW fun j : Fin (2 * m + 1) => (⟨((j : ℕ) - 1) / 2, by omega⟩ : Fin m))
    from word_inl _, incl_posW]
  exact (word_inl _).symm

theorem sEven_mem (k m : ℕ) (hm : m ≤ k) : word (sEven k m hm) ∈ Hm k m := by
  rw [← incl_range hm, ← incl_sEven]; exact ⟨_, rfl⟩

theorem sOdd_mem (k m : ℕ) (hm : m ≤ k) (hm1 : 1 ≤ m) : word (sOdd k m hm hm1) ∈ Hm k m := by
  rw [← incl_range hm, ← incl_sOdd]; exact ⟨_, rfl⟩

theorem lift_sEven {G : Type} [Group G] (k : ℕ) (F : Fin k → G) (n : ℕ) (h : n ≤ k) :
    FreeGroup.lift F (word (sEven k n h)) = (List.ofFn fun j : Fin n => F (Fin.castLE h j) ^ 2).prod := by
  induction n with
  | zero =>
    have : word (sEven k 0 h) = 1 := word_zero _
    rw [this]; simp
  | succ n ih =>
    rw [sEven_succ k n h, _root_.map_mul, ih (by omega), List.ofFn_succ', List.concat_eq_append,
      List.prod_append]
    simp [sq]
    rfl

theorem lift_sOdd {G : Type} [Group G] (k : ℕ) (F : Fin k → G) (n : ℕ) (h : n + 1 ≤ k) :
    FreeGroup.lift F (word (sOdd k (n + 1) h (by omega))) =
      F ⟨0, by omega⟩ ^ 3 * (List.ofFn fun j : Fin n => F ⟨(j : ℕ) + 1, by omega⟩ ^ 2).prod := by
  induction n with
  | zero =>
    rw [sOdd_one k h]; simp
  | succ n ih =>
    rw [sOdd_succ k (n + 1) h (by omega), _root_.map_mul, ih (by omega), List.ofFn_succ',
      List.concat_eq_append, List.prod_append]
    simp [sq, mul_assoc]

/-! The dihedral group of order 6. -/
abbrev G3 := DihedralGroup 3

def rot : G3 → Bool
  | DihedralGroup.r _ => true
  | DihedralGroup.sr _ => false

theorem rot_sq : ∀ g : G3, rot (g ^ 2) = true := by decide

theorem rot_mul : ∀ a b : G3, rot a = true → rot b = true → rot (a * b) = true := by decide

theorem rot_prod (l : List G3) (h : ∀ a ∈ l, rot a = true) : rot l.prod = true := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.prod_cons]
    exact rot_mul _ _ (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

theorem lift_apply_basis {H' : Type} [Group H'] {ι : Type} {G : Type} [Group G]
    (b : FreeGroupBasis ι H') (f : ι → G) (i : ι) : b.lift f (b i) = f i := by
  show FreeGroup.lift f (b.repr (b i)) = f i
  rw [FreeGroupBasis.repr_apply_coe, FreeGroup.lift_apply_of]

theorem lift_symm_eq {H' : Type} [Group H'] {ι : Type} {G : Type} [Group G]
    (b : FreeGroupBasis ι H') (φ : H' →* G) : b.lift (fun i => φ (b i)) = φ :=
  b.lift.apply_symm_apply φ

theorem not_prim_sEven (k m : ℕ) (hm : m ≤ k) : ¬ IsPrimitiveIn (Hm k m) (word (sEven k m hm)) := by
  rintro ⟨ι, b, i₀, hb⟩
  classical
  let φ : Hm k m →* G3 := b.lift fun i => if i = i₀ then DihedralGroup.sr 0 else 1
  have h1 : φ (b i₀) = DihedralGroup.sr 0 := by
    show b.lift _ (b i₀) = _
    rw [lift_apply_basis, if_pos rfl]
  have h2 : b i₀ = E hm (word (sEven m m le_rfl)) := Subtype.ext (by rw [hb, E_apply, incl_sEven])
  rw [h2, ← lift_symm_eq (bx hm) φ, bx_lift_E, lift_sEven] at h1
  have : rot (DihedralGroup.sr 0 : G3) = true := by
    rw [← h1]
    refine rot_prod _ fun a ha => ?_
    simp only [List.mem_ofFn] at ha
    obtain ⟨j, rfl⟩ := ha
    exact rot_sq _
  exact absurd this (by decide)

/-! Counting `S₃`-points for `x_0^3 x_1^2 ⋯ x_{m-1}^2`. -/
theorem card_fiber_eq {H' : Type} [Group H'] {ι κ : Type} [Fintype κ] [DecidableEq κ]
    {G : Type} [Group G] [Fintype G] [DecidableEq G]
    (b : FreeGroupBasis ι H') (bx : FreeGroupBasis κ H') (i₀ : ι) (a : G) :
    (Finset.univ.filter fun F : κ → G => bx.lift F (b i₀) = 1).card =
    (Finset.univ.filter fun F : κ → G => bx.lift F (b i₀) = a).card := by
  classical
  let Ψ : (κ → G) ≃ (ι → G) := bx.lift.trans b.lift.symm
  have key : ∀ F, bx.lift F (b i₀) = Ψ F i₀ := fun F => rfl
  let e : (κ → G) ≃ (κ → G) := Ψ.trans ((Equiv.mulLeft (Pi.mulSingle i₀ a)).trans Ψ.symm)
  have he : ∀ F, Ψ (e F) = Pi.mulSingle i₀ a * Ψ F := fun F => by simp [e]
  refine Finset.card_equiv e fun F => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, key, he, Pi.mul_apply,
    Pi.mulSingle_eq_same]
  exact ⟨fun h => by rw [h, mul_one], fun h => mul_eq_left.1 h⟩

def Q3 {n : ℕ} (f : Fin n → G3) : G3 := (List.ofFn fun j => f j ^ 2).prod

def N3 (n : ℕ) (g : G3) : ℕ := (Finset.univ.filter fun f : Fin n → G3 => Q3 f = g).card

def α3 : G3 → ℤ
  | DihedralGroup.r _ => 1
  | DihedralGroup.sr _ => 0

def β3 : G3 → ℤ
  | DihedralGroup.r i => if i = 0 then 2 else -1
  | DihedralGroup.sr _ => 0

theorem sum_cons {n : ℕ} (φ : (Fin (n + 1) → G3) → ℕ) :
    ∑ F, φ F = ∑ h : G3, ∑ f : Fin n → G3, φ (Fin.cons h f) := by
  rw [← (Fin.consEquiv fun _ => G3).sum_comp, Fintype.sum_prod_type]
  rfl

theorem N3_succ (n : ℕ) (g : G3) : N3 (n + 1) g = ∑ h : G3, N3 n ((h ^ 2)⁻¹ * g) := by
  unfold N3
  simp only [Finset.card_filter]
  rw [sum_cons]
  refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun f _ => ?_
  have : Q3 (Fin.cons h f : Fin (n + 1) → G3) = h ^ 2 * Q3 f := by
    simp [Q3, List.ofFn_succ]
  simp only [this, eq_inv_mul_iff_mul_eq]

theorem N3_zero (g : G3) : N3 0 g = if g = 1 then 1 else 0 := by
  unfold N3
  rw [Finset.card_filter, Fintype.sum_unique]
  simp [Q3, eq_comm]

theorem hα : ∀ g : G3, ∑ h : G3, α3 ((h ^ 2)⁻¹ * g) = 6 * α3 g := by decide
theorem hβ : ∀ g : G3, ∑ h : G3, β3 ((h ^ 2)⁻¹ * g) = 3 * β3 g := by decide
theorem h0 : ∀ g : G3, 3 * ((if g = 1 then 1 else 0 : ℕ) : ℤ) = α3 g + β3 g := by decide

theorem N3_formula (n : ℕ) : ∀ g : G3, 3 * (N3 n g : ℤ) = 6 ^ n * α3 g + 3 ^ n * β3 g := by
  induction n with
  | zero => intro g; rw [N3_zero, h0]; ring
  | succ n ih =>
    intro g
    rw [N3_succ]
    push_cast
    rw [Finset.mul_sum]
    simp only [ih, Finset.sum_add_distrib, ← Finset.mul_sum, hα, hβ]
    ring

/-- The number of `S₃`-points of `x_0^3 x_1^2 ⋯ x_n^2` with value `a`. -/
def C3 (n : ℕ) (a : G3) : ℕ :=
  (Finset.univ.filter fun F : Fin (n + 1) → G3 =>
    F ⟨0, by omega⟩ ^ 3 * (List.ofFn fun j : Fin n => F ⟨(j : ℕ) + 1, by omega⟩ ^ 2).prod = a).card

theorem C3_eq (n : ℕ) (a : G3) : C3 n a = ∑ h : G3, N3 n ((h ^ 3)⁻¹ * a) := by
  unfold C3 N3
  simp only [Finset.card_filter]
  rw [sum_cons]
  refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun f _ => ?_
  have : (Fin.cons h f : Fin (n + 1) → G3) ⟨0, by omega⟩ ^ 3 *
      (List.ofFn fun j : Fin n => (Fin.cons h f : Fin (n + 1) → G3) ⟨(j : ℕ) + 1, by omega⟩ ^ 2).prod
      = h ^ 3 * Q3 f := rfl
  simp only [this, eq_inv_mul_iff_mul_eq]

theorem hc1 : ∑ h : G3, α3 ((h ^ 3)⁻¹ * 1) = 3 ∧ ∑ h : G3, β3 ((h ^ 3)⁻¹ * 1) = 6 ∧
    ∑ h : G3, α3 ((h ^ 3)⁻¹ * DihedralGroup.r 1) = 3 ∧
    ∑ h : G3, β3 ((h ^ 3)⁻¹ * DihedralGroup.r 1) = -3 := by decide

theorem C3_ne (n : ℕ) : C3 n 1 ≠ C3 n (DihedralGroup.r 1) := by
  intro h
  have e : ∀ a : G3, 3 * (C3 n a : ℤ) = 6 ^ n * ∑ h : G3, α3 ((h ^ 3)⁻¹ * a) +
      3 ^ n * ∑ h : G3, β3 ((h ^ 3)⁻¹ * a) := by
    intro a
    rw [C3_eq]
    push_cast
    rw [Finset.mul_sum]
    simp only [N3_formula, Finset.sum_add_distrib, ← Finset.mul_sum]
  have e1 := e 1
  have e2 := e (DihedralGroup.r 1)
  obtain ⟨a1, a2, a3, a4⟩ := hc1
  rw [a1, a2] at e1
  rw [a3, a4] at e2
  rw [h] at e1
  have : (0 : ℤ) < 3 ^ n := by positivity
  linarith

theorem not_prim_sOdd (k n : ℕ) (hm : n + 1 ≤ k) :
    ¬ IsPrimitiveIn (Hm k (n + 1)) (word (sOdd k (n + 1) hm (by omega))) := by
  rintro ⟨ι, b, i₀, hb⟩
  classical
  have h2 : b i₀ = E hm (word (sOdd (n + 1) (n + 1) le_rfl (by omega))) :=
    Subtype.ext (by rw [hb, E_apply, incl_sOdd])
  have := card_fiber_eq b (bx hm) i₀ (DihedralGroup.r 1 : G3)
  simp only [h2, bx_lift_E, lift_sOdd] at this
  exact C3_ne n this

end Puder.T85.PartX
end

section
namespace Puder.T85.PartX
open FreeGroup

theorem primitivityRank_sEven (k m : ℕ) (hm : m ≤ k) (_hm1 : 1 ≤ m) :
    primitivityRank (word (sEven k m hm)) = m :=
  le_antisymm
    (primitivityRank_le _ (Hm k m) m (sEven_mem k m hm) (hasRank_Hm hm) (not_prim_sEven k m hm))
    (le_primitivityRank_sEven k m hm)

end Puder.T85.PartX
end

section
open Filter Topology
namespace Puder.T85
alias primitivityRank_sEven := Puder.T85.PartX.primitivityRank_sEven

end Puder.T85
end

section
namespace Puder.T85.PartX
open FreeGroup
theorem primitivityRank_sOdd (k m : ℕ) (hm : m ≤ k) (hm1 : 1 ≤ m) :
    primitivityRank (word (sOdd k m hm hm1)) = m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  exact le_antisymm
    (primitivityRank_le _ (Hm k (n + 1)) (n + 1) (sOdd_mem k (n + 1) hm hm1) (hasRank_Hm hm)
      (not_prim_sOdd k n hm))
    (le_primitivityRank_sOdd k (n + 1) hm hm1)

end Puder.T85.PartX
end

section
open Filter Topology
namespace Puder.T85
alias primitivityRank_sOdd := Puder.T85.PartX.primitivityRank_sOdd

end Puder.T85
end

section
open Filter Topology
namespace Puder.T85.PartY
open Finset
variable {k : ℕ}
/-! q218 Part Y: the counting bounds and the limit argument for Puder Theorem 8.5.
The Dyck-word machinery (`pp` … `card_G_ge`) and `four_pow_le_catalan` are copied from q216's
`PartS6B` / `PartS6A`. -/
/-- One step of free reduction with a stack (the reversed reduced word): a letter equal to the
inverse of the top pops it, any other letter is pushed. -/
def pp (s : List (Fin k ⊕ Fin k)) (x : Fin k ⊕ Fin k) : List (Fin k ⊕ Fin k) :=
  if s.head? = some x.swap then s.tail else x :: s

/-- Dyck-structured words whose top-level blocks never start with the forbidden letter `f`:
`a · u · a⁻¹ · v` with `a ≠ f`, `u` forbidding `a⁻¹`, `v` forbidding `f`. -/
inductive Good : (Fin k ⊕ Fin k) → List (Fin k ⊕ Fin k) → Prop
  | nil (f : Fin k ⊕ Fin k) : Good f []
  | cons {f a : Fin k ⊕ Fin k} {u v : List (Fin k ⊕ Fin k)} :
      a ≠ f → Good a.swap u → Good f v → Good f (a :: (u ++ a.swap :: v))

theorem pp_push {s : List (Fin k ⊕ Fin k)} {f a : Fin k ⊕ Fin k}
    (hs : s = [] ∨ s.head? = some f.swap) (ha : a ≠ f) : pp s a = a :: s := by
  unfold pp
  rw [if_neg]
  intro h
  rcases hs with rfl | hs
  · simp at h
  · rw [hs] at h
    apply ha
    have := congrArg Sum.swap (Option.some.inj h)
    simpa using this.symm

theorem pp_pop (s : List (Fin k ⊕ Fin k)) (a : Fin k ⊕ Fin k) : pp (a :: s) a.swap = s := by
  simp [pp]

theorem pp_nil (a : Fin k ⊕ Fin k) : pp [] a = [a] := by
  simp [pp]

theorem foldl_good {f : Fin k ⊕ Fin k} {t : List (Fin k ⊕ Fin k)} (h : Good f t) :
    ∀ s : List (Fin k ⊕ Fin k), (s = [] ∨ s.head? = some f.swap) → t.foldl pp s = s := by
  induction h with
  | nil f => intro s _; rfl
  | @cons f a u v ha hu hv ihu ihv =>
    intro s hs
    rw [List.foldl_cons, pp_push hs ha, List.foldl_append, ihu (a :: s) (Or.inr (by simp)),
      List.foldl_cons, pp_pop, ihv s hs]

theorem foldl_take_good {f : Fin k ⊕ Fin k} {t : List (Fin k ⊕ Fin k)} (h : Good f t) :
    ∀ s : List (Fin k ⊕ Fin k), (s = [] ∨ s.head? = some f.swap) →
      ∀ m, ∃ r, (t.take m).foldl pp s = r ++ s := by
  induction h with
  | nil f => intro s _ m; exact ⟨[], by simp⟩
  | @cons f a u v ha hu hv ihu ihv =>
    intro s hs m
    cases m with
    | zero => exact ⟨[], by simp⟩
    | succ m =>
      rw [List.take_succ_cons, List.foldl_cons, pp_push hs ha, List.take_append,
        List.foldl_append]
      obtain ⟨r1, hr1⟩ := ihu (a :: s) (Or.inr (by simp)) m
      rcases Nat.eq_zero_or_pos (m - u.length) with h0 | h0
      · rw [h0, hr1]
        exact ⟨r1 ++ [a], by simp⟩
      · obtain ⟨d, hd⟩ : ∃ d, m - u.length = d + 1 := ⟨m - u.length - 1, by omega⟩
        rw [hd, List.take_of_length_le (l := u) (by omega),
          foldl_good hu (a :: s) (Or.inr (by simp)), List.take_succ_cons, List.foldl_cons,
          pp_pop]
        exact ihv s hs d

theorem foldl_first_return {a : Fin k ⊕ Fin k} {u : List (Fin k ⊕ Fin k)}
    (v : List (Fin k ⊕ Fin k)) (hu : Good a.swap u) :
    ((a :: (u ++ a.swap :: v)).take (u.length + 1 + 1)).foldl pp [] = [] := by
  rw [List.take_succ_cons, List.foldl_cons, pp_nil, List.take_append,
    List.take_of_length_le (l := u) (by omega), show u.length + 1 - u.length = 0 + 1 by omega,
    List.take_succ_cons, List.take_zero, List.foldl_append, foldl_good hu [a] (Or.inr (by simp)),
    List.foldl_cons, pp_pop, List.foldl_nil]

theorem foldl_no_return {a : Fin k ⊕ Fin k} {u : List (Fin k ⊕ Fin k)}
    (v : List (Fin k ⊕ Fin k)) (hu : Good a.swap u) {m : ℕ} (hm : m ≤ u.length) :
    ((a :: (u ++ a.swap :: v)).take (m + 1)).foldl pp [] ≠ [] := by
  rw [List.take_succ_cons, List.foldl_cons, pp_nil, List.take_append,
    show m - u.length = 0 by omega, List.take_zero, List.append_nil]
  obtain ⟨r, hr⟩ := foldl_take_good hu [a] (Or.inr (by simp)) m
  rw [hr]
  simp

theorem enc_inj {a a' : Fin k ⊕ Fin k} {u v u' v' : List (Fin k ⊕ Fin k)}
    (hu : Good a.swap u) (hu' : Good a'.swap u')
    (h : a :: (u ++ a.swap :: v) = a' :: (u' ++ a'.swap :: v')) :
    a = a' ∧ u = u' ∧ v = v' := by
  have ha : a = a' := (List.cons.inj h).1
  subst ha
  have hlen : u.length = u'.length := by
    rcases lt_trichotomy u.length u'.length with hlt | heq | hgt
    · exfalso
      have h1 := foldl_first_return v hu
      rw [h] at h1
      exact foldl_no_return v' hu' (m := u.length + 1) (by omega) h1
    · exact heq
    · exfalso
      have h1 := foldl_first_return v' hu'
      rw [← h] at h1
      exact foldl_no_return v hu (m := u'.length + 1) (by omega) h1
  have h2 := (List.cons.inj h).2
  obtain ⟨rfl, h3⟩ := List.append_inj h2 hlen
  exact ⟨rfl, rfl, (List.cons.inj h3).2⟩

/-- The generator attached to a letter. -/
def gen : Fin k ⊕ Fin k → FreeGroup (Fin k)
  | Sum.inl i => FreeGroup.of i
  | Sum.inr i => (FreeGroup.of i)⁻¹

theorem gen_swap (a : Fin k ⊕ Fin k) : gen a.swap = (gen a)⁻¹ := by
  cases a <;> simp [gen]

theorem wordFree_map (w : List (Fin k ⊕ Fin k)) :
    StrongConv.wordFree (w.map some) = (w.map gen).prod := by
  unfold StrongConv.wordFree
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro x _
  cases x <;> rfl

theorem good_prod {f : Fin k ⊕ Fin k} {w : List (Fin k ⊕ Fin k)} (h : Good f w) :
    (w.map gen).prod = 1 := by
  induction h with
  | nil f => rfl
  | @cons f a u v ha hu hv ihu ihv =>
    simp [List.map_append, List.prod_append, ihu, ihv, gen_swap]

/-- Words of length `m`. -/
def W (k m : ℕ) : Finset (List (Fin k ⊕ Fin k)) :=
  Finset.univ.image (List.ofFn : (Fin m → Fin k ⊕ Fin k) → List (Fin k ⊕ Fin k))

theorem mem_W {m : ℕ} {w : List (Fin k ⊕ Fin k)} : w ∈ W k m ↔ w.length = m := by
  constructor
  · intro h
    simp only [W, Finset.mem_image] at h
    obtain ⟨i, _, rfl⟩ := h
    simp
  · intro h
    subst h
    exact Finset.mem_image.2 ⟨fun j => w[j.val], Finset.mem_univ _, List.ofFn_getElem⟩

open Classical in
/-- Good words of length `2n`. -/
noncomputable def G (k n : ℕ) (f : Fin k ⊕ Fin k) : Finset (List (Fin k ⊕ Fin k)) :=
  (W k (2 * n)).filter (Good f)

theorem mem_G {n : ℕ} {f : Fin k ⊕ Fin k} {w : List (Fin k ⊕ Fin k)} :
    w ∈ G k n f ↔ w ∈ W k (2 * n) ∧ Good f w := by
  unfold G
  exact @Finset.mem_filter _ _ (Classical.decPred _) _ _

/-- The words built from a first block over `i` and the rest. -/
noncomputable def T (k n : ℕ) (f : Fin k ⊕ Fin k) : Finset (List (Fin k ⊕ Fin k)) :=
  (univ : Finset (Fin (n + 1))).biUnion fun i => (univ.erase f).biUnion fun a =>
    (G k i a.swap ×ˢ G k (n - i) f).image fun p => a :: (p.1 ++ a.swap :: p.2)

theorem T_subset (n : ℕ) (f : Fin k ⊕ Fin k) : T k n f ⊆ G k (n + 1) f := by
  intro w hw
  simp only [T, mem_biUnion, mem_image, mem_product, mem_univ, true_and, mem_erase] at hw
  obtain ⟨i, a, ⟨haf, _⟩, ⟨u, v⟩, ⟨hu, hv⟩, rfl⟩ := hw
  rw [mem_G, mem_W] at hu hv
  rw [mem_G, mem_W]
  refine ⟨?_, Good.cons haf hu.2 hv.2⟩
  have hi := i.isLt
  simp only [List.length_cons, List.length_append] at hu hv ⊢
  omega

theorem card_T (n : ℕ) (f : Fin k ⊕ Fin k) :
    (T k n f).card = ∑ i : Fin (n + 1), ∑ a ∈ univ.erase f,
      (G k i a.swap).card * (G k (n - i) f).card := by
  unfold T
  rw [card_biUnion]
  · refine sum_congr rfl fun i _ => ?_
    rw [card_biUnion]
    · refine sum_congr rfl fun a _ => ?_
      rw [card_image_of_injOn, card_product]
      rintro ⟨u, v⟩ huv ⟨u', v'⟩ huv' heq
      simp only [coe_product, Set.mem_prod, mem_coe, mem_G] at huv huv'
      obtain ⟨-, rfl, rfl⟩ := enc_inj huv.1.2 huv'.1.2 heq
      rfl
    · intro a _ b _ hab
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro w hw hw'
      simp only [mem_image, mem_product, mem_G] at hw hw'
      obtain ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩ := hw
      obtain ⟨⟨u', v'⟩, ⟨hu', hv'⟩, heq⟩ := hw'
      exact hab (enc_inj hu.2 hu'.2 heq.symm).1
  · intro i _ j _ hij
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro w hw hw'
    simp only [mem_biUnion, mem_image, mem_product, mem_G, mem_W] at hw hw'
    obtain ⟨a, _, ⟨u, v⟩, ⟨hu, hv⟩, rfl⟩ := hw
    obtain ⟨a', _, ⟨u', v'⟩, ⟨hu', hv'⟩, heq⟩ := hw'
    obtain ⟨-, rfl, -⟩ := enc_inj hu.2 hu'.2 heq.symm
    apply hij
    ext
    have := hu.1.symm.trans hu'.1
    omega

theorem card_G_ge (n : ℕ) : ∀ f : Fin k ⊕ Fin k,
    catalan n * (2 * k - 1) ^ n ≤ (G k n f).card := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f
    cases n with
    | zero =>
      simp only [catalan_zero, pow_zero, mul_one]
      exact Finset.card_pos.2 ⟨[], mem_G.2 ⟨mem_W.2 rfl, Good.nil f⟩⟩
    | succ n =>
      calc catalan (n + 1) * (2 * k - 1) ^ (n + 1)
          = ∑ i : Fin (n + 1), ∑ _a ∈ univ.erase f,
              (catalan i * (2 * k - 1) ^ (i : ℕ)) *
                (catalan (n - i) * (2 * k - 1) ^ (n - i)) := by
            rw [catalan_succ, Finset.sum_mul]
            refine sum_congr rfl fun i _ => ?_
            rw [sum_const, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_sum,
              Fintype.card_fin, smul_eq_mul]
            have hi := i.isLt
            have hp : (2 * k - 1) ^ (n + 1) =
                (2 * k - 1) * ((2 * k - 1) ^ (i : ℕ) * (2 * k - 1) ^ (n - i)) := by
              rw [← pow_add, show (i : ℕ) + (n - i) = n by omega, pow_succ, mul_comm]
            rw [hp, show k + k - 1 = 2 * k - 1 by omega]
            ring
        _ ≤ ∑ i : Fin (n + 1), ∑ a ∈ univ.erase f,
              (G k i a.swap).card * (G k (n - i) f).card := by
            refine sum_le_sum fun i _ => sum_le_sum fun a _ => ?_
            have hi := i.isLt
            exact Nat.mul_le_mul (ih i (by omega) _) (ih (n - i) (by omega) _)
        _ = (T k n f).card := (card_T n f).symm
        _ ≤ (G k (n + 1) f).card := card_le_card (T_subset n f)

end Puder.T85.PartY
end

section
open Filter Topology
namespace Puder.T85.PartY
open Finset
theorem four_pow_le_catalan (n : ℕ) :
    (4 : ℝ) ^ n ≤ ((n : ℝ) + 1) * (2 * n + 1) * catalan n := by
  have h1 := Nat.four_pow_le_two_mul_add_one_mul_central_binom n
  have h0 := succ_mul_catalan_eq_centralBinom n
  rw [Nat.centralBinom_eq_two_mul_choose] at h0
  rw [← h0] at h1
  have h2 : ((4 ^ n : ℕ) : ℝ) ≤ ((((2 * n + 1) * ((n + 1) * catalan n)) : ℕ) : ℝ) := by
    exact_mod_cast h1
  push_cast at h2
  linarith

/-! ## Counting -/
theorem ofFn_getD {α : Type*} (M : List α) (d : α) (t : ℕ) (h : M.length = t) :
    List.ofFn (fun j : Fin t => M.getD j d) = M := by
  subst h
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp

theorem word_eq {k t : ℕ} (i : Fin t → Fin k ⊕ Fin k) : word i = ((List.ofFn i).map gen).prod := by
  unfold word
  rw [show (List.ofFn fun j => some (i j)) = (List.ofFn i).map some from List.map_ofFn.symm,
    wordFree_map]

theorem card_G_le_b (k m n ℓ : ℕ) (hk : 1 ≤ k) (s : Fin ℓ → Fin k ⊕ Fin k)
    (hs : primitivityRank (word s) = m) (f : Fin k ⊕ Fin k) :
    ((G k n f).card : ℝ) ≤ b k m (2 * n + ℓ) := by
  unfold b
  have d : Fin k ⊕ Fin k := Sum.inl ⟨0, hk⟩
  exact_mod_cast Finset.card_le_card_of_injOn
    (fun L => fun j : Fin (2 * n + ℓ) => (L ++ List.ofFn s).getD j d)
    (by
      intro L hL
      rw [Finset.mem_coe, mem_G, mem_W] at hL
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      rw [word_eq, ofFn_getD _ _ _ (by simp [hL.1]), List.map_append, List.prod_append,
        good_prod hL.2, one_mul, ← word_eq, hs])
    (by
      intro L hL L' hL' heq
      have := congrArg List.ofFn heq
      simp only at this
      rw [Finset.mem_coe, mem_G, mem_W] at hL hL'
      rw [ofFn_getD _ _ _ (by simp [hL.1]), ofFn_getD _ _ _ (by simp [hL'.1])] at this
      exact List.append_cancel_right this)

theorem catalan_le_b (k m n ℓ : ℕ) (hk : 1 ≤ k) (s : Fin ℓ → Fin k ⊕ Fin k)
    (hs : primitivityRank (word s) = m) :
    (catalan n : ℝ) * (2 * k - 1 : ℝ) ^ n ≤ b k m (2 * n + ℓ) := by
  have h := card_G_ge (k := k) n (Sum.inl ⟨0, hk⟩)
  have hc : ((2 * k - 1 : ℕ) : ℝ) = 2 * k - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [← hc]
  refine le_trans ?_ (card_G_le_b k m n ℓ hk s hs (Sum.inl ⟨0, hk⟩))
  exact_mod_cast h

theorem exists_split (k m t : ℕ) (hk : 2 ≤ k) (hm1 : 1 ≤ m) (hm : m ≤ k) (ht : 2 * m + 1 ≤ t) :
    ∃ n ℓ : ℕ, t = 2 * n + ℓ ∧ ℓ ≤ 2 * m + 1 ∧
      (catalan n : ℝ) * (2 * k - 1 : ℝ) ^ n ≤ b k m t := by
  obtain ⟨n, hn | hn⟩ := Nat.even_or_odd' (t - 2 * m)
  · refine ⟨n, 2 * m, by omega, by omega, ?_⟩
    rw [show t = 2 * n + 2 * m by omega]
    exact catalan_le_b k m n _ (by omega) _ (primitivityRank_sEven k m hm hm1)
  · refine ⟨n, 2 * m + 1, by omega, le_rfl, ?_⟩
    rw [show t = 2 * n + (2 * m + 1) by omega]
    exact catalan_le_b k m n _ (by omega) _ (primitivityRank_sOdd k m hm hm1)

theorem b_nonneg (k m t : ℕ) : 0 ≤ b k m t := by unfold b; positivity

/-! ## Upper bound -/
theorem upper (k m : ℕ) (hk : 2 ≤ k) (hm1 : 1 ≤ m) (hm : m ≤ k) :
    IsBoundedUnder (· ≤ ·) atTop (fun t : ℕ => b k m t ^ (1 / (t : ℝ))) ∧
      limsup (fun t : ℕ => b k m t ^ (1 / (t : ℝ))) atTop ≤ StrongConv.rhoStair k m := by
  obtain ⟨hB, hL⟩ := Puder.limsup_sum_ncard_crit_rpow_le_rhoStair k m hk hm1 hm
  have hle : ∀ t : ℕ, b k m t ^ (1 / (t : ℝ)) ≤
      (∑ i : Fin t → Fin k ⊕ Fin k with
            primitivityRank (StrongConv.wordFree (List.ofFn fun j => some (i j))) = m,
          ((Crit (StrongConv.wordFree (List.ofFn fun j => some (i j)))).ncard : ℝ)) ^
          (1 / (t : ℝ)) := by
    intro t
    apply Real.rpow_le_rpow (b_nonneg k m t) _ (by positivity)
    unfold b
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_filter] at hi
    have hne := crit_nonempty _ m hi.2
    have := (Set.ncard_pos (Puder.Q284Fin.crit_finite _)).2 hne
    simp only [Nat.cast_one]
    exact_mod_cast this
  have hB' : IsBoundedUnder (· ≤ ·) atTop (fun t : ℕ => b k m t ^ (1 / (t : ℝ))) :=
    hB.mono_le (Eventually.of_forall hle)
  refine ⟨hB', le_trans (limsup_le_limsup (Eventually.of_forall hle) ?_ hB) hL⟩
  exact isCoboundedUnder_le_of_le atTop (fun t => Real.rpow_nonneg (b_nonneg k m t) _)

end Puder.T85.PartY
end

section
open Filter Topology
namespace Puder.T85
/-! ## Part Y: counting and limits (stubs) -/

end Puder.T85
end

section
open Filter Topology
namespace Puder.T85.PartY
open Finset
/-! ## Lower bound in the small-`m` range -/
theorem tendsto_g (C : ℝ) (hC : 0 < C) :
    Tendsto (fun t : ℕ => C ^ (1 / (t : ℝ)) / ((t : ℝ) ^ (1 / (t : ℝ)) * (t : ℝ) ^ (1 / (t : ℝ))))
      atTop (𝓝 1) := by
  have h0 : Tendsto (fun t : ℕ => 1 / (t : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have h1 : Tendsto (fun t : ℕ => C ^ (1 / (t : ℝ))) atTop (𝓝 (C ^ (0 : ℝ))) :=
    tendsto_const_nhds.rpow h0 (Or.inl hC.ne')
  have h2 : Tendsto (fun t : ℕ => (t : ℝ) ^ (1 / (t : ℝ))) atTop (𝓝 1) :=
    tendsto_rpow_div.comp tendsto_natCast_atTop_atTop
  rw [Real.rpow_zero] at h1
  have := h1.div (h2.mul h2) (by norm_num)
  rw [show (1 : ℝ) / (1 * 1) = 1 by norm_num] at this
  exact this

theorem lower_small (k m : ℕ) (hk : 2 ≤ k) (hm1 : 1 ≤ m) (hm : m ≤ k)
    (hsmall : (2 * m - 1 : ℝ) ≤ Real.sqrt (2 * k - 1)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℕ in atTop, 2 * Real.sqrt (2 * k - 1) - ε ≤ b k m t ^ (1 / (t : ℝ)) := by
  set q : ℝ := 2 * k - 1 with hqdef
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hq : 3 ≤ q := by rw [hqdef]; linarith
  set A : ℝ := 2 * Real.sqrt q with hAdef
  have hsq : Real.sqrt q ^ 2 = q := Real.sq_sqrt (by linarith)
  have hA2 : A ^ 2 = 4 * q := by rw [hAdef, mul_pow, hsq]; norm_num
  have hA1 : 1 ≤ A := by nlinarith [Real.sqrt_nonneg q]
  have hA0 : 0 < A := by linarith
  set C : ℝ := 1 / (A ^ (2 * m + 1) * 8) with hCdef
  have hC : 0 < C := by positivity
  -- the explicit lower bound
  have hbound : ∀ t : ℕ, 2 * m + 1 ≤ t →
      A ^ t * C / ((t : ℝ) * t) ≤ b k m t := by
    intro t ht
    obtain ⟨n, ℓ, rfl, hℓ, hb⟩ := exists_split k m t hk hm1 hm ht
    refine le_trans ?_ hb
    have hcat := four_pow_le_catalan n
    have ht1 : (1 : ℝ) ≤ ((2 * n + ℓ : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ 2 * n + ℓ by omega)
    have hnt : (n : ℝ) ≤ ((2 * n + ℓ : ℕ) : ℝ) := by exact_mod_cast (show n ≤ 2 * n + ℓ by omega)
    set T : ℝ := ((2 * n + ℓ : ℕ) : ℝ) with hT
    have hpow : A ^ (2 * n + ℓ) ≤ (4 * q) ^ n * A ^ (2 * m + 1) := by
      rw [pow_add, pow_mul, hA2]
      gcongr
    have hpoly : ((n : ℝ) + 1) * (2 * n + 1) ≤ 8 * (T * T) := by nlinarith
    have hqn : 0 ≤ q ^ n := by positivity
    have hc0 : (0 : ℝ) ≤ catalan n := by positivity
    rw [hCdef, div_le_iff₀ (by positivity)]
    calc A ^ (2 * n + ℓ) * (1 / (A ^ (2 * m + 1) * 8))
        ≤ (4 * q) ^ n * A ^ (2 * m + 1) * (1 / (A ^ (2 * m + 1) * 8)) := by gcongr
      _ = 4 ^ n * q ^ n / 8 := by field_simp; rw [mul_pow]
      _ ≤ ((n : ℝ) + 1) * (2 * n + 1) * catalan n * q ^ n / 8 := by gcongr
      _ ≤ 8 * (T * T) * catalan n * q ^ n / 8 := by gcongr
      _ = catalan n * q ^ n * (T * T) := by ring
  -- the rescaled lower bound tends to `A`
  have hlim : Tendsto (fun t : ℕ => A * (C ^ (1 / (t : ℝ)) /
      ((t : ℝ) ^ (1 / (t : ℝ)) * (t : ℝ) ^ (1 / (t : ℝ))))) atTop (𝓝 A) := by
    simpa using (tendsto_g C hC).const_mul A
  have hev := hlim.eventually (eventually_gt_nhds (show A - ε < A by linarith))
  filter_upwards [hev, eventually_ge_atTop (2 * m + 1)] with t h1 h2
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have heq : (A ^ t * C / ((t : ℝ) * t)) ^ (1 / (t : ℝ)) = A * (C ^ (1 / (t : ℝ)) /
      ((t : ℝ) ^ (1 / (t : ℝ)) * (t : ℝ) ^ (1 / (t : ℝ)))) := by
    rw [Real.div_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) hC.le,
      Real.mul_rpow ht0.le ht0.le, one_div (t : ℝ), Real.pow_rpow_inv_natCast hA0.le (by omega)]
    ring
  calc 2 * Real.sqrt (2 * k - 1) - ε = A - ε := rfl
    _ ≤ A * (C ^ (1 / (t : ℝ)) / ((t : ℝ) ^ (1 / (t : ℝ)) * (t : ℝ) ^ (1 / (t : ℝ)))) := h1.le
    _ = (A ^ t * C / ((t : ℝ) * t)) ^ (1 / (t : ℝ)) := heq.symm
    _ ≤ b k m t ^ (1 / (t : ℝ)) :=
      Real.rpow_le_rpow (by positivity) (hbound t h2) (by positivity)

end Puder.T85.PartY
end

section
open Filter Topology
namespace Puder.T85

end Puder.T85
end

section
open Filter Topology
namespace Puder.T85.PartY
open Finset
/-! ## Target -/
theorem t85_dev (k m : ℕ) (hk : 2 ≤ k) (hm1 : 1 ≤ m) (hm : m ≤ k) :
    Tendsto (fun t : ℕ =>
        ((Finset.univ.filter fun i : Fin t → Fin k ⊕ Fin k =>
            primitivityRank (StrongConv.wordFree (List.ofFn fun j => some (i j))) = m).card : ℝ) ^
          (1 / (t : ℝ))) atTop (𝓝 (StrongConv.rhoStair k m)) := by
  by_cases h : (2 * m - 1 : ℝ) ≤ Real.sqrt (2 * k - 1)
  · show Tendsto (fun t : ℕ => b k m t ^ (1 / (t : ℝ))) atTop (𝓝 (StrongConv.rhoStair k m))
    have hr : StrongConv.rhoStair k m = 2 * Real.sqrt (2 * k - 1) := by
      rw [StrongConv.rhoStair, if_pos h]
    obtain ⟨hB, hL⟩ := upper k m hk hm1 hm
    rw [hr] at hL ⊢
    have hB0 : IsBoundedUnder (· ≥ ·) atTop (fun t : ℕ => b k m t ^ (1 / (t : ℝ))) :=
      isBoundedUnder_of_eventually_ge
        (Eventually.of_forall fun t => Real.rpow_nonneg (b_nonneg k m t) _)
    refine tendsto_of_le_liminf_of_limsup_le ?_ hL hB hB0
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have := le_liminf_of_le hB.isCoboundedUnder_ge (lower_small k m hk hm1 hm h ε hε)
    linarith
  · rw [StrongConv.rhoStair, if_neg h]
    exact Puder.tendsto_card_primitivityRank_eq_rpow_of_sqrt_lt k m hk hm (lt_of_not_ge h)

end Puder.T85.PartY
end

section
open Filter Topology
namespace Puder.T85
/-! ## Target -/
alias t85_dev := Puder.T85.PartY.t85_dev

end Puder.T85
end

open Filter Topology Puder in
theorem solution (k m : ℕ) (hk : 2 ≤ k) (hm1 : 1 ≤ m)
    (hm : m ≤ k) :
    Tendsto (fun t : ℕ =>
        ((Finset.univ.filter fun i : Fin t → Fin k ⊕ Fin k =>
            primitivityRank (StrongConv.wordFree (List.ofFn fun j => some (i j))) = m).card : ℝ) ^
          (1 / (t : ℝ))) atTop (𝓝 (StrongConv.rhoStair k m)) :=
  Puder.T85.t85_dev k m hk hm1 hm
