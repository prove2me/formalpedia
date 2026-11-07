-- Prove2me | solution 1 for Puder.tendsto_card_primitivityRank_eq_rpow_rhoStair
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T10:33:46.307444+00:00
-- url     : https://prove2.me/submissions/23e9dcb2-9d4e-43ab-87c9-1660fd09d095
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvPuder
import Theorems.Thm_Puder_crit_finite_and_isBigO_uniformExp_card_fixedPoints
import Theorems.Thm_Puder_limsup_sum_ncard_crit_rpow_le_rhoStair
import Theorems.Thm_Puder_primitivityRank_mul_eq_add_of_disjoint
import Theorems.Thm_Puder_tendsto_card_primitivityRank_eq_rpow_of_sqrt_lt

section
open Filter Topology
namespace Puder.T85
/-! q218 Blueprint: Puder Theorem 8.5, clause m ∈ {1, …, k}, from Corollary 4.5, Theorem 2.3 (finiteness of
Crit), Puder 2014 Lemma 6.8 and the case 2m - 1 > √(2k-1). -/
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

theorem freeGroup_fin_zero_eq_one (g : FreeGroup (Fin 0)) : g = 1 := by
  induction g using FreeGroup.induction_on with
  | C1 => rfl
  | of i => exact i.elim0
  | inv_of i _ => exact i.elim0
  | mul x y hx hy => rw [hx, hy, mul_one]

theorem one_le_primitivityRank {k : ℕ} (w : FreeGroup (Fin k)) (hw1 : w ≠ 1) :
    1 ≤ primitivityRank w := by
  unfold primitivityRank
  refine le_iInf₂ fun r hr => ?_
  obtain ⟨J, hw, ⟨b⟩, _⟩ := hr
  rcases Nat.eq_zero_or_pos r with h0 | hpos
  · subst h0
    exfalso
    apply hw1
    have : (⟨w, hw⟩ : J) = 1 := by
      rw [← b.repr.symm_apply_apply ⟨w, hw⟩, freeGroup_fin_zero_eq_one (b.repr ⟨w, hw⟩)]; exact map_one _
    exact congrArg Subtype.val this
  · exact_mod_cast hpos

/-- The homomorphism counting the exponent sum of the letter `x`. -/
noncomputable def expSum {k : ℕ} (x : Fin k) : FreeGroup (Fin k) →* Multiplicative ℤ :=
  FreeGroup.lift fun j => if j = x then Multiplicative.ofAdd 1 else 1

theorem expSum_of {k : ℕ} (x : Fin k) : expSum x (of x) = Multiplicative.ofAdd 1 := by
  simp [expSum]

theorem of_pow_ne_one {k : ℕ} (x : Fin k) (a : ℕ) (ha : 1 ≤ a) : (of x) ^ a ≠ 1 := by
  intro h
  have := congrArg (fun g => Multiplicative.toAdd (expSum x g)) h
  simp [expSum_of] at this
  omega

theorem primitivityRank_of_pow {k : ℕ} (x : Fin k) (a : ℕ) (ha : 2 ≤ a) :
    primitivityRank ((of x) ^ a) = 1 := by
  apply le_antisymm
  · let φ : FreeGroup (Fin 1) →* FreeGroup (Fin k) := FreeGroup.map fun _ => x
    have hinj : Function.Injective φ :=
      FreeGroup.map_injective (fun _ _ _ => Subsingleton.elim _ _)
    have hx : of x ∈ φ.range := ⟨of 0, by simp [φ]⟩
    refine primitivityRank_le _ φ.range 1 (pow_mem hx a)
      ⟨FreeGroupBasis.ofRepr (MonoidHom.ofInjective hinj).symm⟩ ?_
    rintro ⟨ι, b, i, hb⟩
    classical
    let ψ : φ.range →* Multiplicative ℤ := b.lift fun j => if j = i then Multiplicative.ofAdd 1 else 1
    have h1 : ψ (b i) = Multiplicative.ofAdd 1 := by
      simp [ψ, FreeGroupBasis.lift]
    have h2 : b i = (⟨of x, hx⟩ : φ.range) ^ a := Subtype.ext (by simp [hb])
    rw [h2, map_pow] at h1
    have h3 := congrArg Multiplicative.toAdd h1
    simp only [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul] at h3
    have h4 : (a : ℤ) ∣ 1 := ⟨_, h3.symm⟩
    have h5 : a ∣ 1 := Int.ofNat_dvd.mp h4
    have := Nat.le_of_dvd one_pos h5
    omega
  · exact one_le_primitivityRank _ (of_pow_ne_one x a (by omega))

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

theorem step {k n : ℕ} (hn : n < k) (w : FreeGroup (Fin k))
    (hw : w ∈ Subgroup.closure (of '' {j : Fin k | (j : ℕ) < n})) (hπ : primitivityRank w = n) :
    primitivityRank (w * (of (⟨n, hn⟩ : Fin k) * of ⟨n, hn⟩)) = ((n + 1 : ℕ) : ℕ∞) ∧
      w * (of (⟨n, hn⟩ : Fin k) * of ⟨n, hn⟩) ∈
        Subgroup.closure (of '' {j : Fin k | (j : ℕ) < n + 1}) := by
  have h2 : of (⟨n, hn⟩ : Fin k) * of ⟨n, hn⟩ ∈
      Subgroup.closure (of '' {j : Fin k | (j : ℕ) = n}) :=
    mul_mem (Subgroup.subset_closure ⟨⟨n, hn⟩, rfl, rfl⟩)
      (Subgroup.subset_closure ⟨⟨n, hn⟩, rfl, rfl⟩)
  have hdisj : Disjoint {j : Fin k | (j : ℕ) < n} {j : Fin k | (j : ℕ) = n} := by
    rw [Set.disjoint_left]
    intro j h1 h2
    simp only [Set.mem_ofPred_eq] at h1 h2
    omega
  constructor
  · rw [Puder.primitivityRank_mul_eq_add_of_disjoint _ _ hdisj w _ hw h2, hπ, ← sq,
      primitivityRank_of_pow _ 2 le_rfl]
    push_cast
    rfl
  · refine mul_mem (Subgroup.closure_mono (Set.image_mono ?_) hw)
      (Subgroup.closure_mono (Set.image_mono ?_) h2)
    · intro j hj
      simp only [Set.mem_ofPred_eq] at hj ⊢
      omega
    · intro j hj
      simp only [Set.mem_ofPred_eq] at hj ⊢
      omega

theorem sEven_aux (k n : ℕ) (hn1 : 1 ≤ n) : ∀ h : n ≤ k,
    primitivityRank (word (sEven k n h)) = n ∧
      word (sEven k n h) ∈ Subgroup.closure (of '' {j : Fin k | (j : ℕ) < n}) := by
  induction n, hn1 using Nat.le_induction with
  | base =>
    intro h
    have e : word (sEven k 1 h) = (of (⟨0, by omega⟩ : Fin k)) ^ 2 := by
      rw [sq]
      exact (sEven_succ k 0 h).trans (by rw [word_zero, one_mul])
    rw [e]
    refine ⟨by exact_mod_cast primitivityRank_of_pow _ 2 le_rfl, ?_⟩
    exact pow_mem (Subgroup.subset_closure (Set.mem_image_of_mem of (show (⟨0, by omega⟩ : Fin k) ∈ {j : Fin k | (j : ℕ) < 1} by simp))) 2
  | succ n hn ih =>
    intro h
    obtain ⟨hπ, hm⟩ := ih (by omega)
    rw [sEven_succ k n h]
    exact step (by omega) _ hm hπ

theorem sOdd_aux (k n : ℕ) (hn1 : 1 ≤ n) : ∀ h : n ≤ k,
    primitivityRank (word (sOdd k n h hn1)) = n ∧
      word (sOdd k n h hn1) ∈ Subgroup.closure (of '' {j : Fin k | (j : ℕ) < n}) := by
  induction n, hn1 using Nat.le_induction with
  | base =>
    intro h
    rw [sOdd_one k h]
    refine ⟨by exact_mod_cast primitivityRank_of_pow _ 3 (by norm_num), ?_⟩
    exact pow_mem (Subgroup.subset_closure (Set.mem_image_of_mem of (show (⟨0, by omega⟩ : Fin k) ∈ {j : Fin k | (j : ℕ) < 1} by simp))) 3
  | succ n hn ih =>
    intro h
    obtain ⟨hπ, hm⟩ := ih (by omega)
    rw [sOdd_succ k n h hn]
    exact step (by omega) _ hm hπ

theorem primitivityRank_sEven (k m : ℕ) (hm : m ≤ k) (hm1 : 1 ≤ m) :
    primitivityRank (word (sEven k m hm)) = m :=
  (sEven_aux k m hm1 hm).1

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
    primitivityRank (word (sOdd k m hm hm1)) = m :=
  (sOdd_aux k m hm1 hm).1

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
    have hfin := (Puder.crit_finite_and_isBigO_uniformExp_card_fixedPoints k _ m hi.2).1
    have hne := crit_nonempty _ m hi.2
    have := (Set.ncard_pos hfin).2 hne
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
