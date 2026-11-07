-- Prove2me | solution 1 for Puder.limsup_card_wordFree_eq_one_rpow
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T09:50:37.288747+00:00
-- url     : https://prove2.me/submissions/7ddcbfe2-70a5-4bca-8b9c-a1a5964ad612

import Mathlib
import Definitions.Def_StrongConv
import Theorems.Thm_StrongConv_norm_adjFree

section
open Filter Topology
namespace Puder.BS
/-- The number of words of length `t` in `2k` letters reducing to `1`. -/
noncomputable abbrev e (k t : ℕ) : ℕ :=
  (Finset.univ.filter fun i : Fin t → Fin k ⊕ Fin k =>
    StrongConv.wordFree (List.ofFn fun j => some (i j)) = 1).card

end Puder.BS
end

section
open Filter Topology StrongConv
open scoped InnerProductSpace
noncomputable section
namespace Puder.BS.PartS6A
/-! ### The left-regular representation (copied from the accepted `nuAdj_one_pow_eq` proof) -/
lemma leftReg_apply {d : ℕ} (g : FreeGroup (Fin d)) (f : L2Free d) (h : FreeGroup (Fin d)) :
    leftReg g f h = f (g⁻¹ * h) := rfl

lemma leftReg_mul {d : ℕ} (g g' : FreeGroup (Fin d)) :
    leftReg (g * g') = leftReg g * leftReg g' := by
  ext f h
  simp only [leftReg_apply, mul_apply_eq_comp, mul_inv_rev, mul_assoc]

lemma leftReg_one {d : ℕ} : leftReg (1 : FreeGroup (Fin d)) = 1 := by
  ext f h
  simp [leftReg_apply]

lemma star_leftReg {d : ℕ} (g : FreeGroup (Fin d)) : star (leftReg g) = leftReg g⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  simp only [leftReg_apply, inv_inv]
  rw [← (Equiv.mulLeft g⁻¹).tsum_eq]
  simp

lemma wordEval_sLimit {d : ℕ} (w : List (Letter d)) :
    wordEval (sLimit d) w = leftReg (wordFree w) := by
  induction w with
  | nil => simp [wordEval, wordFree, leftReg_one]
  | cons a w ih =>
    simp only [wordEval, wordFree, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, leftReg_mul]
    congr 1
    rcases a with _ | (i | i)
    · simp [leftReg_one]
    · simp [letterOp, sLimit]
    · simp [letterOp, sLimit, star_leftReg]

theorem tau_wordEval_sLimit {d : ℕ} (w : List (Letter d)) :
    tau (wordEval (sLimit d) w) = if wordFree w = 1 then 1 else 0 := by
  classical
  rw [wordEval_sLimit, tau, delta, lp.inner_single_left, leftReg_apply]
  simp only [mul_one, lp.single_apply]
  by_cases h : wordFree w = 1
  · simp [h]
  · rw [if_neg h, Pi.single_apply, if_neg (by simpa [inv_eq_one] using h)]
    simp

end Puder.BS.PartS6A
end
end

section
open Filter Topology StrongConv
open scoped InnerProductSpace
noncomputable section
namespace Puder.BS.PartS6A
variable {R ι : Type*} [Ring R] [Fintype ι]
lemma sum_pow_words (f : ι → R) (p : ℕ) :
    (∑ i, f i) ^ p = ∑ x : Fin p → ι, (List.ofFn fun j => f (x j)).prod := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [pow_succ', ih, Finset.sum_mul_sum]
    symm
    rw [← (Fin.consEquiv (fun _ : Fin (p + 1) => ι)).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun x _ => ?_))
    simp [Fin.consEquiv, List.ofFn_succ]

end Puder.BS.PartS6A
end
end

section
open Filter Topology StrongConv
open scoped InnerProductSpace
noncomputable section
namespace Puder.BS.PartS6A
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
lemma adj_sum {d : ℕ} (u : Fin d → H →L[ℂ] H) :
    ∑ i, (u i + star (u i)) = ∑ l : Fin d ⊕ Fin d, letterOp u l := by
  rw [Fintype.sum_sum_type]; simp [letterOp, Finset.sum_add_distrib]

lemma wordEval_ofFn {d p : ℕ} (u : Fin d → H →L[ℂ] H) (x : Fin p → Fin d ⊕ Fin d) :
    wordEval u (List.ofFn fun j => some (x j)) = (List.ofFn fun j => letterOp u (x j)).prod := by
  simp [wordEval, List.map_ofFn, Function.comp_def]

lemma adj_pow {d : ℕ} (u : Fin d → H →L[ℂ] H) (p : ℕ) :
    (∑ i, (u i + star (u i))) ^ p =
      ∑ x : Fin p → Fin d ⊕ Fin d, wordEval u (List.ofFn fun j => some (x j)) := by
  rw [adj_sum, sum_pow_words]
  simp_rw [wordEval_ofFn]

end Puder.BS.PartS6A
end
end

section
open Filter Topology StrongConv
open scoped InnerProductSpace
noncomputable section
namespace Puder.BS.PartS6A
lemma tau_adj_pow (d p : ℕ) :
    tau (adjFree d ^ p) = ∑ x : Fin p → Fin d ⊕ Fin d,
      tau (wordEval (sLimit d) (List.ofFn fun j => some (x j))) := by
  have : adjFree d ^ p = ∑ x : Fin p → Fin d ⊕ Fin d,
      wordEval (sLimit d) (List.ofFn fun j => some (x j)) :=
    adj_pow (sLimit d) p
  rw [this]
  unfold tau
  simp

lemma e_eq_tau (k t : ℕ) : ((Puder.BS.e k t : ℕ) : ℂ) = tau (adjFree k ^ t) := by
  classical
  rw [tau_adj_pow]
  simp_rw [tau_wordEval_sLimit]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]

lemma norm_delta_one (d : ℕ) : ‖(delta (1 : FreeGroup (Fin d)))‖ = 1 := by
  rw [delta, lp.norm_single (by norm_num)]
  simp

lemma norm_tau_le {d : ℕ} (a : L2Free d →L[ℂ] L2Free d) : ‖tau a‖ ≤ ‖a‖ := by
  unfold tau
  calc ‖⟪delta 1, a (delta 1)⟫_ℂ‖ ≤ ‖delta (1 : FreeGroup (Fin d))‖ * ‖a (delta 1)‖ :=
        norm_inner_le_norm _ _
    _ ≤ ‖delta (1 : FreeGroup (Fin d))‖ * (‖a‖ * ‖delta (1 : FreeGroup (Fin d))‖) := by
        gcongr
        exact a.le_opNorm _
    _ = ‖a‖ := by rw [norm_delta_one]; ring

theorem e_le (k t : ℕ) (hk : 1 ≤ k) : (Puder.BS.e k t : ℝ) ≤ (2 * Real.sqrt (2 * k - 1)) ^ t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [Puder.BS.e, StrongConv.wordFree]
  have h1 : ((Puder.BS.e k t : ℕ) : ℝ) = ‖(((Puder.BS.e k t : ℕ) : ℂ))‖ := by
    rw [Complex.norm_natCast]
  rw [h1, e_eq_tau, ← StrongConv.norm_adjFree k hk]
  exact (norm_tau_le _).trans (norm_pow_le' _ ht)

end Puder.BS.PartS6A
end
end

section
open Filter Topology
namespace Puder.BS

end Puder.BS
end

section
namespace Puder.BS.PartS6B
open Finset
variable {k : ℕ}
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

theorem card_G_le_e (n : ℕ) (f : Fin k ⊕ Fin k) : (G k n f).card ≤ e k (2 * n) := by
  unfold e
  refine le_trans (card_le_card ?_) (card_image_le (f := List.ofFn))
  intro w hw
  rw [mem_G] at hw
  obtain ⟨hwW, hg⟩ := hw
  simp only [W, mem_image, mem_univ, true_and] at hwW
  obtain ⟨i, rfl⟩ := hwW
  refine mem_image.2 ⟨i, mem_filter.2 ⟨mem_univ _, ?_⟩, rfl⟩
  rw [show (List.ofFn fun j => some (i j)) = (List.ofFn i).map some from List.map_ofFn.symm,
    wordFree_map, good_prod hg]

/-- Dyck paths with `2k - 1` choices per up-step give distinct closed walks. -/
theorem catalan_mul_le_e (k n : ℕ) (hk : 1 ≤ k) :
    (catalan n : ℝ) * (2 * k - 1 : ℝ) ^ n ≤ e k (2 * n) := by
  have h := (card_G_ge n (Sum.inl ⟨0, hk⟩)).trans (card_G_le_e (k := k) n (Sum.inl ⟨0, hk⟩))
  have hc : ((2 * k - 1 : ℕ) : ℝ) = 2 * k - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [← hc]
  exact_mod_cast h

end Puder.BS.PartS6B
end

section
open Filter Topology
namespace Puder.BS
alias catalan_mul_le_e := Puder.BS.PartS6B.catalan_mul_le_e

end Puder.BS
end

section
open Filter Topology StrongConv
open scoped InnerProductSpace
noncomputable section
namespace Puder.BS.PartS6A
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

end Puder.BS.PartS6A
end
end

section
open Filter Topology
namespace Puder.BS

end Puder.BS
end

section
open Filter Topology StrongConv
open scoped InnerProductSpace
noncomputable section
namespace Puder.BS.PartS6A
/-- `log((n+1)(2n+1)) / (2n) → 0`. -/
lemma tendsto_L :
    Tendsto (fun n : ℕ => Real.log (((n : ℝ) + 1) * (2 * n + 1)) * (1 / (2 * (n : ℝ))))
      atTop (𝓝 0) := by
  have hg : Tendsto (fun n : ℕ => (2 * (n : ℝ) + 1)) atTop atTop := by
    have : Tendsto (fun n : ℕ => ((2 * n + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_atTop_mono (fun n => by show n ≤ 2 * n + 1; omega) tendsto_id)
    simpa using this
  have hU : Tendsto (fun n : ℕ => Real.log (2 * (n : ℝ) + 1) ^ 1 /
      ((1 / 2) * (2 * (n : ℝ) + 1) + (-1 / 2))) atTop (𝓝 0) :=
    (Real.tendsto_pow_log_div_mul_add_atTop (1 / 2) (-1 / 2) 1 (by norm_num)).comp hg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    apply mul_nonneg
    · apply Real.log_nonneg; nlinarith
    · positivity
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hm : ((n : ℝ) + 1) * (2 * n + 1) ≤ (2 * (n : ℝ) + 1) ^ 2 := by nlinarith
    have hlog : Real.log (((n : ℝ) + 1) * (2 * n + 1)) ≤ 2 * Real.log (2 * (n : ℝ) + 1) := by
      have := Real.log_le_log (by positivity) hm
      rw [Real.log_pow] at this
      push_cast at this
      exact this
    have hden : (1 / 2) * (2 * (n : ℝ) + 1) + (-1 / 2) = n := by ring
    rw [hden, pow_one]
    rw [show Real.log (2 * (n : ℝ) + 1) / n = 2 * Real.log (2 * (n : ℝ) + 1) * (1 / (2 * n)) by
      field_simp]
    gcongr

theorem limsup_e (k : ℕ) (hk : 2 ≤ k) :
    IsBoundedUnder (· ≤ ·) atTop (fun t : ℕ => (Puder.BS.e k t : ℝ) ^ (1 / (t : ℝ))) ∧
      limsup (fun t : ℕ => (Puder.BS.e k t : ℝ) ^ (1 / (t : ℝ))) atTop =
        2 * Real.sqrt (2 * k - 1) := by
  set ρ := 2 * Real.sqrt (2 * k - 1) with hρdef
  set f := fun t : ℕ => (Puder.BS.e k t : ℝ) ^ (1 / (t : ℝ)) with hfdef
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hq : (0 : ℝ) < 2 * k - 1 := by linarith
  have hρ : 0 < ρ := by rw [hρdef]; positivity
  have hρsq : ρ ^ 2 = 4 * (2 * k - 1) := by
    rw [hρdef, mul_pow, Real.sq_sqrt hq.le]; norm_num
  -- upper bound
  have hup : ∀ t : ℕ, 1 ≤ t → f t ≤ ρ := by
    intro t ht
    have hle := e_le k t (by omega)
    have ht0 : t ≠ 0 := by omega
    calc f t = (Puder.BS.e k t : ℝ) ^ (1 / (t : ℝ)) := rfl
      _ ≤ (ρ ^ t) ^ (1 / (t : ℝ)) :=
          Real.rpow_le_rpow (by positivity) hle (by positivity)
      _ = ρ := by rw [one_div]; exact Real.pow_rpow_inv_natCast hρ.le ht0
  have hev : ∀ᶠ t in atTop, f t ≤ ρ := by
    filter_upwards [eventually_ge_atTop 1] with t ht using hup t ht
  have hbdd : IsBoundedUnder (· ≤ ·) atTop f := isBoundedUnder_of_eventually_le hev
  have hcobdd : IsCoboundedUnder (· ≤ ·) atTop f :=
    isCoboundedUnder_le_of_le atTop (fun t => Real.rpow_nonneg (by positivity) _)
  refine ⟨hbdd, le_antisymm (limsup_le_of_le hcobdd hev) ?_⟩
  -- lower bound
  set L := fun n : ℕ => Real.log (((n : ℝ) + 1) * (2 * n + 1)) * (1 / (2 * (n : ℝ))) with hL
  have hlow : ∀ n : ℕ, 1 ≤ n → ρ / Real.exp (L n) ≤ f (2 * n) := by
    intro n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    set m : ℝ := ((n : ℝ) + 1) * (2 * n + 1) with hm
    have hm0 : 0 < m := by positivity
    have hcat := Puder.BS.catalan_mul_le_e k n (by omega)
    have h4 := four_pow_le_catalan n
    have hE : ρ ^ (2 * n) / m ≤ (Puder.BS.e k (2 * n) : ℝ) := by
      rw [div_le_iff₀ hm0, pow_mul, hρsq, mul_pow]
      have hq' : (0 : ℝ) ≤ (2 * k - 1) ^ n := by positivity
      calc (4 : ℝ) ^ n * (2 * k - 1) ^ n ≤ m * catalan n * (2 * k - 1) ^ n := by
            rw [hm]; gcongr
        _ = m * (catalan n * (2 * k - 1) ^ n) := by ring
        _ ≤ m * (Puder.BS.e k (2 * n) : ℝ) := by gcongr
        _ = _ := by ring
    have h2n : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
    have h2n0 : (2 * n : ℕ) ≠ 0 := by omega
    calc ρ / Real.exp (L n) = (ρ ^ (2 * n) / m) ^ (1 / ((2 * n : ℕ) : ℝ)) := by
          rw [Real.div_rpow (by positivity) hm0.le, one_div ((2 * n : ℕ) : ℝ),
            Real.pow_rpow_inv_natCast hρ.le h2n0, Real.rpow_def_of_pos hm0, h2n]
          simp only [hL, hm, one_div]
      _ ≤ f (2 * n) := by
          simp only [hfdef]
          exact Real.rpow_le_rpow (by positivity) hE (by positivity)
  have hlim : Tendsto (fun n : ℕ => ρ / Real.exp (L n)) atTop (𝓝 ρ) := by
    have hL0 : Tendsto L atTop (𝓝 0) := tendsto_L
    have h1 : Tendsto (fun n => Real.exp (L n)) atTop (𝓝 (Real.exp 0)) :=
      (Real.continuous_exp.tendsto 0).comp hL0
    have h2 : Tendsto (fun n => ρ / Real.exp (L n)) atTop (𝓝 (ρ / Real.exp 0)) :=
      tendsto_const_nhds.div h1 (by positivity)
    rwa [Real.exp_zero, div_one] at h2
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hfreq : ∃ᶠ t in atTop, ρ - ε ≤ f t := by
    have hev2 : ∀ᶠ n in atTop, ρ - ε < ρ / Real.exp (L n) :=
      hlim.eventually (lt_mem_nhds (by linarith))
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev2
    rw [frequently_atTop]
    intro a
    refine ⟨2 * max (max N a) 1, by omega, ?_⟩
    exact (hN _ (by omega)).le.trans (hlow _ (by omega))
  have := le_limsup_of_frequently_le hfreq hbdd
  linarith

end Puder.BS.PartS6A
end
end

section
open Filter Topology
namespace Puder.BS
alias limsup_e := Puder.BS.PartS6A.limsup_e

end Puder.BS
end

section
open Filter Topology
theorem Puder.limsup_card_wordFree_eq_one_rpow_dev (k : ℕ) (hk : 2 ≤ k) :
    IsBoundedUnder (· ≤ ·) atTop (fun t : ℕ =>
        ((Finset.univ.filter fun i : Fin t → Fin k ⊕ Fin k =>
            StrongConv.wordFree (List.ofFn fun j => some (i j)) = 1).card : ℝ) ^ (1 / (t : ℝ))) ∧
      limsup (fun t : ℕ =>
        ((Finset.univ.filter fun i : Fin t → Fin k ⊕ Fin k =>
            StrongConv.wordFree (List.ofFn fun j => some (i j)) = 1).card : ℝ) ^ (1 / (t : ℝ)))
        atTop = 2 * Real.sqrt (2 * k - 1) :=
  Puder.BS.limsup_e k hk

end

section
open Filter Topology
theorem solution (k : ℕ) (hk : 2 ≤ k) :
    IsBoundedUnder (· ≤ ·) atTop (fun t : ℕ =>
        ((Finset.univ.filter fun i : Fin t → Fin k ⊕ Fin k =>
            StrongConv.wordFree (List.ofFn fun j => some (i j)) = 1).card : ℝ) ^ (1 / (t : ℝ))) ∧
      limsup (fun t : ℕ =>
        ((Finset.univ.filter fun i : Fin t → Fin k ⊕ Fin k =>
            StrongConv.wordFree (List.ofFn fun j => some (i j)) = 1).card : ℝ) ^ (1 / (t : ℝ)))
        atTop = 2 * Real.sqrt (2 * k - 1) := by
  exact Puder.limsup_card_wordFree_eq_one_rpow_dev k hk
end
