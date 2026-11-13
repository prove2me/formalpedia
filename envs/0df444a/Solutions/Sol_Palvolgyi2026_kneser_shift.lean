-- Prove2me | solution 1 for Palvolgyi2026.kneser_shift
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:43:51.775277+00:00
-- url     : https://prove2.me/submissions/23ad926e-596e-4997-9faa-08ee8f49616f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Palvolgyi2026_kneser_tucker

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.KS
open Classical
/-! Blueprint: Pálvölgyi's Kneser-shift theorem (Palvolgyi2026.kneser_shift) from Ziegler's
Z_p-Tucker lemma (Ziegler2002.zp_tucker), following Section 4 of arXiv:2608.10865. -/
/-- `𝒜 ∈ P_p(n,k)`: families of `k`-subsets of `[n]`, members of different coordinates disjoint,
not all families empty. -/
def InP {q n : ℕ} (k : ℕ) (𝒜 : Fin (q + 1) → Finset (Finset (Fin n))) : Prop :=
  (∀ i, ∀ A ∈ 𝒜 i, A.card = k) ∧
  (∀ i j, i ≠ j → ∀ A ∈ 𝒜 i, ∀ B ∈ 𝒜 j, Disjoint A B) ∧
  ∃ i, (𝒜 i).Nonempty

end RamseyDisambig.Dev.KS
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.KS.PartKT
open RamseyDisambig.Dev.KS
theorem kneser_tucker (q : ℕ) (hp : (q + 1).Prime) (n k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hnk : (q + 1) * k + m ≤ n + 1)
    (μ : (Fin (q + 1) → Finset (Finset (Fin n))) → Fin (q + 1) × Fin m)
    (hμ : ∀ 𝒜, InP k 𝒜 → μ (fun i => 𝒜 (i - 1)) = ((μ 𝒜).1 + 1, (μ 𝒜).2))
    (htie : ∀ 𝒜 ℬ, InP k 𝒜 → InP k ℬ → 𝒜 ≤ ℬ → (μ 𝒜).2 = (μ ℬ).2 → (μ 𝒜).1 = (μ ℬ).1) :
    False :=
  Palvolgyi2026.kneser_tucker q hp n k m hk hm (by omega) (by omega) μ
    (fun 𝒜 h1 h2 h3 => hμ 𝒜 ⟨h1, h2, h3⟩)
    (fun 𝒜 ℬ a1 a2 a3 b1 b2 b3 => htie 𝒜 ℬ ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩)

end RamseyDisambig.Dev.KS.PartKT
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.KS
open Classical
alias kneser_tucker := RamseyDisambig.Dev.KS.PartKT.kneser_tucker

end RamseyDisambig.Dev.KS
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.KS.PartH
open RamseyDisambig.Dev.KS Classical Fin.CommRing
/-! ### A cyclically equivariant sign -/
theorem const_of_inv {p : ℕ} [NeZero p] (hp : p.Prime) {V : Type*} (R : Fin p → V) (t : Fin p)
    (ht : t ≠ 0) (hR : ∀ x, R (x + t) = R x) : ∀ x y, R x = R y := by
  have := Fact.mk hp
  have hz : ∀ x (z : ℤ), R (x + z • t) = R x := by
    intro x z
    induction z using Int.induction_on with
    | zero => simp
    | succ z ih => rw [add_zsmul, one_zsmul, ← add_assoc, hR, ih]
    | pred z ih =>
      have e : x + (-(z : ℤ) - 1) • t + t = x + (-(z : ℤ)) • t := by
        rw [sub_zsmul, one_zsmul]; abel
      calc R (x + (-(z : ℤ) - 1) • t) = R (x + (-(z : ℤ) - 1) • t + t) := (hR _).symm
        _ = R (x + (-(z : ℤ)) • t) := by rw [e]
        _ = R x := ih
  intro x y
  have hm : y - x ∈ AddSubgroup.zmultiples t :=
    mem_zmultiples_of_prime_card (p := p) (by simp) ht
  obtain ⟨z, hz'⟩ := AddSubgroup.mem_zmultiples_iff.mp hm
  rw [show y = x + z • t by rw [hz']; abel, hz]

theorem shift_unique {q : ℕ} (hp : (q + 1).Prime) {V : Type*} (R : Fin (q + 1) → V)
    (hR : ∃ i j, R i ≠ R j) (a b : Fin (q + 1))
    (h : (fun i => R (i - a)) = fun i => R (i - b)) : a = b := by
  by_contra hab
  have ht : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hinv : ∀ x, R (x + (a - b)) = R x := by
    intro x
    have := congrFun h (x + a)
    rw [show x + a - a = x by abel, show x + a - b = x + (a - b) by abel] at this
    exact this.symm
  obtain ⟨i, j, hij⟩ := hR
  exact hij (const_of_inv hp R _ ht hinv i j)

theorem exists_sign (q : ℕ) (hp : (q + 1).Prime) (V : Type*) :
    ∃ f : (Fin (q + 1) → V) → Fin (q + 1),
      ∀ E : Fin (q + 1) → V, (∃ i j, E i ≠ E j) → f (fun i => E (i - 1)) = f E + 1 := by
  let P : (Fin (q + 1) → V) → (Fin (q + 1) → V) → Prop :=
    fun E F => ∃ s : Fin (q + 1), F = fun i => E (i - s)
  let rep : (Fin (q + 1) → V) → (Fin (q + 1) → V) := fun E =>
    @Classical.epsilon _ ⟨E⟩ (P E)
  have rep_spec : ∀ E, ∃ s : Fin (q + 1), rep E = fun i => E (i - s) := fun E =>
    Classical.epsilon_spec (p := P E) ⟨E, 0, by simp⟩
  have hPshift : ∀ E, P (fun i => E (i - 1)) = P E := by
    intro E
    funext F
    apply propext
    constructor
    · rintro ⟨s, rfl⟩; exact ⟨s + 1, by funext i; congr 1; ring⟩
    · rintro ⟨s, rfl⟩; exact ⟨s - 1, by funext i; simp only; congr 1; ring⟩
  have rep_shift : ∀ E, rep (fun i => E (i - 1)) = rep E := by
    intro E
    show @Classical.epsilon _ ⟨fun i => E (i - 1)⟩ (P (fun i => E (i - 1))) =
      @Classical.epsilon _ ⟨E⟩ (P E)
    rw [hPshift]
  refine ⟨fun E => Classical.epsilon (fun s : Fin (q + 1) => E = fun i => rep E (i - s)), ?_⟩
  intro E hE
  obtain ⟨s₀, hs₀⟩ := rep_spec E
  have hf := Classical.epsilon_spec (p := fun s : Fin (q + 1) => E = fun i => rep E (i - s))
    ⟨-s₀, by rw [hs₀]; funext i; simp⟩
  set fE := Classical.epsilon (fun s : Fin (q + 1) => E = fun i => rep E (i - s)) with hfE
  have hR : ∃ i j, rep E i ≠ rep E j := by
    obtain ⟨i, j, hij⟩ := hE
    refine ⟨i - fE, j - fE, ?_⟩
    intro h; apply hij
    rw [hf]; exact h
  have hg := Classical.epsilon_spec
    (p := fun s : Fin (q + 1) => (fun i => E (i - 1)) = fun i => rep (fun i => E (i - 1)) (i - s))
    ⟨fE + 1, by
      rw [rep_shift]; funext i
      conv_lhs => rw [hf]
      simp only; congr 1; ring⟩
  show Classical.epsilon _ = fE + 1
  apply shift_unique hp (rep E) hR
  rw [← rep_shift E, ← hg]
  conv_lhs => rw [hf]
  rw [rep_shift]
  funext i; simp only; congr 1; ring

end RamseyDisambig.Dev.KS.PartH
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.KS
open Classical

end RamseyDisambig.Dev.KS
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.KS.PartH
open RamseyDisambig.Dev.KS Classical Fin.CommRing
/-! ### Levels and histories -/
@[reducible] def Lv (r : ℕ) : ℕ → Type
  | 0 => Fin r
  | d + 1 => Set (Lv r d)

theorem lv_finite (r : ℕ) : ∀ d, Finite (Lv r d)
  | 0 => show Finite (Fin r) from inferInstance
  | d + 1 => by
    have := lv_finite r d
    show Finite (Set (Lv r d))
    infer_instance

theorem lv_nonempty {r : ℕ} (hr : 0 < r) : ∀ d, Nonempty (Lv r d)
  | 0 => ⟨(⟨0, hr⟩ : Fin r)⟩
  | _ + 1 => ⟨(∅ : Set _)⟩

def le (r : ℕ) : (d : ℕ) → Lv r d → Lv r d → Prop
  | 0, a, b => a = b
  | d + 1, a, b => ∀ x : Lv r d, x ∈ (a : Set (Lv r d)) → x ∈ (b : Set (Lv r d))

theorem le_refl' (r : ℕ) : ∀ (d : ℕ) (a : Lv r d), le r d a a
  | 0, _ => rfl
  | _ + 1, _ => fun _ h => h

theorem le_trans' (r : ℕ) : ∀ (d : ℕ) (a b c : Lv r d), le r d a b → le r d b c → le r d a c
  | 0, _, _, _, h1, h2 => Eq.trans h1 h2
  | _ + 1, _, _, _, h1, h2 => fun x hx => h2 x (h1 x hx)

def dc (r d : ℕ) (S : Set (Lv r d)) : Lv r (d + 1) :=
  ({a | ∃ b ∈ S, le r d a b} : Set (Lv r d))

end RamseyDisambig.Dev.KS.PartH
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.KS.PartH
open RamseyDisambig.Dev.KS Classical Fin.CommRing
variable {q n r : ℕ} (c : (Fin q → Finset (Fin n)) → Fin r)
def H (𝒜 : Fin (q + 1) → Finset (Finset (Fin n))) :
    (d : ℕ) → Fin (q + 1) → (Fin (q + 1) → Finset (Fin n)) → Lv r d
  | 0, i, s => (c (fun t : Fin q => s (i - ((q - 1 - t.val : ℕ) : Fin (q + 1)))) : Fin r)
  | d + 1, i, s => dc r d {x | ∃ B ∈ 𝒜 (i - ((q - (d + 1) : ℕ) : Fin (q + 1))),
      x = H 𝒜 d i (Function.update s (i - ((q - (d + 1) : ℕ) : Fin (q + 1))) B)}

theorem mem_H_succ (𝒜 : Fin (q + 1) → Finset (Finset (Fin n))) (d : ℕ) (i : Fin (q + 1))
    (s : Fin (q + 1) → Finset (Fin n)) (x : Lv r d) :
    x ∈ (H c 𝒜 (d + 1) i s : Set (Lv r d)) ↔
      ∃ b, (∃ B ∈ 𝒜 (i - ((q - (d + 1) : ℕ) : Fin (q + 1))),
        b = H c 𝒜 d i (Function.update s (i - ((q - (d + 1) : ℕ) : Fin (q + 1))) B)) ∧
        le r d x b := by
  simp only [H, dc, Set.mem_setOf_eq]

theorem H_mono {𝒜 ℬ : Fin (q + 1) → Finset (Finset (Fin n))} (h : ∀ t, 𝒜 t ⊆ ℬ t) :
    ∀ (d : ℕ) (i : Fin (q + 1)) (s : Fin (q + 1) → Finset (Fin n)),
      le r d (H c 𝒜 d i s) (H c ℬ d i s)
  | 0, _, _ => rfl
  | d + 1, i, s => by
    intro x hx
    rw [mem_H_succ] at hx ⊢
    obtain ⟨b, ⟨B, hB, rfl⟩, hxb⟩ := hx
    exact ⟨_, ⟨B, h _ hB, rfl⟩, le_trans' r d _ _ _ hxb (H_mono h d i _)⟩

theorem H_local (𝒜 : Fin (q + 1) → Finset (Finset (Fin n))) :
    ∀ (d : ℕ) (i : Fin (q + 1)) (s s' : Fin (q + 1) → Finset (Fin n)),
      (∀ e : ℕ, e < q - d → s (i - (e : Fin (q + 1))) = s' (i - (e : Fin (q + 1)))) →
        H c 𝒜 d i s = H c 𝒜 d i s'
  | 0, i, s, s', h => by
    show (c _ : Fin r) = c _
    congr 1; funext t; apply h; omega
  | d + 1, i, s, s', h => by
    have key : ∀ B, H c 𝒜 d i (Function.update s (i - ((q - (d + 1) : ℕ) : Fin (q + 1))) B) =
        H c 𝒜 d i (Function.update s' (i - ((q - (d + 1) : ℕ) : Fin (q + 1))) B) := by
      intro B
      apply H_local 𝒜 d i
      intro e he
      by_cases hc : i - (e : Fin (q + 1)) = i - ((q - (d + 1) : ℕ) : Fin (q + 1))
      · rw [hc, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hc, Function.update_of_ne hc]
        apply h
        have : e ≠ q - (d + 1) := by rintro rfl; exact hc rfl
        omega
    show dc r d _ = dc r d _
    simp only [key]

theorem H_shift (𝒜 : Fin (q + 1) → Finset (Finset (Fin n))) :
    ∀ (d : ℕ) (i : Fin (q + 1)) (s : Fin (q + 1) → Finset (Fin n)),
      H c (fun t => 𝒜 (t - 1)) d i s = H c 𝒜 d (i - 1) (fun t => s (t + 1))
  | 0, i, s => by
    show (c _ : Fin r) = c _
    congr 1; funext t; congr 1; ring
  | d + 1, i, s => by
    have e1 : i - ((q - (d + 1) : ℕ) : Fin (q + 1)) - 1 =
        i - 1 - ((q - (d + 1) : ℕ) : Fin (q + 1)) := by ring
    have e2 : ∀ B, (fun t => Function.update s (i - ((q - (d + 1) : ℕ) : Fin (q + 1))) B (t + 1)) =
        Function.update (fun t => s (t + 1)) (i - 1 - ((q - (d + 1) : ℕ) : Fin (q + 1))) B := by
      intro B; funext t
      have e3 : i - 1 - ((q - (d + 1) : ℕ) : Fin (q + 1)) =
          i - ((q - (d + 1) : ℕ) : Fin (q + 1)) - 1 := by ring
      simp only [Function.update_apply, e3, eq_sub_iff_add_eq]
    show dc r d _ = dc r d _
    simp only [H_shift 𝒜 d, e1, e2]

theorem cast_inj {q a b : ℕ} (ha : a < q + 1) (hb : b < q + 1)
    (h : ((a : ℕ) : Fin (q + 1)) = b) : a = b := by
  have := congrArg Fin.val h
  simpa [Fin.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this

theorem H_incomp {k : ℕ} (𝒜 : Fin (q + 1) → Finset (Finset (Fin n))) (hP : InP k 𝒜)
    (hc : ∀ A : Fin (q + 1) → Finset (Fin n), (∀ i, (A i).card = k) →
      (∀ i j, i ≠ j → Disjoint (A i) (A j)) → c (fun i => A i.castSucc) ≠ c (fun i => A i.succ)) :
    ∀ d, d ≤ q → ∀ (i : Fin (q + 1)) (s : Fin (q + 1) → Finset (Fin n)), (∀ t, s t ∈ 𝒜 t) →
      ¬ le r d (H c 𝒜 d i s) (H c 𝒜 d (i - 1) s)
  | 0, _, i, s, hs => by
    intro heq
    let A : Fin (q + 1) → Finset (Fin n) := fun u => s (i - ((q - u.val : ℕ) : Fin (q + 1)))
    refine hc A (fun u => hP.1 _ _ (hs _)) ?_ ?_
    · intro u v huv
      refine hP.2.1 _ _ ?_ _ (hs _) _ (hs _)
      intro h
      rw [sub_right_inj] at h
      have := cast_inj (by omega) (by omega) h
      exact huv (Fin.ext (by omega))
    · have h1 : (fun t : Fin q => A t.castSucc) =
          fun t : Fin q => s (i - 1 - ((q - 1 - t.val : ℕ) : Fin (q + 1))) := by
        funext t
        simp only [A, Fin.coe_castSucc]
        have : (q - t.val : ℕ) = (q - 1 - t.val) + 1 := by omega
        rw [this, Nat.cast_add, Nat.cast_one]
        congr 1; ring
      have h2 : (fun t : Fin q => A t.succ) =
          fun t : Fin q => s (i - ((q - 1 - t.val : ℕ) : Fin (q + 1))) := by
        funext t
        simp only [A, Fin.val_succ]
        congr 3; omega
      rw [h1, h2]
      exact heq.symm
  | d + 1, hd, i, s, hs => by
    intro hle
    have hmem : H c 𝒜 d i s ∈ (H c 𝒜 (d + 1) i s : Set (Lv r d)) := by
      rw [mem_H_succ]
      exact ⟨_, ⟨s _, hs _, by rw [Function.update_eq_self]⟩, le_refl' r d _⟩
    have hmem' := hle _ hmem
    rw [mem_H_succ] at hmem'
    obtain ⟨b, ⟨B', hB', rfl⟩, hb⟩ := hmem'
    have hs' : ∀ t, Function.update s (i - 1 - ((q - (d + 1) : ℕ) : Fin (q + 1))) B' t ∈ 𝒜 t := by
      intro t
      by_cases ht : t = i - 1 - ((q - (d + 1) : ℕ) : Fin (q + 1))
      · subst ht; rw [Function.update_self]; exact hB'
      · rw [Function.update_of_ne ht]; exact hs t
    have hpos : i - 1 - ((q - (d + 1) : ℕ) : Fin (q + 1)) = i - ((q - d : ℕ) : Fin (q + 1)) := by
      rw [show q - d = (q - (d + 1)) + 1 by omega, Nat.cast_add, Nat.cast_one]; ring
    have hloc : H c 𝒜 d i s =
        H c 𝒜 d i (Function.update s (i - 1 - ((q - (d + 1) : ℕ) : Fin (q + 1))) B') := by
      apply H_local
      intro e he
      rw [Function.update_of_ne]
      rw [hpos]
      intro h
      rw [sub_right_inj] at h
      have := cast_inj (by omega) (by omega) h
      omega
    rw [hloc] at hb
    exact H_incomp 𝒜 hP hc d (by omega) i _ hs' hb

theorem H_succ_nonempty_iff (𝒜 : Fin (q + 1) → Finset (Finset (Fin n))) (d : ℕ)
    (i : Fin (q + 1)) (s : Fin (q + 1) → Finset (Fin n)) :
    (H c 𝒜 (d + 1) i s : Set (Lv r d)).Nonempty ↔
      (𝒜 (i - ((q - (d + 1) : ℕ) : Fin (q + 1)))).Nonempty := by
  constructor
  · rintro ⟨x, hx⟩
    rw [mem_H_succ] at hx
    obtain ⟨b, ⟨B, hB, rfl⟩, _⟩ := hx
    exact ⟨B, hB⟩
  · rintro ⟨B, hB⟩
    refine ⟨H c 𝒜 d i (Function.update s (i - ((q - (d + 1) : ℕ) : Fin (q + 1))) B), ?_⟩
    rw [mem_H_succ]
    exact ⟨_, ⟨B, hB, rfl⟩, le_refl' r d _⟩

end RamseyDisambig.Dev.KS.PartH
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.KS.PartH
open RamseyDisambig.Dev.KS Classical Fin.CommRing
/-! ### The rank bound -/
theorem sum_ncard_lt {α : Type} [Finite α] {p : ℕ} (E : Fin p → Set α) (hE : ∃ i j, E i ≠ E j) :
    ∑ i, (E i).ncard < p * Nat.card α := by
  have hle : ∀ i ∈ Finset.univ, (E i).ncard ≤ Nat.card α := by
    intro i _
    rw [← Set.ncard_univ]; exact Set.ncard_le_ncard (Set.subset_univ _)
  have hsum : ∑ i, (E i).ncard ≤ ∑ _i : Fin p, Nat.card α := Finset.sum_le_sum hle
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  refine lt_of_le_of_ne hsum ?_
  intro heq
  have heq' : ∑ i, (E i).ncard = ∑ _i : Fin p, Nat.card α := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; exact heq
  rw [Finset.sum_eq_sum_iff_of_le hle] at heq'
  have hall : ∀ i, E i = Set.univ := by
    intro i
    refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ (Set.finite_univ (α := α))
    rw [Set.ncard_univ, heq' i (Finset.mem_univ _)]
  obtain ⟨i, j, hij⟩ := hE
  exact hij (by rw [hall i, hall j])

/-! ### Theorem 4 -/
theorem ks_main (q : ℕ) (hp : (q + 1).Prime) (r : ℕ) :
    ∃ C : ℕ, ∀ n k : ℕ, (q + 1) * k + C ≤ n →
      ∀ c : (Fin q → Finset (Fin n)) → Fin r,
        ∃ A : Fin (q + 1) → Finset (Fin n),
          (∀ i, (A i).card = k) ∧ (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
            c (fun i => A i.castSucc) = c (fun i => A i.succ) := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by have := hp.two_le; omega⟩
  haveI : Finite (Lv r q') := lv_finite r q'
  refine ⟨(q' + 1 + 1) * Nat.card (Lv r q'), ?_⟩
  intro n k hnk c
  by_contra hcon
  push_neg at hcon
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact hcon (fun _ => ∅) (by simp) (by simp) rfl
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with rfl | h
    · exact (c (fun _ => ∅)).elim0
    · exact h
  haveI := lv_nonempty hr q'
  have hN : 0 < Nat.card (Lv r q') := Nat.card_pos
  let D : (Fin (q' + 1 + 1) → Finset (Finset (Fin n))) → Fin (q' + 1 + 1) → Set (Lv r q') :=
    fun 𝒜 i => H c 𝒜 (q' + 1) i (fun _ => ∅)
  have hDs : ∀ 𝒜 i s, (H c 𝒜 (q' + 1) i s : Set (Lv r q')) = D 𝒜 i := by
    intro 𝒜 i s
    apply H_local
    intro e he; omega
  have hDne : ∀ 𝒜 i, (D 𝒜 i).Nonempty ↔ (𝒜 i).Nonempty := by
    intro 𝒜 i
    have := H_succ_nonempty_iff c 𝒜 q' i (fun _ => ∅)
    simpa using this
  have hDnc : ∀ 𝒜, InP k 𝒜 → ∃ i j, D 𝒜 i ≠ D 𝒜 j := by
    intro 𝒜 hP
    by_cases hall : ∀ t, (𝒜 t).Nonempty
    · choose s hs using hall
      refine ⟨0, 0 - 1, ?_⟩
      intro heq
      apply H_incomp c 𝒜 hP hcon (q' + 1) le_rfl 0 s hs
      rw [show (H c 𝒜 (q' + 1) 0 s : Lv r (q' + 1)) = D 𝒜 0 from hDs 𝒜 0 s,
        show (H c 𝒜 (q' + 1) (0 - 1) s : Lv r (q' + 1)) = D 𝒜 (0 - 1) from hDs 𝒜 _ s, heq]
      exact le_refl' r (q' + 1) _
    · push_neg at hall
      obtain ⟨t, ht⟩ := hall
      obtain ⟨j, hj⟩ := hP.2.2
      refine ⟨t, j, ?_⟩
      intro heq
      have h1 := (hDne 𝒜 j).mpr hj
      rw [← heq, hDne, ht] at h1
      exact Finset.not_nonempty_empty h1
  have hDshift : ∀ 𝒜, D (fun i => 𝒜 (i - 1)) = fun i => D 𝒜 (i - 1) := by
    intro 𝒜; funext i
    exact H_shift c 𝒜 (q' + 1) i _
  have hDmono : ∀ 𝒜 ℬ, 𝒜 ≤ ℬ → ∀ i, D 𝒜 i ⊆ D ℬ i := by
    intro 𝒜 ℬ h i
    exact H_mono c (fun t => h t) (q' + 1) i _
  obtain ⟨f, hf⟩ := exists_sign (q' + 1) hp (Set (Lv r q'))
  have hM : 0 < (q' + 1 + 1) * Nat.card (Lv r q') := Nat.mul_pos (by omega) hN
  let μ : (Fin (q' + 1 + 1) → Finset (Finset (Fin n))) →
      Fin (q' + 1 + 1) × Fin ((q' + 1 + 1) * Nat.card (Lv r q')) :=
    fun 𝒜 => (f (D 𝒜), ⟨(∑ i, (D 𝒜 i).ncard) % ((q' + 1 + 1) * Nat.card (Lv r q')),
      Nat.mod_lt _ hM⟩)
  have hlt : ∀ 𝒜, InP k 𝒜 →
      ∑ i, (D 𝒜 i).ncard < (q' + 1 + 1) * Nat.card (Lv r q') :=
    fun 𝒜 hP => sum_ncard_lt (D 𝒜) (hDnc 𝒜 hP)
  apply kneser_tucker (q' + 1) hp n k ((q' + 1 + 1) * Nat.card (Lv r q')) hk hM
    (Nat.le_succ_of_le hnk) μ
  · intro 𝒜 hP
    have hsum : ∑ i, (D 𝒜 (i - 1)).ncard = ∑ i, (D 𝒜 i).ncard :=
      Fintype.sum_equiv (Equiv.subRight 1) _ _ (fun _ => rfl)
    refine Prod.ext ?_ ?_
    · show f (D (fun i => 𝒜 (i - 1))) = f (D 𝒜) + 1
      rw [hDshift]; exact hf _ (hDnc 𝒜 hP)
    · show (⟨_, _⟩ : Fin _) = ⟨_, _⟩
      simp only [hDshift, hsum]
  · intro 𝒜 ℬ hA hB hAB h2
    have hval := congrArg Fin.val h2
    simp only [μ, Nat.mod_eq_of_lt (hlt 𝒜 hA), Nat.mod_eq_of_lt (hlt ℬ hB)] at hval
    have hle : ∀ i ∈ Finset.univ, (D 𝒜 i).ncard ≤ (D ℬ i).ncard :=
      fun i _ => Set.ncard_le_ncard (hDmono 𝒜 ℬ hAB i)
    rw [Finset.sum_eq_sum_iff_of_le hle] at hval
    have hDeq : D 𝒜 = D ℬ := by
      funext i
      exact Set.eq_of_subset_of_ncard_le (hDmono 𝒜 ℬ hAB i) (hval i (Finset.mem_univ _)).ge
    show f (D 𝒜) = f (D ℬ)
    rw [hDeq]

end RamseyDisambig.Dev.KS.PartH
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.KS
open Classical
alias ks_main := RamseyDisambig.Dev.KS.PartH.ks_main

end RamseyDisambig.Dev.KS
end

section
set_option autoImplicit false
namespace Palvolgyi2026
theorem chk_kneser_shift (q : ℕ) (hp : (q + 1).Prime) (r : ℕ) :
    ∃ C : ℕ, ∀ n k : ℕ, (q + 1) * k + C ≤ n →
      ∀ c : (Fin q → Finset (Fin n)) → Fin r,
        ∃ A : Fin (q + 1) → Finset (Fin n),
          (∀ i, (A i).card = k) ∧ (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
            c (fun i => A i.castSucc) = c (fun i => A i.succ) :=
  RamseyDisambig.Dev.KS.ks_main q hp r

end Palvolgyi2026
end

theorem solution : type_of% @Palvolgyi2026.chk_kneser_shift := @Palvolgyi2026.chk_kneser_shift
