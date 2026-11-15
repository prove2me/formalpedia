-- Prove2me | solution 1 for SymBoolPCSP.CFixing.theorem_4_13
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T20:48:45.307674+00:00
-- url     : https://prove2.me/submissions/5ac6c816-1fcd-4f13-9f21-1bc3e3c26443

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

section cfixingAssembly_AcceptedClosure

section cfixingModule_afeba2bdddf74e508a67c139a013eefe

namespace AddClosure

/-- Path lemma: from `s ∈ S`, bounded closure under `+p`, `+q` reaches `s + a p + b q`. -/
theorem mem_add_mul_add_mul {S : Set ℕ} {s p q N : ℕ} (hs : s ∈ S)
    (hP : ∀ x ∈ S, x + p ≤ N → x + p ∈ S) (hQ : ∀ x ∈ S, x + q ≤ N → x + q ∈ S) :
    ∀ a b : ℕ, s + a * p + b * q ≤ N → s + a * p + b * q ∈ S := by
  intro a
  induction a with
  | zero =>
    intro b
    induction b with
    | zero => intro _; simpa using hs
    | succ b ih =>
      intro h
      have h' : s + 0 * p + b * q + q = s + 0 * p + (b + 1) * q := by ring
      rw [← h'] at h ⊢
      exact hQ _ (ih (by omega)) h
  | succ a ih =>
    intro b h
    have h' : s + a * p + b * q + p = s + (a + 1) * p + b * q := by ring
    rw [← h'] at h ⊢
    exact hP _ (ih b (by omega)) h

/-- Coprime representation: if `p, q` are coprime, `0 < p`, and `p * q ≤ k`, then
`k = a p + b q` for some naturals `a, b`. -/
theorem exists_mul_add_mul_of_coprime {p q k : ℕ} (hp : 0 < p) (hc : Nat.Coprime p q)
    (hk : p * q ≤ k) : ∃ a b : ℕ, a * p + b * q = k := by
  have : NeZero p := ⟨hp.ne'⟩
  set b : ℕ := ((k : ZMod p) * (q : ZMod p)⁻¹).val with hb
  have hblt : b < p := ZMod.val_lt _
  have hbq : b * q ≤ k := by
    calc b * q ≤ p * q := Nat.mul_le_mul_right _ hblt.le
      _ ≤ k := hk
  have hmod : ((b * q : ℕ) : ZMod p) = (k : ZMod p) := by
    rw [Nat.cast_mul, hb, ZMod.natCast_zmod_val, mul_assoc, mul_comm ((q : ZMod p)⁻¹),
      ZMod.coe_mul_inv_eq_one q hc.symm, mul_one]
  have hdvd : p ∣ k - b * q := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hbq, hmod, sub_self]
  obtain ⟨a, ha⟩ := hdvd
  exact ⟨a, b, by rw [mul_comm a p, ← ha]; omega⟩

/-- Two-generator closure (bounded Frobenius form). Let `S ⊆ ℕ` contain `s` and be closed under
adding `p` and adding `q` whenever the result is at most `N`, with `p > 0`. Then every `m` with
`s + p q ≤ m ≤ N` and `gcd(p, q) ∣ m - s` lies in `S`. -/
theorem mem_of_add_closed_pair {S : Set ℕ} {s p q N : ℕ} (hp : 0 < p)
    (hs : s ∈ S) (hP : ∀ x ∈ S, x + p ≤ N → x + p ∈ S)
    (hQ : ∀ x ∈ S, x + q ≤ N → x + q ∈ S) {m : ℕ} (hm : s + p * q ≤ m) (hmN : m ≤ N)
    (hg : Nat.gcd p q ∣ m - s) : m ∈ S := by
  set g := Nat.gcd p q with hgdef
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left q hp
  obtain ⟨p', hp'⟩ : g ∣ p := Nat.gcd_dvd_left p q
  obtain ⟨q', hq'⟩ : g ∣ q := Nat.gcd_dvd_right p q
  obtain ⟨k, hk⟩ := hg
  have hp'0 : 0 < p' := by
    rcases Nat.eq_zero_or_pos p' with h | h
    · rw [h, mul_zero] at hp'; omega
    · exact h
  have hcop : Nat.Coprime p' q' := by
    have := Nat.coprime_div_gcd_div_gcd (m := p) (n := q) hg0
    rwa [← hgdef, hp', hq', Nat.mul_div_cancel_left _ hg0,
      Nat.mul_div_cancel_left _ hg0] at this
  have hkge : p' * q' ≤ k := by
    have h1 : g * (g * (p' * q')) ≤ g * k := by
      have : p * q = g * (g * (p' * q')) := by rw [hp', hq']; ring
      rw [← this, ← hk]; omega
    have h2 := Nat.le_of_mul_le_mul_left h1 hg0
    calc p' * q' ≤ g * (p' * q') := Nat.le_mul_of_pos_left _ hg0
      _ ≤ k := h2
  obtain ⟨a, b, hab⟩ := exists_mul_add_mul_of_coprime hp'0 hcop hkge
  have hrep : m = s + a * p + b * q := by
    have : a * p + b * q = m - s := by
      rw [hk, ← hab, hp', hq']; ring
    omega
  rw [hrep] at hmN ⊢
  exact mem_add_mul_add_mul hs hP hQ a b hmN

end AddClosure

open AddClosure in
theorem cfixingFixture_afeba2bdddf74e508a67c139a013eefe {S : Set ℕ} {s p q N : ℕ} (hp : 0 < p)
    (hs : s ∈ S) (hP : ∀ x ∈ S, x + p ≤ N → x + p ∈ S)
    (hQ : ∀ x ∈ S, x + q ≤ N → x + q ∈ S) {m : ℕ} (hm : s + p * q ≤ m) (hmN : m ≤ N)
    (hg : Nat.gcd p q ∣ m - s) : m ∈ S :=
  AddClosure.mem_of_add_closed_pair hp hs hP hQ hm hmN hg

end cfixingModule_afeba2bdddf74e508a67c139a013eefe

section cfixingModule_4fb162d9536c48de9bf26d7ef08c4b2c

open Finset
namespace FinsetParts

/-- Splitting a finite set into parts of prescribed sizes: if `b₁ + ⋯ + bₙ = |X|`, then `X` is the disjoint union of subsets `Y₁, …, Yₙ` with `|Yᵢ| = bᵢ`. -/
theorem exists_parts_card_eq {α : Type*} [DecidableEq α] {n : ℕ} (X : Finset α)
    (b : Fin n → ℕ) (h : ∑ i, b i = X.card) :
    ∃ Y : Fin n → Finset α, (∀ i, Y i ⊆ X) ∧ (∀ i, (Y i).card = b i) ∧
      ∀ x ∈ X, ∃! i, x ∈ Y i := by
  induction n generalizing X with
  | zero =>
    refine ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, ?_⟩
    simp at h
    intro x hx
    rw [Finset.card_eq_zero.mp h.symm] at hx
    simp at hx
  | succ n ih =>
    rw [Fin.sum_univ_succ] at h
    obtain ⟨Y0, hY0X, hY0c⟩ := Finset.exists_subset_card_eq (show b 0 ≤ X.card by omega)
    obtain ⟨Y', hY'X, hY'c, hY'u⟩ := ih (X \ Y0) (fun i => b i.succ)
      (by rw [Finset.card_sdiff_of_subset hY0X]; omega)
    refine ⟨Fin.cons Y0 Y', ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hY0X
      · simpa using (hY'X j).trans Finset.sdiff_subset
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hY0c
      · simpa using hY'c j
    · intro x hx
      by_cases h0 : x ∈ Y0
      · refine ⟨0, by simpa using h0, fun j hj => ?_⟩
        revert hj
        refine Fin.cases (fun _ => rfl) (fun j hj => ?_) j
        simp only [Fin.cons_succ] at hj
        have := hY'X j hj
        simp [h0] at this
      · obtain ⟨j, hj, hju⟩ := hY'u x (by simp [hx, h0])
        refine ⟨j.succ, by simpa using hj, fun i hi => ?_⟩
        revert hi
        refine Fin.cases (fun hi => ?_) (fun i hi => ?_) i
        · simp at hi; exact absurd hi h0
        · simp only [Fin.cons_succ] at hi
          rw [hju i hi]

end FinsetParts

open FinsetParts in
theorem cfixingFixture_4fb162d9536c48de9bf26d7ef08c4b2c {α : Type*} [DecidableEq α] {n : ℕ} (X : Finset α)
    (b : Fin n → ℕ) (h : ∑ i, b i = X.card) :
    ∃ Y : Fin n → Finset α, (∀ i, Y i ⊆ X) ∧ (∀ i, (Y i).card = b i) ∧
      ∀ x ∈ X, ∃! i, x ∈ Y i :=
  FinsetParts.exists_parts_card_eq X b h

end cfixingModule_4fb162d9536c48de9bf26d7ef08c4b2c

section cfixingModule_8cbeee1b9a5b4eec8f2c918644e7a41c

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

namespace Aux_card_lt_of_minimal

theorem hw_eq_sum {k : ℕ} (x : Fin k → Bool) :
    hw x = ∑ c, (if x c = true then 1 else 0) := by
  unfold hw; rw [Finset.card_filter]

theorem hw_equiv {α : Type} [Fintype α] {k : ℕ} (e : α ≃ Fin k) (x : Fin k → Bool) :
    hw x = ∑ a, (if x (e a) = true then 1 else 0) := by
  rw [hw_eq_sum]; exact (Equiv.sum_comp e (fun c => if x c = true then 1 else 0)).symm

theorem neg_of_folded {L : ℕ} {f : (Fin L → Bool) → Bool} (hfold : IsFolded f)
    (x : Fin L → Bool) : f (neg x) = !f x := by
  have hnn : neg (neg x) = x := funext fun i => by simp [neg]
  rw [hfold (neg x), hnn]

end Aux_card_lt_of_minimal

open Aux_card_lt_of_minimal in
/-- Case 2 of BG Lemma 4.12: let `f` be a folded polymorphism of
`(Ham_{b+r}({1, b+r}), Ham_{b+r}({0, …, b+r} \ {b}))` with `b ≥ 1`. If `S` is minimal with
`f(e_S) = 1` (all proper subsets `T ⊂ S` have `f(e_T) = 0`), then `|S| < b`. -/
theorem card_lt_of_minimal {L b r : ℕ} (f : (Fin L → Bool) → Bool) (hfold : IsFolded f)
    (hb : 1 ≤ b)
    (hpol : PolOf (Ham (b + r) {1, b + r}) (Ham (b + r) (Set.Iic (b + r) \ {b})) f)
    (S : Finset (Fin L)) (hS : f (indicator S) = true)
    (hmin : ∀ T ⊂ S, f (indicator T) = false) :
    S.card < b := by
  classical
  by_contra h
  push_neg at h
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  let sz : Fin (b' + 1) → ℕ := Fin.cons (S.card - b') (fun _ => 1)
  have hsum : ∑ i, sz i = S.card := by
    simp only [sz, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    omega
  obtain ⟨T, hTS, hTc, hcov⟩ := FinsetParts.exists_parts_card_eq S sz hsum
  have hne : ∀ i, (T i).Nonempty := by
    intro i
    rw [← Finset.card_pos, hTc i]
    induction i using Fin.cases with
    | zero => simp only [sz, Fin.cons_zero]; omega
    | succ j => simp [sz]
  have hval : ∀ i, f (neg (indicator (S \ T i))) = true := by
    intro i
    rw [neg_of_folded hfold, hmin _ (Finset.sdiff_ssubset (hTS i) (hne i))]; rfl
  have hval2 : f (neg (indicator S)) = false := by
    rw [neg_of_folded hfold, hS]; rfl
  have hcard : Fintype.card (Fin (b' + 1) ⊕ Fin r) = b' + 1 + r := by simp
  let e := Fintype.equivFinOfCardEq hcard
  let v : Fin (b' + 1) ⊕ Fin r → Fin L → Bool :=
    Sum.elim (fun i => neg (indicator (S \ T i))) (fun _ => neg (indicator S))
  have key := hpol (fun l c => v (e.symm c) l) (by
    intro l
    simp only [Ham, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [hw_equiv e]
    simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type]
    by_cases hl : l ∈ S
    · left
      obtain ⟨i0, hi0, huniq⟩ := hcov l hl
      have hA : ∀ i, (if v (Sum.inl i) l = true then 1 else 0 : ℕ) =
          if l ∈ T i then 1 else 0 := fun i => by
        by_cases hli : l ∈ T i <;> simp [v, neg, indicator, hl, hli]
      simp only [hA]
      rw [Finset.sum_eq_single i0 (fun j _ hj => if_neg (fun h' => hj (huniq j h')))
        (by simp), if_pos hi0]
      simp [v, neg, indicator, hl]
    · right
      simp [v, neg, indicator, hl])
  simp only [Ham, Set.mem_setOf_eq, Set.mem_diff, Set.mem_Iic, Set.mem_singleton_iff] at key
  rw [hw_equiv e] at key
  simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, v, Sum.elim_inl, Sum.elim_inr,
    hval, hval2] at key
  simp at key

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem cfixingFixture_8cbeee1b9a5b4eec8f2c918644e7a41c {L b r : ℕ} (f : (Fin L → Bool) → Bool) (hfold : IsFolded f)
    (hb : 1 ≤ b)
    (hpol : PolOf (Ham (b + r) {1, b + r}) (Ham (b + r) (Set.Iic (b + r) \ {b})) f)
    (S : Finset (Fin L)) (hS : f (indicator S) = true)
    (hmin : ∀ T ⊂ S, f (indicator T) = false) :
    S.card < b :=
  SymBoolPCSP.CFixing.card_lt_of_minimal f hfold hb hpol S hS hmin

end cfixingModule_8cbeee1b9a5b4eec8f2c918644e7a41c

section cfixingModule_2c1564c6bdfa4a80bf4bdb9286ac3fde

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

/-- If every `m`-element subset `Z ⊆ I` has `f(e_Z) = 1` and at most `c` pairwise disjoint sets
can have `f(e_{S_i}) = 1`, then `|I| < m (c + 1)` (BG, proof of Lemma 4.12, Case 1). -/
theorem card_lt_of_subsets_true {L : ℕ} (f : (Fin L → Bool) → Bool) (c m : ℕ)
    (I : Finset (Fin L)) (hI : ∀ Z ⊆ I, Z.card = m → f (indicator Z) = true)
    (hdisj : ∀ (ℓ : ℕ) (S : Fin ℓ → Finset (Fin L)), (∀ i j, i ≠ j → Disjoint (S i) (S j)) →
      (∀ i, f (indicator (S i)) = true) → ℓ ≤ c) :
    I.card < m * (c + 1) := by
  classical
  by_contra h
  push_neg at h
  obtain ⟨J, hJI, hJc⟩ := Finset.exists_subset_card_eq h
  obtain ⟨Y, hYJ, hYc, hcov⟩ := FinsetParts.exists_parts_card_eq J (fun _ : Fin (c + 1) => m)
    (by simp [hJc, mul_comm])
  have := hdisj (c + 1) Y
    (fun i j hij => Finset.disjoint_left.mpr fun x hxi hxj =>
      hij (((hcov x (hYJ i hxi)).unique hxi hxj)))
    (fun i => hI (Y i) ((hYJ i).trans hJI) (hYc i))
  omega

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem cfixingFixture_2c1564c6bdfa4a80bf4bdb9286ac3fde {L : ℕ} (f : (Fin L → Bool) → Bool) (c m : ℕ)
    (I : Finset (Fin L)) (hI : ∀ Z ⊆ I, Z.card = m → f (indicator Z) = true)
    (hdisj : ∀ (ℓ : ℕ) (S : Fin ℓ → Finset (Fin L)), (∀ i j, i ≠ j → Disjoint (S i) (S j)) →
      (∀ i, f (indicator (S i)) = true) → ℓ ≤ c) :
    I.card < m * (c + 1) :=
  SymBoolPCSP.CFixing.card_lt_of_subsets_true f c m I hI hdisj

end cfixingModule_2c1564c6bdfa4a80bf4bdb9286ac3fde

section cfixingModule_cf7c13c53a654cc3a7c567164aa28b9e

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

namespace Aux_cfixing_of_small_witness

theorem indicator_filter {L : ℕ} (x : Fin L → Bool) :
    x = indicator (Finset.univ.filter (fun i => x i = true)) := by
  funext i; simp [indicator]

end Aux_cfixing_of_small_witness

open Aux_cfixing_of_small_witness in
/-- A generic `C`-fixing criterion (BG, proof of Lemma 4.12, Case 2): suppose `f(0) = 0`,
every `X` with `f(e_X) = 1` contains some `T` with `f(e_T) = 1` and `|T| ≤ B`, and at most `c`
pairwise disjoint sets `S_i` can have `f(e_{S_i}) = 1`. Then `f` is `(c + 1) B`-fixing. -/
theorem cfixing_of_small_witness {L : ℕ} (f : (Fin L → Bool) → Bool)
    (h0 : f (fun _ => false) = false) (B c : ℕ)
    (hsmall : ∀ X : Finset (Fin L), f (indicator X) = true →
      ∃ T ⊆ X, f (indicator T) = true ∧ T.card ≤ B)
    (hdisj : ∀ (ℓ : ℕ) (S : Fin ℓ → Finset (Fin L)), (∀ i j, i ≠ j → Disjoint (S i) (S j)) →
      (∀ i, f (indicator (S i)) = true) → ℓ ≤ c) :
    IsCFixing ((c + 1) * B) f := by
  classical
  have key : ∀ n : ℕ, (∃ U : Finset (Fin L), U.card ≤ n * B ∧
      ∀ X : Finset (Fin L), Disjoint X U → f (indicator X) = false) ∨
      (∃ S : Fin n → Finset (Fin L), (∀ i j, i ≠ j → Disjoint (S i) (S j)) ∧
        (∀ i, f (indicator (S i)) = true) ∧ ∀ i, (S i).card ≤ B) := by
    intro n
    induction n with
    | zero => exact Or.inr ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
        fun i => i.elim0⟩
    | succ n ih =>
      rcases ih with ⟨U, hU, hX⟩ | ⟨S, hdis, htrue, hcard⟩
      · exact Or.inl ⟨U, le_trans hU (Nat.mul_le_mul_right _ (Nat.le_succ n)), hX⟩
      · by_cases hall : ∀ X : Finset (Fin L), Disjoint X (Finset.univ.biUnion S) →
            f (indicator X) = false
        · refine Or.inl ⟨Finset.univ.biUnion S, ?_, hall⟩
          calc (Finset.univ.biUnion S).card ≤ ∑ i, (S i).card := Finset.card_biUnion_le
            _ ≤ ∑ _i : Fin n, B := Finset.sum_le_sum (fun i _ => hcard i)
            _ = n * B := by simp
            _ ≤ (n + 1) * B := Nat.mul_le_mul_right _ (Nat.le_succ n)
        · push_neg at hall
          obtain ⟨X, hXd, hXt⟩ := hall
          obtain ⟨T, hTX, hTt, hTc⟩ := hsmall X (by simpa using hXt)
          have hTd : ∀ i, Disjoint T (S i) := fun i =>
            Finset.disjoint_of_subset_left hTX (Finset.disjoint_of_subset_right
              (Finset.subset_biUnion_of_mem S (Finset.mem_univ i)) hXd)
          refine Or.inr ⟨Fin.cons T S, ?_, ?_, ?_⟩
          · intro i j hij
            induction i using Fin.cases with
            | zero =>
              induction j using Fin.cases with
              | zero => exact absurd rfl hij
              | succ j => simpa using hTd j
            | succ i =>
              induction j using Fin.cases with
              | zero => simpa using (hTd i).symm
              | succ j =>
                simpa using hdis i j (fun h' => hij (by rw [h']))
          · intro i
            induction i using Fin.cases with
            | zero => simpa using hTt
            | succ i => simpa using htrue i
          · intro i
            induction i using Fin.cases with
            | zero => simpa using hTc
            | succ i => simpa using hcard i
  rcases key (c + 1) with ⟨U, hU, hX⟩ | ⟨S, hdis, htrue, _⟩
  · refine ⟨U, hU, fun x hx => ?_⟩
    rw [h0, indicator_filter x]
    apply hX
    exact Finset.disjoint_left.mpr fun i hi hiU => by
      have := hx i hiU
      simp [this] at hi
  · have := hdisj (c + 1) S hdis htrue
    omega

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem cfixingFixture_cf7c13c53a654cc3a7c567164aa28b9e {L : ℕ} (f : (Fin L → Bool) → Bool)
    (h0 : f (fun _ => false) = false) (B c : ℕ)
    (hsmall : ∀ X : Finset (Fin L), f (indicator X) = true →
      ∃ T ⊆ X, f (indicator T) = true ∧ T.card ≤ B)
    (hdisj : ∀ (ℓ : ℕ) (S : Fin ℓ → Finset (Fin L)), (∀ i j, i ≠ j → Disjoint (S i) (S j)) →
      (∀ i, f (indicator (S i)) = true) → ℓ ≤ c) :
    IsCFixing ((c + 1) * B) f :=
  SymBoolPCSP.CFixing.cfixing_of_small_witness f h0 B c hsmall hdisj

end cfixingModule_cf7c13c53a654cc3a7c567164aa28b9e

section cfixingModule_888f41edaad5427aacb71e8c73b32fff

open PCSPBLPAff.Symmetric

namespace Aux_SymBoolPCSP_CFixing_claim_4_2
open SymBoolPCSP.CFixing

theorem hw_eq_sum {n : ℕ} (x : Fin n → Bool) : hw x = ∑ i, if x i = true then 1 else 0 := by
  unfold hw
  rw [Finset.card_filter]

theorem hw_snoc {n : ℕ} (y : Fin n → Bool) (b : Bool) :
    hw (Fin.snoc (α := fun _ => Bool) y b) = hw y + (if b = true then 1 else 0) := by
  rw [hw_eq_sum, hw_eq_sum, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem hw_le {n : ℕ} (y : Fin n → Bool) : hw y ≤ n := by
  unfold hw
  exact (Finset.card_filter_le _ _).trans (by simp)

end Aux_SymBoolPCSP_CFixing_claim_4_2

open SymBoolPCSP.CFixing Aux_SymBoolPCSP_CFixing_claim_4_2 in
theorem _root_.SymBoolPCSP.CFixing.claim_4_2 {k : ℕ} (hk : 1 ≤ k) (S T : Set ℕ) (hST : S ⊆ T) (hT : T ⊆ Set.Iic k)
    {L : ℕ} (f : (Fin L → Bool) → Bool) (hidem : IsIdempotent f)
    (hf : PolOf (Ham k S) (Ham k T) f) :
    PolOf (Ham (k - 1) (S \ {k})) (Ham (k - 1) (T \ {k})) f := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  show PolOf (Ham k' (S \ {k' + 1})) (Ham k' (T \ {k' + 1})) f
  intro M hM
  have hM' : ∀ l, (Fin.snoc (α := fun _ => Bool) (M l) false) ∈ Ham (k' + 1) S := by
    intro l
    have h := hM l
    simp only [Ham, Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff] at h ⊢
    rw [hw_snoc]
    simpa using h.1
  have h := hf (fun l => Fin.snoc (α := fun _ => Bool) (M l) false) hM'
  have hz : (fun c => f (fun l => Fin.snoc (α := fun _ => Bool) (M l) false c)) =
      Fin.snoc (α := fun _ => Bool) (fun c => f (fun l => M l c)) false := by
    funext c
    refine Fin.lastCases ?_ (fun i => ?_) c
    · simp only [Fin.snoc_last]
      exact hidem.1
    · simp only [Fin.snoc_castSucc]
  rw [hz] at h
  simp only [Ham, Set.mem_setOf_eq, hw_snoc] at h
  simp only [Ham, Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff]
  refine ⟨by simpa using h, ?_⟩
  have := hw_le (fun c => f (fun l => M l c))
  omega

end cfixingModule_888f41edaad5427aacb71e8c73b32fff

section cfixingModule_9e74cd04ae664d4e88f720a8660fcd85

open PCSPBLPAff.Symmetric

open SymBoolPCSP.CFixing in
theorem _root_.SymBoolPCSP.CFixing.claim_4_3 {k L : ℕ} (P Q : Set (Fin k → Bool)) (hPQ : P ⊆ Q) (S : Finset (Fin k))
    (f : (Fin L → Bool) → Bool) (hfold : IsFolded f) :
    PolOf P Q f ↔ PolOf (flipRel S P) (flipRel S Q) f := by
  have key : ∀ (v : Fin L → Bool) (b : Bool), f (fun l => xor (v l) b) = xor (f v) b := by
    intro v b
    cases b
    · simp
    · have h := hfold (fun l => xor (v l) true)
      have hn : neg (fun l => xor (v l) true) = v := by
        funext l; simp [neg]
      rw [hn] at h
      rw [h]; simp
  constructor
  · intro hf M hM
    have := hf (fun l c => xor (M l c) (indicator S c)) hM
    show (fun i => xor (f (fun l => M l i)) (indicator S i)) ∈ Q
    convert this using 1
    funext c
    rw [key (fun l => M l c) (indicator S c)]
  · intro hf M hM
    have hM' : ∀ l, (fun c => xor (M l c) (indicator S c)) ∈ flipRel S P := by
      intro l
      show (fun i => xor (xor (M l i) (indicator S i)) (indicator S i)) ∈ P
      convert hM l using 1
      funext i; simp
    have := hf (fun l c => xor (M l c) (indicator S c)) hM'
    change (fun i => xor (f (fun l => xor (M l i) (indicator S i))) (indicator S i)) ∈ Q at this
    convert this using 1
    funext c
    rw [key (fun l => M l c) (indicator S c)]
    simp

end cfixingModule_9e74cd04ae664d4e88f720a8660fcd85

section cfixingModule_09d408bdf9f94947b06d27e22e509668

open PCSPBLPAff.Symmetric

namespace Aux_SymBoolPCSP_CFixing_claim_4_4
open SymBoolPCSP.CFixing

theorem hw_eq_sum {n : ℕ} (x : Fin n → Bool) : hw x = ∑ i, if x i = true then 1 else 0 := by
  unfold hw
  rw [Finset.card_filter]

theorem hw_snoc {n : ℕ} (y : Fin n → Bool) (b : Bool) :
    hw (Fin.snoc (α := fun _ => Bool) y b) = hw y + (if b = true then 1 else 0) := by
  rw [hw_eq_sum, hw_eq_sum, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem hw_le {n : ℕ} (y : Fin n → Bool) : hw y ≤ n := by
  unfold hw
  exact (Finset.card_filter_le _ _).trans (by simp)

end Aux_SymBoolPCSP_CFixing_claim_4_4

open SymBoolPCSP.CFixing Aux_SymBoolPCSP_CFixing_claim_4_4 in
theorem _root_.SymBoolPCSP.CFixing.claim_4_4 {k : ℕ} (hk : 1 ≤ k) (S T : Set ℕ) (hST : S ⊆ T) (hT : T ⊆ Set.Iic k)
    {L : ℕ} (f : (Fin L → Bool) → Bool) (hidem : IsIdempotent f) (hfold : IsFolded f)
    (hf : PolOf (Ham k S) (Ham k T) f) :
    PolOf (Ham (k - 1) {l | l + 1 ∈ S}) (Ham (k - 1) {l | l + 1 ∈ T}) f := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  show PolOf (Ham k' {l | l + 1 ∈ S}) (Ham k' {l | l + 1 ∈ T}) f
  intro M hM
  have hM' : ∀ l, (Fin.snoc (α := fun _ => Bool) (M l) true) ∈ Ham (k' + 1) S := by
    intro l
    have h := hM l
    simp only [Ham, Set.mem_setOf_eq] at h ⊢
    rw [hw_snoc]
    simpa using h
  have h := hf (fun l => Fin.snoc (α := fun _ => Bool) (M l) true) hM'
  have hz : (fun c => f (fun l => Fin.snoc (α := fun _ => Bool) (M l) true c)) =
      Fin.snoc (α := fun _ => Bool) (fun c => f (fun l => M l c)) true := by
    funext c
    refine Fin.lastCases ?_ (fun i => ?_) c
    · simp only [Fin.snoc_last]
      exact hidem.2
    · simp only [Fin.snoc_castSucc]
  rw [hz] at h
  simp only [Ham, Set.mem_setOf_eq, hw_snoc] at h
  simp only [Ham, Set.mem_setOf_eq]
  simpa using h

end cfixingModule_09d408bdf9f94947b06d27e22e509668

section cfixingModule_dddc0649ffda4f8cbedaa3afe5bd07ed

open PCSPBLPAff.Symmetric

open SymBoolPCSP.CFixing in
theorem _root_.SymBoolPCSP.CFixing.corollary_4_11 {τ : Type} [Fintype τ] {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPF : IsPromiseFamily 𝔸 𝔹) (hsym : IsSymmetricFamily 𝔸 𝔹) (hfold : IsFoldedFamily 𝔸 𝔹)
    (hidem : IsIdempotentFamily 𝔸 𝔹) (L₁ L₂ : ℕ) (hL₁ : Odd L₁) (hL₂ : Odd L₂)
    (hPar : ¬ IsPolymorphism 𝔸 𝔹 (Par L₁)) (hAT : ¬ IsPolymorphism 𝔸 𝔹 (AT L₂))
    (c : ℕ) (hc : ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsPolymorphism 𝔸 𝔹 f →
      (Finset.univ.filter (fun i : Fin L => f (indicator {i}) = true)).card ≤ c) :
    ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsPolymorphism 𝔸 𝔹 f →
      ∀ (ℓ : ℕ) (S : Fin ℓ → Finset (Fin L)), (∀ i j, i ≠ j → Disjoint (S i) (S j)) →
        (∀ i, f (indicator (S i)) = true) → ℓ ≤ c := by
  intro L f hf ℓ S hdisj hS
  let π : Fin L → Fin (ℓ + 1) := fun j =>
    if h : ∃ i, j ∈ S i then (Classical.choose h).succ else 0
  have hπ : ∀ i j, π j = i.succ ↔ j ∈ S i := by
    intro i j
    simp only [π]
    split_ifs with h
    · have hcs := Classical.choose_spec h
      constructor
      · intro e
        rw [Fin.succ_inj] at e
        rw [← e]; exact hcs
      · intro hj
        rw [Fin.succ_inj]
        by_contra hne
        exact Finset.disjoint_left.mp (hdisj _ _ hne) hcs hj
    · constructor
      · intro e; exact absurd e.symm (Fin.succ_ne_zero i)
      · intro hj; exact absurd ⟨i, hj⟩ h
  let g : (Fin (ℓ + 1) → Bool) → Bool := fun x => f (x ∘ π)
  have hg : IsPolymorphism 𝔸 𝔹 g := by
    intro R M hM
    exact hf R (fun j => M (π j)) (fun j => hM (π j))
  have hgi : ∀ i : Fin ℓ, g (indicator {i.succ}) = true := by
    intro i
    have e : (indicator {i.succ} ∘ π) = indicator (S i) := by
      funext j
      simp only [Function.comp, indicator, Finset.mem_singleton]
      rw [decide_eq_decide]
      exact hπ i j
    show f (indicator {i.succ} ∘ π) = true
    rw [e]; exact hS i
  have hcard := hc (ℓ + 1) g hg
  have hsub : (Finset.univ.image Fin.succ : Finset (Fin (ℓ + 1))) ⊆
      Finset.univ.filter (fun i : Fin (ℓ + 1) => g (indicator {i}) = true) := by
    intro k hk
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgi i⟩
  have h2 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (Fin.succ_injective _), Finset.card_univ,
    Fintype.card_fin] at h2
  omega

end cfixingModule_dddc0649ffda4f8cbedaa3afe5bd07ed

section cfixingModule_e2b263002a5b47e88d01ed86eff3c1b1

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

namespace Aux_eq_false_of_vanish_increasing

theorem indicator_filter {L : ℕ} (x : Fin L → Bool) :
    x = indicator (Finset.univ.filter (fun i => x i = true)) := by
  funext i; simp [indicator]

end Aux_eq_false_of_vanish_increasing

open Aux_eq_false_of_vanish_increasing in
/-- If `f(0) = 0`, then `f(x) = 0` for every `x` vanishing on the set of coordinates on which
`f` is somewhere-increasing, i.e. the `j` with `f(e_Y) = 0`, `f(e_{Y ∪ {j}}) = 1` for some
`Y ∌ j` (BG, proof of Lemma 4.12, Case 1). -/
theorem eq_false_of_vanish_increasing {L : ℕ} (f : (Fin L → Bool) → Bool)
    (h0 : f (fun _ => false) = false) (x : Fin L → Bool)
    (hx : ∀ i ∈ Finset.univ.filter (fun j : Fin L => ∃ Y : Finset (Fin L), j ∉ Y ∧
      f (indicator Y) = false ∧ f (indicator (insert j Y)) = true), x i = false) :
    f x = false := by
  classical
  have claim : ∀ X : Finset (Fin L), f (indicator X) = true → ∃ j ∈ X, ∃ Y : Finset (Fin L),
      j ∉ Y ∧ f (indicator Y) = false ∧ f (indicator (insert j Y)) = true := by
    intro X
    induction X using Finset.induction_on with
    | empty =>
      intro h
      have he : indicator (∅ : Finset (Fin L)) = fun _ => false := funext fun i => by
        simp [indicator]
      rw [he, h0] at h; exact absurd h (by simp)
    | @insert a X ha ih =>
      intro h
      cases hX : f (indicator X) with
      | true =>
        obtain ⟨j, hj, rest⟩ := ih hX
        exact ⟨j, Finset.mem_insert_of_mem hj, rest⟩
      | false => exact ⟨a, Finset.mem_insert_self a X, X, ha, hX, h⟩
  by_contra h
  have ht : f x = true := by simpa using h
  rw [indicator_filter x] at ht
  obtain ⟨j, hj, hjI⟩ := claim _ ht
  have h1 := hx j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjI⟩)
  have h2 : x j = true := (Finset.mem_filter.mp hj).2
  rw [h1] at h2; exact absurd h2 (by simp)

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem cfixingFixture_e2b263002a5b47e88d01ed86eff3c1b1 {L : ℕ} (f : (Fin L → Bool) → Bool)
    (h0 : f (fun _ => false) = false) (x : Fin L → Bool)
    (hx : ∀ i ∈ Finset.univ.filter (fun j : Fin L => ∃ Y : Finset (Fin L), j ∉ Y ∧
      f (indicator Y) = false ∧ f (indicator (insert j Y)) = true), x i = false) :
    f x = false :=
  SymBoolPCSP.CFixing.eq_false_of_vanish_increasing f h0 x hx

end cfixingModule_e2b263002a5b47e88d01ed86eff3c1b1

section cfixingModule_c948aab7027f4f8fb2c2fecf45ce391b

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

namespace Aux_image_negRel_of_folded

theorem neg_neg' {k : ℕ} (x : Fin k → Bool) : neg (neg x) = x := by
  funext i; simp [neg]

end Aux_image_negRel_of_folded

open Aux_image_negRel_of_folded in
/-- For a folded `f` (`f(x) = ¬f(x̄)`), images commute with negation: `f(¬P) = ¬f(P)`. -/
theorem image_negRel_of_folded {k L : ℕ} (f : (Fin L → Bool) → Bool) (hf : IsFolded f)
    (P : Set (Fin k → Bool)) : image f (negRel P) = negRel (image f P) := by
  have hfn : ∀ v, f (neg v) = !f v := fun v => by rw [hf (neg v), neg_neg']
  ext y; constructor
  · rintro ⟨M, hM, rfl⟩
    choose N hN hNM using hM
    refine ⟨fun c => f (fun l => N l c), ⟨N, hN, rfl⟩, ?_⟩
    funext c
    have : (fun l => M l c) = neg (fun l => N l c) := by
      funext l; rw [← hNM l]; rfl
    simp only [neg, this, hfn]
  · rintro ⟨y', ⟨N, hN, rfl⟩, rfl⟩
    refine ⟨fun l => neg (N l), fun l => ⟨N l, hN l, rfl⟩, ?_⟩
    funext c
    have : (fun l => neg (N l) c) = neg (fun l => N l c) := rfl
    rw [this, hfn]; rfl

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem cfixingFixture_c948aab7027f4f8fb2c2fecf45ce391b {k L : ℕ} (f : (Fin L → Bool) → Bool) (hf : IsFolded f)
    (P : Set (Fin k → Bool)) : image f (negRel P) = negRel (image f P) :=
  SymBoolPCSP.CFixing.image_negRel_of_folded f hf P

end cfixingModule_c948aab7027f4f8fb2c2fecf45ce391b

section cfixingModule_6db458b0c67b4a01a2ac506c70555d79

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

namespace Aux_image_subset_of_conservative

theorem const_of_mem_ham0k {k : ℕ} {x : Fin k → Bool} (hx : x ∈ Ham k {0, k}) :
    (∀ c, x c = false) ∨ (∀ c, x c = true) := by
  simp only [Ham, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, hw] at hx
  rcases hx with h | h
  · left; intro c
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
    simpa using h (Finset.mem_univ c)
  · right; intro c
    have : Finset.univ.filter (fun i => x i = true) = Finset.univ :=
      Finset.eq_univ_of_card _ (by simpa using h)
    have hc := Finset.mem_univ c
    rw [← this, Finset.mem_filter] at hc
    exact hc.2

end Aux_image_subset_of_conservative

open Aux_image_subset_of_conservative in
/-- A conservative function (`f(v)` is always one of the entries of `v`) maps every relation consisting of constant tuples into itself: `f(P) ⊆ P` whenever `P ⊆ Ham_k({0, k})`. -/
theorem image_subset_of_conservative {k L : ℕ} (f : (Fin L → Bool) → Bool)
    (hf : ∀ v, ∃ l, f v = v l) (P : Set (Fin k → Bool)) (hP : P ⊆ Ham k {0, k}) :
    image f P ⊆ P := by
  rintro y ⟨M, hM, rfl⟩
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    obtain ⟨l, -⟩ := hf (fun _ => false)
    have : (fun c : Fin 0 => f (fun l => M l c)) = M l := funext (fun c => c.elim0)
    rw [this]; exact hM l
  · let c0 : Fin k := ⟨0, hk⟩
    obtain ⟨l, hl⟩ := hf (fun l => M l c0)
    have hcol : ∀ c, (fun l => M l c) = fun l => M l c0 := by
      intro c; funext l
      rcases const_of_mem_ham0k (hP (hM l)) with h | h <;> simp [h]
    have : (fun c => f (fun l => M l c)) = M l := by
      funext c
      rw [hcol c, hl]
      rcases const_of_mem_ham0k (hP (hM l)) with h | h <;> simp [h]
    rw [this]; exact hM l

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem cfixingFixture_6db458b0c67b4a01a2ac506c70555d79 {k L : ℕ} (f : (Fin L → Bool) → Bool)
    (hf : ∀ v, ∃ l, f v = v l) (P : Set (Fin k → Bool)) (hP : P ⊆ Ham k {0, k}) :
    image f P ⊆ P :=
  SymBoolPCSP.CFixing.image_subset_of_conservative f hf P hP

end cfixingModule_6db458b0c67b4a01a2ac506c70555d79

section cfixingModule_0e11fca7777743c3863cde0035943598

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

/-- A symmetric Boolean relation is the Hamming relation of its set of weights: `P = Ham_k({|x| : x ∈ P})`. -/
theorem isSymmetricRel_eq_ham {k : ℕ} {P : Set (Fin k → Bool)} (hP : IsSymmetricRel P) :
    P = Ham k {s | ∃ x ∈ P, hw x = s} := by
  ext y; constructor
  · intro hy; exact ⟨y, hy, rfl⟩
  · rintro ⟨x, hx, hxy⟩
    have c1 : Fintype.card {c // y c = true} = Fintype.card {c // x c = true} := by
      rw [Fintype.card_subtype, Fintype.card_subtype]; exact hxy.symm
    have c2 : Fintype.card {c // ¬ y c = true} = Fintype.card {c // ¬ x c = true} := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, c1]
    let e1 := Fintype.equivOfCardEq c1
    let e2 := Fintype.equivOfCardEq c2
    have : y = x ∘ (e1.subtypeCongr e2) := by
      funext c
      by_cases hc : y c = true
      · rw [Function.comp_apply, Equiv.subtypeCongr, Equiv.trans_apply, Equiv.trans_apply,
          Equiv.sumCompl_symm_apply_of_pos (p := fun c => y c = true) hc]
        simp only [Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
        rw [hc, (e1 ⟨c, hc⟩).2]
      · rw [Function.comp_apply, Equiv.subtypeCongr, Equiv.trans_apply, Equiv.trans_apply,
          Equiv.sumCompl_symm_apply_of_neg (p := fun c => y c = true) hc]
        simp only [Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]
        have := (e2 ⟨c, hc⟩).2
        simp only [Bool.not_eq_true] at hc this
        rw [hc, this]
    rw [this]; exact hP x hx _

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem cfixingFixture_0e11fca7777743c3863cde0035943598 {k : ℕ} {P : Set (Fin k → Bool)} (hP : IsSymmetricRel P) :
    P = Ham k {s | ∃ x ∈ P, hw x = s} :=
  SymBoolPCSP.CFixing.isSymmetricRel_eq_ham hP

end cfixingModule_0e11fca7777743c3863cde0035943598

section cfixingModule_cde05dcba18e4987b4f538d942c2a14c

open PCSPBLPAff.Symmetric

open SymBoolPCSP.CFixing in
theorem _root_.SymBoolPCSP.CFixing.lemma_2_13_1 {τ : Type} [Fintype τ] {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPF : IsPromiseFamily 𝔸 𝔹) (hnd : IsNonDegenerateFamily 𝔸 𝔹)
    (hex : ∃ (L : ℕ) (f : (Fin L → Bool) → Bool), IsPolymorphism 𝔸 𝔹 f ∧ ¬ IsIdempotent f) :
    ∀ (L : ℕ) (f : (Fin L → Bool) → Bool),
      IsPolymorphism 𝔸 𝔹 f ↔
        (IsPolymorphism (withConsts 𝔸) (withConsts 𝔹) f ∨
          ∃ g : (Fin L → Bool) → Bool,
            IsPolymorphism (withConsts 𝔸) (withConsts (negStruct 𝔹)) g ∧ f = fun x => !g x) := by
  intro L f
  constructor
  · intro hf
    have h01 := hnd L f hf
    unfold IsNonDegenerate at h01
    -- constant rows
    have hconst : ∀ (b : Bool) (M : Fin L → Fin 1 → Bool), (∀ l, M l ∈ ({fun _ => b} : Set (Fin 1 → Bool))) →
        ∀ c, (fun l => M l c) = fun _ => b := by
      intro b M hM c
      funext l
      have := hM l
      rw [Set.mem_singleton_iff] at this
      rw [this]
    cases h0 : f (fun _ => false) <;> cases h1 : f (fun _ => true)
    · rw [h0, h1] at h01; exact absurd rfl h01
    · left
      intro R M hM
      cases R with
      | inl R => exact hf R M hM
      | inr b =>
        show (fun c : Fin 1 => f (fun l => M l c)) = fun _ => b
        funext c
        rw [hconst b M hM c]
        cases b
        · exact h0
        · exact h1
    · right
      refine ⟨fun x => !f x, ?_, ?_⟩
      · intro R M hM
        cases R with
        | inl R =>
          show (fun c => !f (fun l => M l c)) ∈ neg '' (𝔹.rel R)
          exact ⟨_, hf R M hM, rfl⟩
        | inr b =>
          show (fun c : Fin 1 => !f (fun l => M l c)) = fun _ => b
          funext c
          rw [hconst b M hM c]
          cases b
          · rw [h0]; rfl
          · rw [h1]; rfl
      · funext x
        simp
    · rw [h0, h1] at h01; exact absurd rfl h01
  · rintro (h | ⟨g, hg, rfl⟩)
    · intro R M hM
      exact h (Sum.inl R) M hM
    · intro R M hM
      obtain ⟨y, hy, hyeq⟩ := hg (Sum.inl R) M hM
      have : (fun c => !g (fun l => M l c)) = y := by
        funext c
        have := congrFun hyeq c
        simp only [neg] at this
        rw [← this, Bool.not_not]
      rw [this]; exact hy

end cfixingModule_cde05dcba18e4987b4f538d942c2a14c

section cfixingModule_1a50b454778a49f2935ed36458195d37

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

namespace Aux_majImage_ham_upper

theorem hw_decide_mem {k : ℕ} (T : Finset (Fin k)) : hw (fun c => decide (c ∈ T)) = T.card := by
  unfold hw; congr 1; ext c; simp

theorem hw_prefix {k b : ℕ} (hb : b ≤ k) : hw (fun c : Fin k => decide (c.val < b)) = b := by
  unfold hw
  rw [← Finset.card_map Fin.valEmbedding]
  convert Finset.card_range b using 2
  ext n; simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    decide_eq_true_eq, Fin.valEmbedding_apply, Finset.mem_range]
  constructor
  · rintro ⟨c, hc, rfl⟩; exact hc
  · intro hn; exact ⟨⟨n, by omega⟩, hn, rfl⟩

theorem maj_construction {k : ℕ} {S : Set ℕ} (R0 : Fin k → Bool) (hR0 : hw R0 ∈ S)
    (r q a b : ℕ) (ha : a ∈ S) (hab : a ≤ b) (hbk : b ≤ k) (hb : 0 < b)
    (hL : Odd (r + q * b)) :
    (fun c : Fin k => decide (r + q * b < 2 * ((if R0 c then r else 0) +
      (if c.val < b then q * a else 0)))) ∈ MajImage (Ham k S) := by
  have : NeZero b := ⟨hb.ne'⟩
  obtain ⟨G, -, hG⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin b)))
    (n := a) (by simpa using hab)
  let F : Fin b → Finset (Fin b) := fun j => G.map (Equiv.addRight j).toEmbedding
  let emb : Fin b ↪ Fin k := Fin.castLEEmb hbk
  let cyc : Fin b → Fin k → Bool := fun j c => decide (c ∈ (F j).map emb)
  have hcyc : ∀ j, hw (cyc j) = a := fun j => by
    simp only [cyc, hw_decide_mem, Finset.card_map, F, hG]
  let g : Fin r ⊕ (Fin q × Fin b) → Fin k → Bool := Sum.elim (fun _ => R0) (fun p => cyc p.2)
  let e : Fin (r + q * b) ≃ Fin r ⊕ (Fin q × Fin b) :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) finProdFinEquiv.symm)
  refine ⟨r + q * b, hL, fun i => g (e i), fun i => ?_, ?_⟩
  · show hw (g (e i)) ∈ S
    rcases e i with i' | p
    · exact hR0
    · show hw (cyc p.2) ∈ S
      rw [hcyc]; exact ha
  · funext c
    simp only [Maj]
    congr 2
    have hcnt : ∑ j : Fin b, (if cyc j c = true then 1 else 0) =
        if c.val < b then a else 0 := by
      split_ifs with hcb
      · let c' : Fin b := ⟨c.val, hcb⟩
        have hmem : ∀ j, (cyc j c = true) ↔ (c' - j ∈ G) := fun j => by
          have : c = emb c' := Fin.ext rfl
          simp only [cyc, decide_eq_true_eq, this, Finset.mem_map' emb, F,
            Finset.mem_map_equiv, Equiv.coe_addRight, Equiv.addRight_symm, sub_eq_add_neg]
        simp only [hmem]
        rw [Fintype.sum_equiv (Equiv.subLeft c') (fun j => if c' - j ∈ G then 1 else 0)
          (fun g' => if g' ∈ G then 1 else 0) (fun j => rfl)]
        rw [Finset.sum_boole]; simp [hG]
      · refine Finset.sum_eq_zero (fun j _ => ?_)
        have : cyc j c = false := by
          simp only [cyc, decide_eq_false_iff_not, Finset.mem_map]
          rintro ⟨x, -, hx⟩
          apply hcb; rw [← hx]; simp [emb]
        simp [this]
    unfold hw
    rw [Finset.card_filter]
    rw [Fintype.sum_equiv e (fun i => if g (e i) c = true then 1 else 0)
      (fun x => if g x c = true then 1 else 0) (fun i => rfl)]
    rw [Fintype.sum_sum_type]
    have h1 : ∀ x : Fin r, (if g (Sum.inl x) c = true then 1 else 0) =
        if R0 c = true then 1 else 0 := fun x => rfl
    have h2 : ∀ p : Fin q × Fin b, (if g (Sum.inr p) c = true then 1 else 0) =
        if cyc p.2 c = true then 1 else 0 := fun p => rfl
    rw [Finset.sum_congr rfl (fun x _ => h1 x), Finset.sum_congr rfl (fun p _ => h2 p),
      Fintype.sum_prod_type, Finset.sum_congr rfl (fun x _ => hcnt)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    split_ifs <;> simp

theorem majImage_hw_le {k : ℕ} {S : Set ℕ} {w : ℕ} (hw1 : 1 ≤ w) (hS : ∀ s ∈ S, s ≤ w)
    {y : Fin k → Bool} (hy : y ∈ MajImage (Ham k S)) : hw y ≤ 2 * w - 1 := by
  obtain ⟨L, hL, M, hM, rfl⟩ := hy
  have hdc : ∑ c : Fin k, hw (fun i => M i c) = ∑ i, hw (M i) := by
    unfold hw; simp only [Finset.card_filter]; exact Finset.sum_comm
  have hrow : ∑ i, hw (M i) ≤ L * w := by
    calc ∑ i, hw (M i) ≤ ∑ _i : Fin L, w := Finset.sum_le_sum (fun i _ => hS _ (hM i))
      _ = L * w := by simp
  have hlow : (L + 1) * hw (fun c => Maj L (fun l => M l c)) ≤ ∑ c : Fin k, 2 * hw (fun i => M i c) := by
    unfold hw
    rw [Finset.card_filter, Finset.mul_sum]
    refine Finset.sum_le_sum (fun c _ => ?_)
    split_ifs with h
    · simp only [Maj, decide_eq_true_eq] at h; unfold hw at h; omega
    · simp
  rw [← Finset.mul_sum, hdc] at hlow
  by_contra hcon
  push Not at hcon
  have : (L + 1) * (2 * w) ≤ 2 * (L * w) := by
    calc (L + 1) * (2 * w) ≤ (L + 1) * hw (fun c => Maj L (fun l => M l c)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ ≤ 2 * ∑ i, hw (M i) := hlow
      _ ≤ 2 * (L * w) := Nat.mul_le_mul_left _ hrow
  nlinarith

theorem exists_perm_of_hw_eq {k : ℕ} (x y : Fin k → Bool) (h : hw x = hw y) :
    ∃ σ : Equiv.Perm (Fin k), y = x ∘ σ := by
  have c1 : Fintype.card {c // y c = true} = Fintype.card {c // x c = true} := by
    rw [Fintype.card_subtype, Fintype.card_subtype]; exact h.symm
  have c2 : Fintype.card {c // ¬ y c = true} = Fintype.card {c // ¬ x c = true} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, c1]
  let e1 := Fintype.equivOfCardEq c1
  let e2 := Fintype.equivOfCardEq c2
  refine ⟨e1.subtypeCongr e2, ?_⟩
  funext c
  by_cases hc : y c = true
  · rw [Function.comp_apply, Equiv.subtypeCongr, Equiv.trans_apply, Equiv.trans_apply,
      Equiv.sumCompl_symm_apply_of_pos (p := fun c => y c = true) hc]; simp only [Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
    rw [hc, (e1 ⟨c, hc⟩).2]
  · rw [Function.comp_apply, Equiv.subtypeCongr, Equiv.trans_apply, Equiv.trans_apply,
      Equiv.sumCompl_symm_apply_of_neg (p := fun c => y c = true) hc]; simp only [Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]
    have := (e2 ⟨c, hc⟩).2
    simp only [Bool.not_eq_true] at hc this
    rw [hc, this]

theorem image_symm_of_ham {k L : ℕ} (f : (Fin L → Bool) → Bool) (S : Set ℕ)
    {x : Fin k → Bool} (hx : x ∈ image f (Ham k S)) (σ : Equiv.Perm (Fin k)) :
    x ∘ σ ∈ image f (Ham k S) := by
  obtain ⟨M, hM, rfl⟩ := hx
  refine ⟨fun l => M l ∘ σ, fun l => ?_, rfl⟩
  show hw _ ∈ S
  have : hw (M l ∘ σ) = hw (M l) := by
    unfold hw
    exact Finset.card_bij (fun c _ => σ c) (by simp) (fun a _ b _ h => σ.injective h)
      (fun c hc => ⟨σ.symm c, by simpa using hc, by simp⟩)
  rw [this]; exact hM l

theorem ham_subset_majImage {k : ℕ} {S : Set ℕ} {l w b : ℕ} (hl : l ∈ S) (hl1 : 1 ≤ l)
    (hwS : w ∈ S) (hwk : w ≤ k) (hlb : l ≤ b) (hbk : b ≤ k) (hbw : b ≤ 2 * w - 1) :
    Ham k {b} ⊆ MajImage (Ham k S) := by
  have hpre : (fun c : Fin k => decide (c.val < b)) ∈ MajImage (Ham k S) := by
    have hR0 : hw (fun c : Fin k => decide (c.val < w)) ∈ S := by rw [hw_prefix hwk]; exact hwS
    by_cases hwb : w ≤ b
    · have h := maj_construction (fun c : Fin k => decide (c.val < w)) hR0 1 2 w b hwS hwb hbk
        (by omega) ⟨b, by ring⟩
      convert h using 1
      funext c
      by_cases h1 : c.val < b <;> by_cases h2 : c.val < w <;> simp [h1, h2] <;> omega
    · push Not at hwb
      have h := maj_construction (fun c : Fin k => decide (c.val < w)) hR0 (2 * b - 1) 2 l b hl
        hlb hbk (by omega) ⟨2 * b - 1, by omega⟩
      convert h using 1
      funext c
      by_cases h1 : c.val < b <;> by_cases h2 : c.val < w <;> simp [h1, h2] <;> omega
  rintro y hy
  obtain ⟨σ, hσ⟩ := exists_perm_of_hw_eq _ y (by rw [hw_prefix hbk]; exact hy.symm)
  obtain ⟨L, hL, hx⟩ := hpre
  exact ⟨L, hL, hσ ▸ image_symm_of_ham _ S hx σ⟩

end Aux_majImage_ham_upper

open Aux_majImage_ham_upper in
/-- Upper half of `Maj(Ham_k(S))`: if `w = max S ≤ k` and `ℓ ∈ S` with `ℓ ≥ 1`, then every tuple in `Maj(Ham_k(S))` has weight at most `2w - 1`, and every weight `b` with `ℓ ≤ b ≤ min(k, 2w - 1)` occurs (`Ham_k({b}) ⊆ Maj(Ham_k(S))`). -/
theorem majImage_ham_upper {k : ℕ} {S : Set ℕ} {l w : ℕ} (hl : l ∈ S) (hl1 : 1 ≤ l)
    (hwS : w ∈ S) (hwk : w ≤ k) (hmax : ∀ s ∈ S, s ≤ w) :
    (∀ y ∈ MajImage (Ham k S), hw y ≤ 2 * w - 1) ∧
    (∀ b : ℕ, l ≤ b → b ≤ k → b ≤ 2 * w - 1 → Ham k {b} ⊆ MajImage (Ham k S)) := by
  have hw1 : 1 ≤ w := le_trans hl1 (hmax l hl)
  exact ⟨fun y hy => majImage_hw_le hw1 hmax hy,
    fun b hlb hbk hbw => ham_subset_majImage hl hl1 hwS hwk hlb hbk hbw⟩

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem cfixingFixture_1a50b454778a49f2935ed36458195d37 {k : ℕ} {S : Set ℕ} {l w : ℕ} (hl : l ∈ S) (hl1 : 1 ≤ l)
    (hwS : w ∈ S) (hwk : w ≤ k) (hmax : ∀ s ∈ S, s ≤ w) :
    (∀ y ∈ MajImage (Ham k S), hw y ≤ 2 * w - 1) ∧
    (∀ b : ℕ, l ≤ b → b ≤ k → b ≤ 2 * w - 1 → Ham k {b} ⊆ MajImage (Ham k S)) :=
  SymBoolPCSP.CFixing.majImage_ham_upper hl hl1 hwS hwk hmax

end cfixingModule_1a50b454778a49f2935ed36458195d37

section cfixingModule_3edd9b966cba4fbfb734431cc307ed77

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

namespace Aux_mem_ATImage_of_mem_diffClosure

theorem Z_append {k : ℕ} (P : Set (Fin k → Bool)) (L : ℕ) (hL : Odd L) (M : Fin L → Fin k → Bool)
    (hM : ∀ l, M l ∈ P) (u v : Fin k → Bool) (hu : u ∈ P) (hv : v ∈ P) :
    ∃ L', Odd L' ∧ ∃ M' : Fin L' → Fin k → Bool, (∀ l, M' l ∈ P) ∧
      (fun c => ∑ i : Fin L', (-1 : ℤ) ^ (i : ℕ) * (if M' i c then 1 else 0)) =
      fun c => (∑ i : Fin L, (-1 : ℤ) ^ (i : ℕ) * (if M i c then 1 else 0)) +
        ((if v c then 1 else 0) - (if u c then 1 else 0)) := by
  refine ⟨L + 2, by obtain ⟨t, rfl⟩ := hL; exact ⟨t + 1, by ring⟩,
    Fin.snoc (α := fun _ => Fin k → Bool) (Fin.snoc (α := fun _ => Fin k → Bool) M u) v, ?_, ?_⟩
  · intro l
    refine Fin.lastCases ?_ (fun j => ?_) l
    · simpa using hv
    · simp only [Fin.snoc_castSucc]
      refine Fin.lastCases ?_ (fun j' => ?_) j
      · simpa using hu
      · simpa using hM j'
  · funext c
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
    rw [hL.neg_one_pow, (hL.add_one).neg_one_pow]
    ring

end Aux_mem_ATImage_of_mem_diffClosure

open Aux_mem_ATImage_of_mem_diffClosure in
/-- The AT-image `AT(P) = ⋃_{L odd} AT_L(P)` contains the positivity pattern of every point `x + z`, where `x ∈ P` and `z` lies in the subgroup of `ℤ^k` generated by the differences `v - u` (`u, v ∈ P`). -/
theorem mem_ATImage_of_mem_diffClosure {k : ℕ} (P : Set (Fin k → Bool)) {x : Fin k → Bool}
    (hx : x ∈ P) {z : Fin k → ℤ}
    (hz : z ∈ AddSubgroup.closure {d : Fin k → ℤ | ∃ u ∈ P, ∃ v ∈ P,
        d = fun c => (if v c then 1 else 0) - (if u c then 1 else 0)}) :
    (fun c => decide (0 < (if x c then (1 : ℤ) else 0) + z c)) ∈ ATImage P := by
  set G := {d : Fin k → ℤ | ∃ u ∈ P, ∃ v ∈ P,
        d = fun c => (if v c then 1 else 0) - (if u c then 1 else 0)} with hG
  let Z : Set (Fin k → ℤ) := {s | ∃ L, Odd L ∧ ∃ M : Fin L → Fin k → Bool, (∀ l, M l ∈ P) ∧
      s = fun c => ∑ i : Fin L, (-1 : ℤ) ^ (i : ℕ) * (if M i c then 1 else 0)}
  have hstep : ∀ s ∈ Z, ∀ d ∈ G, s + d ∈ Z := by
    rintro s ⟨L, hL, M, hM, rfl⟩ d ⟨u, hu, v, hv, rfl⟩
    obtain ⟨L', hL', M', hM', he⟩ := Z_append P L hL M hM u v hu hv
    exact ⟨L', hL', M', hM', by rw [he]; rfl⟩
  let W : AddSubmonoid (Fin k → ℤ) :=
    { carrier := {z | ∀ s ∈ Z, s + z ∈ Z}
      zero_mem' := by intro s hs; simpa using hs
      add_mem' := by
        intro a b ha hb s hs
        rw [← add_assoc]; exact hb _ (ha _ hs) }
  have hzW : z ∈ W := by
    have hz' : z ∈ (AddSubgroup.closure G).toAddSubmonoid := hz
    rw [AddSubgroup.closure_toAddSubmonoid] at hz'
    refine AddSubmonoid.closure_le.mpr ?_ hz'
    rintro d (hd | hd) s hs
    · exact hstep s hs d hd
    · obtain ⟨u, hu, v, hv, he⟩ := hd
      refine hstep s hs d ⟨v, hv, u, hu, ?_⟩
      have : d = - -d := by simp
      rw [this, he]; funext c; simp
  have hx1 : (fun c => if x c then (1 : ℤ) else 0) ∈ Z :=
    ⟨1, odd_one, fun _ => x, fun _ => hx, by funext c; simp⟩
  obtain ⟨L, hL, M, hM, he⟩ := hzW _ hx1
  refine ⟨L, hL, M, hM, ?_⟩
  funext c
  have := congrFun he c
  simp only [Pi.add_apply] at this
  simp only [AT, this]

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem cfixingFixture_3edd9b966cba4fbfb734431cc307ed77 {k : ℕ} (P : Set (Fin k → Bool)) {x : Fin k → Bool}
    (hx : x ∈ P) {z : Fin k → ℤ}
    (hz : z ∈ AddSubgroup.closure {d : Fin k → ℤ | ∃ u ∈ P, ∃ v ∈ P,
        d = fun c => (if v c then 1 else 0) - (if u c then 1 else 0)}) :
    (fun c => decide (0 < (if x c then (1 : ℤ) else 0) + z c)) ∈ ATImage P :=
  SymBoolPCSP.CFixing.mem_ATImage_of_mem_diffClosure P hx hz

end cfixingModule_3edd9b966cba4fbfb734431cc307ed77

section cfixingModule_5a6df09a2c9e46638ff77e1f58c5774f

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

namespace Aux_mem_ATImage_ham_of_sign_sum

theorem hw_decide_mem {k : ℕ} (T : Finset (Fin k)) : hw (fun c => decide (c ∈ T)) = T.card := by
  unfold hw; congr 1; ext c; simp

theorem sum_boole_hw {k : ℕ} (x : Fin k → Bool) :
    ∑ c, (if x c then (1 : ℤ) else 0) = (hw x : ℤ) := by
  unfold hw; rw [Finset.sum_boole]

theorem exists_hw_eq {k w : ℕ} (hw' : w ≤ k) : ∃ x : Fin k → Bool, hw x = w := by
  obtain ⟨T, -, hT⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin k)))
    (n := w) (by simpa using hw')
  exact ⟨_, by rw [hw_decide_mem, hT]⟩

theorem ham_diffClosure {k : ℕ} {S : Set ℕ} {l l' : ℕ} (hl : l ∈ S) (hl1 : 1 ≤ l)
    (hlk : l + 1 ≤ k) (hl' : l' ∈ S) (hl'k : l' ≤ k) (z : Fin k → ℤ)
    (hz : ((l' : ℤ) - l) ∣ ∑ c, z c) :
    z ∈ AddSubgroup.closure {d : Fin k → ℤ | ∃ u ∈ Ham k S, ∃ v ∈ Ham k S,
        d = fun c => (if v c then 1 else 0) - (if u c then 1 else 0)} := by
  set H := AddSubgroup.closure {d : Fin k → ℤ | ∃ u ∈ Ham k S, ∃ v ∈ Ham k S,
        d = fun c => (if v c then 1 else 0) - (if u c then 1 else 0)} with hH
  have gen : ∀ u ∈ Ham k S, ∀ v ∈ Ham k S,
      (fun c => (if v c then (1 : ℤ) else 0) - (if u c then 1 else 0)) ∈ H :=
    fun u hu v hv => AddSubgroup.subset_closure ⟨u, hu, v, hv, rfl⟩
  -- transfers
  have tr : ∀ a b : Fin k, a ≠ b → (Pi.single a (1 : ℤ) - Pi.single b 1) ∈ H := by
    intro a b hab
    have hc : l - 1 ≤ ((Finset.univ : Finset (Fin k)) \ {a, b}).card := by
      have : ((Finset.univ : Finset (Fin k)) \ {a, b}).card + ({a, b} : Finset (Fin k)).card = k := by
        rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
      rw [Finset.card_pair hab] at this
      omega
    obtain ⟨R, hRs, hR⟩ := Finset.exists_subset_card_eq hc
    have haR : a ∉ R := fun h => by simpa using hRs h
    have hbR : b ∉ R := fun h => by simpa using hRs h
    have hu : (fun c => decide (c ∈ insert b R)) ∈ Ham k S := by
      show hw _ ∈ S
      rw [hw_decide_mem, Finset.card_insert_of_notMem hbR, hR, Nat.sub_add_cancel hl1]; exact hl
    have hv : (fun c => decide (c ∈ insert a R)) ∈ Ham k S := by
      show hw _ ∈ S
      rw [hw_decide_mem, Finset.card_insert_of_notMem haR, hR, Nat.sub_add_cancel hl1]; exact hl
    convert gen _ hu _ hv using 1
    funext c
    by_cases hca : c = a
    · subst hca; simp [hab, haR]
    · by_cases hcb : c = b
      · subst hcb; simp [hbR, Ne.symm hab]
      · simp [hca, hcb]
  -- sum-zero vectors
  have k0 : 0 < k := by omega
  let c0 : Fin k := ⟨0, k0⟩
  have sz : ∀ w : Fin k → ℤ, ∑ c, w c = 0 → w ∈ H := by
    intro w hw0
    have hrep : w = ∑ c, w c • (Pi.single c (1 : ℤ) - Pi.single c0 1) := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_sub,
        Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
      by_cases hj : j = c0
      · subst hj; simp [hw0]
      · simp [hj]
    rw [hrep]
    refine AddSubgroup.sum_mem _ (fun c _ => AddSubgroup.zsmul_mem _ ?_ _)
    by_cases hc : c = c0
    · subst hc; simp
    · exact tr c c0 hc
  obtain ⟨x1, hx1⟩ := exists_hw_eq (k := k) (w := l) (by omega)
  obtain ⟨x2, hx2⟩ := exists_hw_eq (k := k) (w := l') hl'k
  have hd := gen x1 (by show hw x1 ∈ S; rw [hx1]; exact hl) x2
    (by show hw x2 ∈ S; rw [hx2]; exact hl')
  obtain ⟨j, hj⟩ := hz
  have hsum : ∑ c, ((fun c => (if x2 c then (1 : ℤ) else 0) - (if x1 c then 1 else 0)) c) =
      (l' : ℤ) - l := by
    simp only [Finset.sum_sub_distrib, sum_boole_hw, hx1, hx2]
  have : z - j • (fun c => (if x2 c then (1 : ℤ) else 0) - (if x1 c then 1 else 0)) ∈ H := by
    apply sz
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
      ← Finset.mul_sum, sum_boole_hw, hx1, hx2]
    rw [hj]; ring
  have h2 := H.add_mem this (H.zsmul_mem hd j)
  simpa using h2

theorem exists_int_sign_sum {k : ℕ} (y : Fin k → Bool) (T : ℤ)
    (h : ((∃ c, y c = true) ∧ (hw y : ℤ) ≤ T) ∨ ((∃ c, y c = false) ∧ T ≤ hw y)) :
    ∃ t : Fin k → ℤ, ∑ c, t c = T ∧ ∀ c, decide (0 < t c) = y c := by
  have key : ∀ c0 : Fin k, (y c0 = true → (hw y : ℤ) ≤ T) → (y c0 = false → T ≤ hw y) →
      ∃ t : Fin k → ℤ, ∑ c, t c = T ∧ ∀ c, decide (0 < t c) = y c := by
    intro c0 h1 h2
    refine ⟨fun c => (if y c then 1 else 0) + if c = c0 then T - hw y else 0, ?_, ?_⟩
    · rw [Finset.sum_add_distrib, sum_boole_hw]; simp
    · intro c
      by_cases hc : c = c0
      · subst hc; cases hy : y c <;> simp [hy] at h1 h2 ⊢ <;> omega
      · cases hy : y c <;> simp [hy, hc]
  rcases h with ⟨⟨c0, hc0⟩, hT⟩ | ⟨⟨c0, hc0⟩, hT⟩
  · exact key c0 (fun _ => hT) (fun h' => by rw [hc0] at h'; cases h')
  · exact key c0 (fun h' => by rw [hc0] at h'; cases h') (fun _ => hT)

end Aux_mem_ATImage_ham_of_sign_sum

open Aux_mem_ATImage_ham_of_sign_sum in
/-- `AT(Ham_k(S))` contains every `y ∈ {0,1}^k` that is the positivity pattern of an integer vector with total `T`, whenever `T ≡ ℓ (mod ℓ' - ℓ)` for some `ℓ, ℓ' ∈ S` with `1 ≤ ℓ ≤ k - 1`, `ℓ' ≤ k`; the condition on `(y, T)` is exactly that such an integer vector exists. -/
theorem mem_ATImage_ham_of_sign_sum {k : ℕ} {S : Set ℕ} {l l' : ℕ} (hl : l ∈ S) (hl1 : 1 ≤ l)
    (hlk : l + 1 ≤ k) (hl' : l' ∈ S) (hl'k : l' ≤ k) (y : Fin k → Bool) (T : ℤ)
    (hT : ((l' : ℤ) - l) ∣ T - l)
    (h : ((∃ c, y c = true) ∧ (hw y : ℤ) ≤ T) ∨ ((∃ c, y c = false) ∧ T ≤ hw y)) :
    y ∈ ATImage (Ham k S) := by
  obtain ⟨x, hx⟩ := exists_hw_eq (k := k) (w := l) (by omega)
  obtain ⟨t, ht, hty⟩ := exists_int_sign_sum y T h
  have hz := ham_diffClosure hl hl1 hlk hl' hl'k (t - fun c => if x c then 1 else 0)
    (by simp only [Pi.sub_apply, Finset.sum_sub_distrib, sum_boole_hw, hx, ht]; exact hT)
  have hm := mem_ATImage_of_mem_diffClosure (Ham k S) (x := x)
    (show hw x ∈ S by rw [hx]; exact hl) hz
  convert hm using 1
  funext c
  rw [← hty c]; simp

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem cfixingFixture_5a6df09a2c9e46638ff77e1f58c5774f {k : ℕ} {S : Set ℕ} {l l' : ℕ} (hl : l ∈ S) (hl1 : 1 ≤ l)
    (hlk : l + 1 ≤ k) (hl' : l' ∈ S) (hl'k : l' ≤ k) (y : Fin k → Bool) (T : ℤ)
    (hT : ((l' : ℤ) - l) ∣ T - l)
    (h : ((∃ c, y c = true) ∧ (hw y : ℤ) ≤ T) ∨ ((∃ c, y c = false) ∧ T ≤ hw y)) :
    y ∈ ATImage (Ham k S) :=
  SymBoolPCSP.CFixing.mem_ATImage_ham_of_sign_sum hl hl1 hlk hl' hl'k y T hT h

end cfixingModule_5a6df09a2c9e46638ff77e1f58c5774f

section cfixingModule_eb416fad871a48f1a25572aed3a51bb5

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

namespace Aux_claim_4_6

theorem const_of_mem_ham0k {k : ℕ} {x : Fin k → Bool} (hx : x ∈ Ham k {0, k}) :
    (∀ c, x c = false) ∨ (∀ c, x c = true) := by
  simp only [Ham, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, hw] at hx
  rcases hx with h | h
  · left; intro c
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
    simpa using h (Finset.mem_univ c)
  · right; intro c
    have : Finset.univ.filter (fun i => x i = true) = Finset.univ :=
      Finset.eq_univ_of_card _ (by simpa using h)
    have hc := Finset.mem_univ c
    rw [← this, Finset.mem_filter] at hc
    exact hc.2

theorem subset_image_of_proj {k L : ℕ} (f : (Fin L → Bool) → Bool) (j : Fin L)
    (hf : ∀ v, f v = v j) (P : Set (Fin k → Bool)) : P ⊆ image f P := by
  intro x hx
  exact ⟨fun _ => x, fun _ => hx, by funext c; simp [hf]⟩

theorem sum_neg_one_pow_odd {L : ℕ} (hL : Odd L) : ∑ i : Fin L, (-1 : ℤ) ^ (i : ℕ) = 1 := by
  obtain ⟨n, rfl⟩ := hL
  rw [Fin.sum_univ_eq_sum_range (fun i => (-1 : ℤ) ^ i)]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, pow_succ, pow_succ, show 2 * n + 1 = 2 * n + 1 from rfl,
      Odd.neg_one_pow (⟨n, rfl⟩ : Odd (2 * n + 1))]
    ring_nf; rw [Even.neg_one_pow ⟨n, by ring⟩]; norm_num

theorem AT_conservative {L : ℕ} (hL : Odd L) (v : Fin L → Bool) : ∃ l, AT L v = v l := by
  by_cases h : ∃ l, v l = AT L v
  · obtain ⟨l, hl⟩ := h; exact ⟨l, hl.symm⟩
  · push Not at h
    exfalso
    cases hA : AT L v
    · have : ∀ i, v i = true := fun i => by have := h i; rw [hA] at this; simpa using this
      simp only [AT, this, if_true, mul_one, sum_neg_one_pow_odd hL, decide_eq_false_iff_not] at hA
      exact hA one_pos
    · have : ∀ i, v i = false := fun i => by have := h i; rw [hA] at this; simpa using this
      simp [AT, this] at hA

theorem sum_boole_hw {k : ℕ} (x : Fin k → Bool) :
    ∑ c, (if x c then (1 : ℤ) else 0) = (hw x : ℤ) := by
  unfold hw; rw [Finset.sum_boole]

theorem hw_eq_zero_iff {k : ℕ} (y : Fin k → Bool) : hw y = 0 ↔ ∀ c, y c = false := by
  simp [hw, Finset.card_eq_zero, Finset.filter_eq_empty_iff]

theorem hw_eq_k_iff {k : ℕ} (y : Fin k → Bool) : hw y = k ↔ ∀ c, y c = true := by
  constructor
  · intro h c
    have : Finset.univ.filter (fun i => y i = true) = Finset.univ :=
      Finset.eq_univ_of_card _ (by simpa [hw] using h)
    have hc := Finset.mem_univ c
    rw [← this, Finset.mem_filter] at hc
    exact hc.2
  · intro h; simp [hw, h]

theorem hw_le {k : ℕ} (y : Fin k → Bool) : hw y ≤ k := by
  unfold hw; exact (Finset.card_filter_le _ _).trans (by simp)

theorem ATImage_sum {k : ℕ} {P : Set (Fin k → Bool)} {y : Fin k → Bool} (hy : y ∈ ATImage P) :
    ∃ s : Fin k → ℤ, (∀ c, y c = decide (0 < s c)) ∧ ∃ L, Odd L ∧
      ∃ M : Fin L → Fin k → Bool, (∀ l, M l ∈ P) ∧
      ∑ c, s c = ∑ i : Fin L, (-1 : ℤ) ^ (i : ℕ) * hw (M i) := by
  obtain ⟨L, hL, M, hM, rfl⟩ := hy
  refine ⟨fun c => ∑ i : Fin L, (-1 : ℤ) ^ (i : ℕ) * (if M i c then 1 else 0),
    fun c => rfl, L, hL, M, hM, ?_⟩
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.mul_sum, sum_boole_hw]

end Aux_claim_4_6

open Aux_claim_4_6 in
theorem claim_4_6 (k : ℕ) (hk : 1 ≤ k) :
    ATImage (Ham k {0}) = Ham k {0} ∧
    ATImage (Ham k {k}) = Ham k {k} ∧
    ATImage (Ham k {0, k}) = Ham k {0, k} ∧
    (2 ≤ k → ∀ l : ℕ, 1 ≤ l → l ≤ k - 1 → ATImage (Ham k {l}) = Ham k (Set.Icc 1 (k - 1))) ∧
    (2 ≤ k → ∀ l₁ l₂ : ℕ, l₁ ≤ k → l₂ ≤ k → ({l₁, l₂} : Set ℕ) ≠ {0, k} → l₁ ≠ l₂ →
      ATImage (Ham k {l₁, l₂}) = Set.univ) := by
  have hAT1 : ∀ P : Set (Fin k → Bool), P ⊆ ATImage P := fun P x hx =>
    ⟨1, odd_one, subset_image_of_proj (AT 1) 0
      (fun v => by cases h : v 0 <;> simp [AT, h] <;> exact ⟨0, by simp [h]⟩) P hx⟩
  have hATsub : ∀ P : Set (Fin k → Bool), P ⊆ Ham k {0, k} → ATImage P ⊆ P := by
    rintro P hP y ⟨L, hL, hy⟩
    exact image_subset_of_conservative (AT L) (AT_conservative hL) P hP hy
  have h0k : ∀ T : Set ℕ, T ⊆ {0, k} → Ham k T ⊆ Ham k {0, k} := fun T hT x hx => hT hx
  refine ⟨Set.Subset.antisymm (hATsub _ (h0k _ (by simp))) (hAT1 _),
    Set.Subset.antisymm (hATsub _ (h0k _ (by simp))) (hAT1 _),
    Set.Subset.antisymm (hATsub _ subset_rfl) (hAT1 _), ?_, ?_⟩
  · intro hk2 l hl1 hlk
    ext y; constructor
    · intro hy
      obtain ⟨s, hs, L, hL, M, hM, hsum⟩ := ATImage_sum hy
      have hrow : ∀ i, hw (M i) = l := fun i => hM i
      simp only [hrow] at hsum
      rw [← Finset.sum_mul, sum_neg_one_pow_odd hL, one_mul] at hsum
      show hw y ∈ Set.Icc 1 (k - 1)
      have hyk := hw_le y
      constructor
      · by_contra h0
        have hall := (hw_eq_zero_iff y).mp (by omega)
        have : ∑ c, s c ≤ 0 := Finset.sum_nonpos (fun c _ => by
          have := hs c; rw [hall c] at this; simpa using this.symm)
        omega
      · by_contra h0
        have hall := (hw_eq_k_iff y).mp (by omega)
        have : ∑ c : Fin k, (1 : ℤ) ≤ ∑ c, s c := Finset.sum_le_sum (fun c _ => by
          have := hs c; rw [hall c] at this
          have h' : 0 < s c := by simpa using this.symm
          omega)
        simp at this
        omega
    · intro hy
      have hy' : 1 ≤ hw y ∧ hw y ≤ k - 1 := hy
      refine mem_ATImage_ham_of_sign_sum (S := {l}) (l' := l) (Set.mem_singleton l) hl1 (by omega)
        (Set.mem_singleton l) (by omega) y l
        (by simp) ?_
      by_cases hle : hw y ≤ l
      · left
        refine ⟨?_, by exact_mod_cast hle⟩
        by_contra hn; push Not at hn
        have := (hw_eq_zero_iff y).mpr (fun c => by simpa using hn c); omega
      · right
        refine ⟨?_, by push Not at hle; exact_mod_cast hle.le⟩
        by_contra hn; push Not at hn
        have := (hw_eq_k_iff y).mpr (fun c => by simpa using hn c); omega
  · intro hk2 l₁ l₂ h1 h2 hne hneq
    obtain ⟨l, l', hl, hl', hl1, hlk, hl'k, hd⟩ : ∃ l l', l ∈ ({l₁, l₂} : Set ℕ) ∧
        l' ∈ ({l₁, l₂} : Set ℕ) ∧ 1 ≤ l ∧ l + 1 ≤ k ∧ l' ≤ k ∧ l ≠ l' := by
      by_cases hA : 1 ≤ l₁ ∧ l₁ + 1 ≤ k
      · exact ⟨l₁, l₂, by simp, by simp, hA.1, hA.2, h2, hneq⟩
      · refine ⟨l₂, l₁, by simp, by simp, ?_, ?_, h1, Ne.symm hneq⟩ <;>
        · by_contra hB
          apply hne
          have : (l₁ = 0 ∧ l₂ = k) ∨ (l₁ = k ∧ l₂ = 0) := by omega
          rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rfl
          · exact Set.pair_comm _ _
    ext y
    simp only [Set.mem_univ, iff_true]
    set d : ℤ := (l' : ℤ) - l with hdd
    have hd0 : d ≠ 0 := by rw [hdd]; omega
    have hdd1 : 1 ≤ d * d := by
      rcases lt_or_gt_of_ne hd0 with h | h <;> nlinarith
    have hyk := hw_le y
    by_cases hy : ∃ c, y c = true
    · refine mem_ATImage_ham_of_sign_sum hl hl1 hlk hl' hl'k y (l + d * (d * k))
        ⟨d * k, by ring⟩ (Or.inl ⟨hy, ?_⟩)
      have : (k : ℤ) ≤ d * (d * k) := by nlinarith
      omega
    · push Not at hy
      have h0 : hw y = 0 := (hw_eq_zero_iff y).mpr (fun c => by simpa using hy c)
      refine mem_ATImage_ham_of_sign_sum hl hl1 hlk hl' hl'k y (l - d * (d * k))
        ⟨-(d * k), by ring⟩ (Or.inr ⟨⟨⟨0, by omega⟩, by simpa using hy _⟩, ?_⟩)
      have : (k : ℤ) ≤ d * (d * k) := by nlinarith
      rw [h0]; push_cast; omega

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem cfixingFixture_eb416fad871a48f1a25572aed3a51bb5 (k : ℕ) (hk : 1 ≤ k) :
    ATImage (Ham k {0}) = Ham k {0} ∧
    ATImage (Ham k {k}) = Ham k {k} ∧
    ATImage (Ham k {0, k}) = Ham k {0, k} ∧
    (2 ≤ k → ∀ l : ℕ, 1 ≤ l → l ≤ k - 1 → ATImage (Ham k {l}) = Ham k (Set.Icc 1 (k - 1))) ∧
    (2 ≤ k → ∀ l₁ l₂ : ℕ, l₁ ≤ k → l₂ ≤ k → ({l₁, l₂} : Set ℕ) ≠ {0, k} → l₁ ≠ l₂ →
      ATImage (Ham k {l₁, l₂}) = Set.univ) :=
  SymBoolPCSP.CFixing.claim_4_6 k hk

end cfixingModule_eb416fad871a48f1a25572aed3a51bb5

section cfixingModule_924e8e1a8e1d41089fe53875f22ce076

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

namespace Aux_par_minor_of_parity

theorem hw_eq_sum {k : ℕ} (x : Fin k → Bool) : hw x = ∑ i, if x i = true then 1 else 0 := by
  unfold hw; rw [Finset.card_filter]

theorem hw_neg_add {k : ℕ} (y : Fin k → Bool) : hw (neg y) + hw y = k := by
  rw [hw_eq_sum, hw_eq_sum, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun i _ => show (if neg y i = true then 1 else 0) +
    (if y i = true then 1 else 0) = 1 by unfold neg; split_ifs <;> simp_all)]
  simp

end Aux_par_minor_of_parity

open Aux_par_minor_of_parity in
/-- Parity as a minor: let `f : {0,1}^L → {0,1}` be folded with `f(0,…,0) = 0`, let `L₁` be odd, `T ⊆ [L]` and `C ∈ ℕ`. If `f(e_X) = |X| mod 2` for every `X ⊆ T` with `|X| ≥ C`, and `|T| ≥ L₁(C + 1)`, then `Par_{L₁}` is a minor of `f`: there is `π : [L] → [L₁]` with `f(y_{π(1)}, …, y_{π(L)}) = Par_{L₁}(y)` for all `y ∈ {0,1}^{L₁}`. -/
theorem par_minor_of_parity {L L₁ : ℕ} (f : (Fin L → Bool) → Bool) (hfold : IsFolded f)
    (h0 : f (fun _ => false) = false) (hL₁ : Odd L₁) (T : Finset (Fin L)) (C : ℕ)
    (hpar : ∀ X ⊆ T, C ≤ X.card → f (indicator X) = decide (X.card % 2 = 1))
    (hT : L₁ * (C + 1) ≤ T.card) :
    ∃ π : Fin L → Fin L₁, ∀ y : Fin L₁ → Bool, f (fun i => y (π i)) = Par L₁ y := by
  classical
  obtain ⟨m, hCm, hmC, hm⟩ : ∃ m, C ≤ m ∧ m ≤ C + 1 ∧ m % 2 = 1 := by
    by_cases hC : C % 2 = 1
    · exact ⟨C, le_rfl, by omega, hC⟩
    · exact ⟨C + 1, by omega, le_rfl, by omega⟩
  have hL1pos : 0 < L₁ := hL₁.pos
  obtain ⟨X', hX'T, hX'c⟩ := Finset.exists_subset_card_eq
    (show L₁ * m ≤ T.card from le_trans (Nat.mul_le_mul_left _ hmC) hT)
  obtain ⟨Y, hYX, hYc, hu⟩ := FinsetParts.exists_parts_card_eq X' (fun _ : Fin L₁ => m)
    (by rw [hX'c]; simp)
  let π : Fin L → Fin L₁ := fun i => if hi : i ∈ X' then (hu i hi).exists.choose else ⟨0, hL1pos⟩
  have hπ : ∀ i ∈ X', ∀ j, π i = j ↔ i ∈ Y j := by
    intro i hi j
    simp only [π, dif_pos hi]
    constructor
    · rintro rfl; exact (hu i hi).exists.choose_spec
    · intro h; exact (hu i hi).unique (hu i hi).exists.choose_spec h
  have key : ∀ y : Fin L₁ → Bool, y ⟨0, hL1pos⟩ = false →
      f (fun i => y (π i)) = Par L₁ y := by
    intro y hy0
    set Z := X'.filter (fun i => y (π i) = true) with hZdef
    have hZ : (fun i => y (π i)) = indicator Z := by
      funext i
      simp only [indicator, hZdef, mem_filter]
      by_cases hi : i ∈ X'
      · simp [hi]
      · simp [hi, π, hy0]
    have hZc : Z.card = m * hw y := by
      rw [Finset.card_eq_sum_card_fiberwise (f := π) (t := univ) (fun _ _ => mem_univ _)]
      rw [hw_eq_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have : Z.filter (fun i => π i = j) = if y j = true then Y j else ∅ := by
        ext i
        simp only [hZdef, mem_filter]
        split_ifs with hyj
        · constructor
          · rintro ⟨⟨hi, _⟩, hij⟩; exact (hπ i hi j).mp hij
          · intro hi
            have hiX := hYX j hi
            have hij := (hπ i hiX j).mpr hi
            exact ⟨⟨hiX, by rw [hij]; exact hyj⟩, hij⟩
        · simp only [Finset.notMem_empty, iff_false]
          rintro ⟨⟨_, hy⟩, hij⟩
          rw [hij] at hy; exact hyj hy
      rw [this]
      split_ifs <;> simp [hYc]
    rw [hZ]
    by_cases hyz : hw y = 0
    · have hZe : Z = ∅ := by rw [← Finset.card_eq_zero, hZc, hyz, mul_zero]
      have hind : indicator (∅ : Finset (Fin L)) = fun _ => false := by
        funext i; simp [indicator]
      rw [hZe, hind, h0]
      unfold Par; rw [hyz]; rfl
    · rw [hpar Z ((Finset.filter_subset _ _).trans hX'T)
        (by rw [hZc]; exact hCm.trans (Nat.le_mul_of_pos_right _ (by omega)))]
      unfold Par
      rw [hZc, Nat.mul_mod, hm, one_mul, Nat.mod_mod]
  refine ⟨π, fun y => ?_⟩
  cases hy : y ⟨0, hL1pos⟩
  · exact key y hy
  · rw [hfold]
    have hn : neg (fun i => y (π i)) = fun i => (neg y) (π i) := rfl
    rw [hn, key (neg y) (by simp [neg, hy])]
    unfold Par
    have h1 := hw_neg_add y
    obtain ⟨t, ht⟩ := hL₁
    have h2 : hw (neg y) % 2 = 1 ↔ ¬ hw y % 2 = 1 := by omega
    simp only [h2, decide_not, Bool.not_not]

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem cfixingFixture_924e8e1a8e1d41089fe53875f22ce076 {L L₁ : ℕ} (f : (Fin L → Bool) → Bool) (hfold : IsFolded f)
    (h0 : f (fun _ => false) = false) (hL₁ : Odd L₁) (T : Finset (Fin L)) (C : ℕ)
    (hpar : ∀ X ⊆ T, C ≤ X.card → f (indicator X) = decide (X.card % 2 = 1))
    (hT : L₁ * (C + 1) ≤ T.card) :
    ∃ π : Fin L → Fin L₁, ∀ y : Fin L₁ → Bool, f (fun i => y (π i)) = Par L₁ y :=
  SymBoolPCSP.CFixing.par_minor_of_parity f hfold h0 hL₁ T C hpar hT

end cfixingModule_924e8e1a8e1d41089fe53875f22ce076

section cfixingModule_9703338e39f14b88a725ff76caf450a4

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

namespace Aux_polOf_ham_flip

theorem hw_le' {k : ℕ} (y : Fin k → Bool) : hw y ≤ k := by
  unfold hw; exact (Finset.card_filter_le _ _).trans (by simp)

theorem flipRel_univ_ham {k : ℕ} (X : Set ℕ) :
    flipRel Finset.univ (Ham k X) = Ham k {l | l ≤ k ∧ k - l ∈ X} := by
  ext y
  have hn : (fun i => xor (y i) (indicator Finset.univ i)) = neg y := by
    funext i; simp [indicator, neg]
  have hneg : hw (neg y) = k - hw y := by
    have : hw y + hw (neg y) = k := by
      unfold hw neg
      rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
      rw [Finset.sum_congr rfl (fun i _ => show (if y i = true then 1 else 0) +
        (if (!y i) = true then 1 else 0) = 1 by cases y i <;> simp)]
      simp
    omega
  show (fun i => xor (y i) (indicator Finset.univ i)) ∈ Ham k X ↔ _
  rw [hn]
  show hw (neg y) ∈ X ↔ hw y ≤ k ∧ k - hw y ∈ X
  rw [hneg]; exact ⟨fun h => ⟨hw_le' y, h⟩, fun h => h.2⟩

end Aux_polOf_ham_flip

open Aux_polOf_ham_flip in
/-- Complementing all coordinates (Claim 4.3 with the full flip set): for folded `f`, `f ∈ Pol(Ham_k(S), Ham_k(T))` implies `f ∈ Pol(Ham_k(k - S), Ham_k(k - T))`. -/
theorem polOf_ham_flip {k L : ℕ} {S T : Set ℕ} (hST : S ⊆ T) (f : (Fin L → Bool) → Bool)
    (hfold : IsFolded f) (hf : PolOf (Ham k S) (Ham k T) f) :
    PolOf (Ham k {l | l ≤ k ∧ k - l ∈ S}) (Ham k {l | l ≤ k ∧ k - l ∈ T}) f := by
  have := (claim_4_3 (Ham k S) (Ham k T) (fun x hx => hST hx) Finset.univ f hfold).mp hf
  rwa [flipRel_univ_ham, flipRel_univ_ham] at this

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem cfixingFixture_9703338e39f14b88a725ff76caf450a4 {k L : ℕ} {S T : Set ℕ} (hST : S ⊆ T) (f : (Fin L → Bool) → Bool)
    (hfold : IsFolded f) (hf : PolOf (Ham k S) (Ham k T) f) :
    PolOf (Ham k {l | l ≤ k ∧ k - l ∈ S}) (Ham k {l | l ≤ k ∧ k - l ∈ T}) f :=
  SymBoolPCSP.CFixing.polOf_ham_flip hST f hfold hf

end cfixingModule_9703338e39f14b88a725ff76caf450a4

section cfixingModule_9ea6c5c6a02e415681b6f9176a25671c

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

namespace Aux_polOf_ham_pin

theorem hw_le' {k : ℕ} (y : Fin k → Bool) : hw y ≤ k := by
  unfold hw; exact (Finset.card_filter_le _ _).trans (by simp)

theorem ham_congr {k : ℕ} {X Y : Set ℕ} (h : ∀ l ≤ k, l ∈ X ↔ l ∈ Y) : Ham k X = Ham k Y := by
  ext x; exact h _ (hw_le' x)

theorem polOf_mono {k L : ℕ} {P Q P' Q' : Set (Fin k → Bool)} {f : (Fin L → Bool) → Bool}
    (hf : PolOf P Q f) (hP : P' ⊆ P) (hQ : Q ⊆ Q') : PolOf P' Q' f :=
  fun M hM => hQ (hf M (fun l => hP (hM l)))

theorem polOf_ham_drop {L : ℕ} (f : (Fin L → Bool) → Bool) (hidem : IsIdempotent f) :
    ∀ (i n : ℕ) (S T : Set ℕ), S ⊆ T → T ⊆ Set.Iic (n + i) →
      PolOf (Ham (n + i) S) (Ham (n + i) T) f →
      PolOf (Ham n {l | l ∈ S ∧ l ≤ n}) (Ham n {l | l ∈ T ∧ l ≤ n}) f := by
  intro i
  induction i with
  | zero =>
    intro n S T _ hT hf
    rw [ham_congr (X := {l | l ∈ S ∧ l ≤ n}) (Y := S) (fun l hl => by simp [hl]),
      ham_congr (X := {l | l ∈ T ∧ l ≤ n}) (Y := T) (fun l hl => by simp [hl])]
    exact hf
  | succ i ih =>
    intro n S T hST hT hf
    have h2 := claim_4_2 (k := n + i + 1) (by omega) S T hST hT f hidem hf
    have h3 := ih n (S \ {n + i + 1}) (T \ {n + i + 1}) (Set.sdiff_subset_sdiff_left hST)
      (fun l hl => by
        have h1 := hT hl.1; have h2 : l ≠ n + i + 1 := hl.2
        simp only [Set.mem_Iic] at h1 ⊢; omega) h2
    rw [ham_congr (X := {l | l ∈ S ∧ l ≤ n}) (Y := {l | l ∈ S \ {n + i + 1} ∧ l ≤ n})
      (fun l hl => by simp <;> omega),
      ham_congr (X := {l | l ∈ T ∧ l ≤ n}) (Y := {l | l ∈ T \ {n + i + 1} ∧ l ≤ n})
      (fun l hl => by simp <;> omega)]
    exact h3

theorem polOf_ham_shift {L : ℕ} (f : (Fin L → Bool) → Bool) (hidem : IsIdempotent f)
    (hfold : IsFolded f) :
    ∀ (j n : ℕ) (S T : Set ℕ), S ⊆ T → T ⊆ Set.Iic (n + j) →
      PolOf (Ham (n + j) S) (Ham (n + j) T) f →
      PolOf (Ham n {l | l + j ∈ S}) (Ham n {l | l + j ∈ T}) f := by
  intro j
  induction j with
  | zero => intro n S T _ _ hf; simpa using hf
  | succ j ih =>
    intro n S T hST hT hf
    have h2 := claim_4_4 (k := n + j + 1) (by omega) S T hST hT f hidem hfold hf
    have h3 := ih n {l | l + 1 ∈ S} {l | l + 1 ∈ T} (fun l hl => hST hl)
      (fun l hl => by have := hT hl; simp only [Set.mem_Iic] at this ⊢; omega) h2
    have e : ∀ X : Set ℕ, {l | l + j ∈ {l | l + 1 ∈ X}} = {l | l + (j + 1) ∈ X} := fun X => by
      ext l; simp only [Set.mem_setOf_eq]; rw [show l + j + 1 = l + (j + 1) by omega]
    rw [e, e] at h3; exact h3

end Aux_polOf_ham_pin

open Aux_polOf_ham_pin in
/-- Pinning coordinates of Hamming promise relations (Claims 4.2 and 4.4 iterated): for an idempotent folded `f`, if `f ∈ Pol(Ham_{n+j+i}(S), Ham_{n+j+i}(T))` with `S ⊆ T ⊆ {0,…,n+j+i}`, then `f ∈ Pol(Ham_n(S'), Ham_n(T'))` where `S' = {l ≤ n : l + j ∈ S}` and `T' = {l ≤ n : l + j ∈ T}` (fix `j` coordinates to `1` and `i` coordinates to `0`). -/
theorem polOf_ham_pin {n i j L : ℕ} {S T : Set ℕ} (hST : S ⊆ T) (hT : T ⊆ Set.Iic (n + j + i))
    (f : (Fin L → Bool) → Bool) (hidem : IsIdempotent f) (hfold : IsFolded f)
    (hf : PolOf (Ham (n + j + i) S) (Ham (n + j + i) T) f) :
    PolOf (Ham n {l | l + j ∈ S ∧ l ≤ n}) (Ham n {l | l + j ∈ T ∧ l ≤ n}) f := by
  have h1 := polOf_ham_drop f hidem i (n + j) S T hST hT hf
  have h2 := polOf_ham_shift f hidem hfold j n {l | l ∈ S ∧ l ≤ n + j} {l | l ∈ T ∧ l ≤ n + j}
    (fun l (hl : l ∈ S ∧ l ≤ n + j) => (⟨hST hl.1, hl.2⟩ : l ∈ T ∧ l ≤ n + j))
    (fun l (hl : l ∈ T ∧ l ≤ n + j) => (hl.2 : l ≤ n + j)) h1
  rw [ham_congr (X := {l | l + j ∈ S ∧ l ≤ n}) (Y := {l | l + j ∈ {l | l ∈ S ∧ l ≤ n + j}})
    (fun l hl => by simp <;> omega),
    ham_congr (X := {l | l + j ∈ T ∧ l ≤ n}) (Y := {l | l + j ∈ {l | l ∈ T ∧ l ≤ n + j}})
    (fun l hl => by simp <;> omega)]
  exact h2

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem cfixingFixture_9ea6c5c6a02e415681b6f9176a25671c {n i j L : ℕ} {S T : Set ℕ} (hST : S ⊆ T) (hT : T ⊆ Set.Iic (n + j + i))
    (f : (Fin L → Bool) → Bool) (hidem : IsIdempotent f) (hfold : IsFolded f)
    (hf : PolOf (Ham (n + j + i) S) (Ham (n + j + i) T) f) :
    PolOf (Ham n {l | l + j ∈ S ∧ l ≤ n}) (Ham n {l | l + j ∈ T ∧ l ≤ n}) f :=
  SymBoolPCSP.CFixing.polOf_ham_pin hST hT f hidem hfold hf

end cfixingModule_9ea6c5c6a02e415681b6f9176a25671c

section cfixingModule_69a9224cca4c438c9f2be0aac26f0ed4

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

namespace Aux_lemma_4_5_single

theorem hw_le' {k : ℕ} (y : Fin k → Bool) : hw y ≤ k := by
  unfold hw; exact (Finset.card_filter_le _ _).trans (by simp)

theorem polOf_mono {k L : ℕ} {P Q P' Q' : Set (Fin k → Bool)} {f : (Fin L → Bool) → Bool}
    (hf : PolOf P Q f) (hP : P' ⊆ P) (hQ : Q ⊆ Q') : PolOf P' Q' f :=
  fun M hM => hQ (hf M (fun l => hP (hM l)))

theorem ham_subset {k : ℕ} {X Y : Set ℕ} (h : ∀ l ≤ k, l ∈ X → l ∈ Y) : Ham k X ⊆ Ham k Y :=
  fun x hx => h _ (hw_le' x) hx

theorem sum_neg_one_pow_odd {L : ℕ} (hL : Odd L) : ∑ i : Fin L, (-1 : ℤ) ^ (i : ℕ) = 1 := by
  obtain ⟨n, rfl⟩ := hL
  rw [Fin.sum_univ_eq_sum_range (fun i => (-1 : ℤ) ^ i)]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, pow_succ, pow_succ, show 2 * n + 1 = 2 * n + 1 from rfl,
      Odd.neg_one_pow (⟨n, rfl⟩ : Odd (2 * n + 1))]
    ring_nf; rw [Even.neg_one_pow ⟨n, by ring⟩]; norm_num

theorem AT_conservative {L : ℕ} (hL : Odd L) (v : Fin L → Bool) : ∃ l, AT L v = v l := by
  by_cases h : ∃ l, v l = AT L v
  · obtain ⟨l, hl⟩ := h; exact ⟨l, hl.symm⟩
  · push Not at h
    exfalso
    cases hA : AT L v
    · have : ∀ i, v i = true := fun i => by have := h i; rw [hA] at this; simpa using this
      simp only [AT, this, if_true, mul_one, sum_neg_one_pow_odd hL, decide_eq_false_iff_not] at hA
      exact hA one_pos
    · have : ∀ i, v i = false := fun i => by have := h i; rw [hA] at this; simpa using this
      simp [AT, this] at hA

theorem red45_A {k ℓ b : ℕ} {S T : Set ℕ} (X : ∀ L : ℕ, ((Fin L → Bool) → Bool) → Prop)
    (hX : ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsIdempotent f → IsFolded f → X L f →
      PolOf (Ham k S) (Ham k T) f)
    (hℓ : ℓ ∈ S) (hℓ1 : 1 ≤ ℓ) (hℓb : ℓ < b) (hbk : b + 1 ≤ k) (hbT : b ∉ T) :
    ∃ k' : ℕ,
      (3 ≤ k' ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsIdempotent f → IsFolded f → X L f →
        PolOf (Ham k' {1}) (Ham k' (Set.Iic (k' - 2) ∪ {k'})) f) ∨
      (2 ≤ k' ∧ ∃ b : ℕ, 1 ≤ b ∧ b ≤ k' - 1 ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool),
        IsIdempotent f → IsFolded f → X L f →
        PolOf (Ham k' {0, b}) (Ham k' (Set.Iic (k' - 1))) f) := by
  obtain ⟨i, rfl⟩ : ∃ i, k = (b - ℓ + 2) + (ℓ - 1) + i := ⟨k - b - 1, by omega⟩
  refine ⟨b - ℓ + 2, Or.inl ⟨by omega, fun L f hi hfo hx => ?_⟩⟩
  have h := polOf_mono (hX L f hi hfo hx) (P' := Ham _ {ℓ})
    (Q' := Ham _ (Set.Iic ((b - ℓ + 2) + (ℓ - 1) + i) \ {b}))
    (ham_subset fun l _ h => by rw [Set.mem_singleton_iff.mp h]; exact hℓ)
    (ham_subset fun l hl h => Set.mem_diff_of_mem (Set.mem_Iic.mpr hl)
      (fun e => hbT (by rw [Set.mem_singleton_iff] at e; subst e; exact h)))
  have h2 := polOf_ham_pin (n := b - ℓ + 2) (j := ℓ - 1) (i := i)
    (fun l h => by
      simp only [Set.mem_singleton_iff, Set.mem_diff, Set.mem_Iic] at h ⊢; omega)
    Set.diff_subset f hi hfo h
  exact polOf_mono h2 (ham_subset fun l hl h => by simp at h ⊢ <;> omega)
    (ham_subset fun l hl h => by simp at h ⊢ <;> omega)

theorem red45_B {k ℓ ℓ' : ℕ} {S T : Set ℕ} (X : ∀ L : ℕ, ((Fin L → Bool) → Bool) → Prop)
    (hX : ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsIdempotent f → IsFolded f → X L f →
      PolOf (Ham k S) (Ham k T) f)
    (hST : S ⊆ T) (hT : T ⊆ Set.Iic k)
    (hℓ : ℓ ∈ S) (hℓ' : ℓ' ∈ S) (hlt : ℓ < ℓ') (hkT : k ∉ T) :
    ∃ k' : ℕ,
      (3 ≤ k' ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsIdempotent f → IsFolded f → X L f →
        PolOf (Ham k' {1}) (Ham k' (Set.Iic (k' - 2) ∪ {k'})) f) ∨
      (2 ≤ k' ∧ ∃ b : ℕ, 1 ≤ b ∧ b ≤ k' - 1 ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool),
        IsIdempotent f → IsFolded f → X L f →
        PolOf (Ham k' {0, b}) (Ham k' (Set.Iic (k' - 1))) f) := by
  have hℓ'k : ℓ' + 1 ≤ k := by
    have h1 : ℓ' ≤ k := hT (hST hℓ')
    have h2 : ℓ' ≠ k := fun e => hkT (e ▸ hST hℓ')
    omega
  obtain ⟨n, rfl⟩ : ∃ n, k = n + ℓ + 0 := ⟨k - ℓ, by omega⟩
  refine ⟨n, Or.inr ⟨by omega, ℓ' - ℓ, by omega, by omega, fun L f hi hfo hx => ?_⟩⟩
  have h := polOf_mono (hX L f hi hfo hx) (P' := Ham _ {ℓ, ℓ'})
    (Q' := Ham _ (Set.Iic (n + ℓ + 0) \ {n + ℓ + 0}))
    (ham_subset fun l _ h => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with rfl | rfl <;> assumption)
    (ham_subset fun l hl h => Set.mem_diff_of_mem (Set.mem_Iic.mpr hl)
      (fun e => hkT (by rw [Set.mem_singleton_iff] at e; subst e; exact h)))
  have h2 := polOf_ham_pin (n := n) (j := ℓ) (i := 0)
    (fun l h => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_diff, Set.mem_Iic] at h ⊢
      omega)
    Set.diff_subset f hi hfo h
  exact polOf_mono h2 (ham_subset fun l hl h => by simp at h ⊢ <;> omega)
    (ham_subset fun l hl h => by simp at h ⊢ <;> omega)

theorem red45 {k ℓ b : ℕ} {S T : Set ℕ} (X : ∀ L : ℕ, ((Fin L → Bool) → Bool) → Prop)
    (hX : ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsIdempotent f → IsFolded f → X L f →
      PolOf (Ham k S) (Ham k T) f)
    (hST : S ⊆ T) (hT : T ⊆ Set.Iic k) (hbk : b ≤ k) (hbT : b ∉ T)
    (hℓ : ℓ ∈ S) (hℓ1 : 1 ≤ ℓ) (hℓk : ℓ + 1 ≤ k)
    (h2 : b = 0 ∨ b = k → ∃ ℓ' ∈ S, ℓ' ≠ ℓ) :
    ∃ k' : ℕ,
      (3 ≤ k' ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsIdempotent f → IsFolded f → X L f →
        PolOf (Ham k' {1}) (Ham k' (Set.Iic (k' - 2) ∪ {k'})) f) ∨
      (2 ≤ k' ∧ ∃ b : ℕ, 1 ≤ b ∧ b ≤ k' - 1 ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool),
        IsIdempotent f → IsFolded f → X L f →
        PolOf (Ham k' {0, b}) (Ham k' (Set.Iic (k' - 1))) f) := by
  have hXf : ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsIdempotent f → IsFolded f → X L f →
      PolOf (Ham k {l | l ≤ k ∧ k - l ∈ S}) (Ham k {l | l ≤ k ∧ k - l ∈ T}) f :=
    fun L f hi hfo hx => polOf_ham_flip hST f hfo (hX L f hi hfo hx)
  have hSTf : {l | l ≤ k ∧ k - l ∈ S} ⊆ {l | l ≤ k ∧ k - l ∈ T} := fun l h => ⟨h.1, hST h.2⟩
  have hTf : {l | l ≤ k ∧ k - l ∈ T} ⊆ Set.Iic k := fun l h => h.1
  have hmem : ∀ {s}, s ∈ S → k - s ∈ {l | l ≤ k ∧ k - l ∈ S} := fun {s} hs => by
    have : s ≤ k := hT (hST hs)
    exact ⟨Nat.sub_le _ _, by rw [Nat.sub_sub_self this]; exact hs⟩
  have hnT : ∀ {s}, s ≤ k → s ∉ T → k - s ∉ {l | l ≤ k ∧ k - l ∈ T} := fun {s} hs hsT h =>
    hsT (by have := h.2; rwa [Nat.sub_sub_self hs] at this)
  have hℓb : ℓ ≠ b := fun e => hbT (e ▸ hST hℓ)
  rcases Nat.eq_zero_or_pos b with hb0 | hb0
  · obtain ⟨ℓ', hℓ'S, hne⟩ := h2 (Or.inl hb0)
    have hℓ'k : ℓ' ≤ k := hT (hST hℓ'S)
    have hkT : k ∉ {l | l ≤ k ∧ k - l ∈ T} := by
      have := hnT (s := b) hbk hbT; rwa [hb0, Nat.sub_zero] at this
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact red45_B X hXf hSTf hTf (hmem hℓ) (hmem hℓ'S) (by omega) hkT
    · exact red45_B X hXf hSTf hTf (hmem hℓ'S) (hmem hℓ) (by omega) hkT
  rcases eq_or_ne b k with hbk' | hbk'
  · obtain ⟨ℓ', hℓ'S, hne⟩ := h2 (Or.inr hbk')
    have hkT : k ∉ T := hbk' ▸ hbT
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact red45_B X hX hST hT hℓ'S hℓ h hkT
    · exact red45_B X hX hST hT hℓ hℓ'S h hkT
  rcases Nat.lt_or_gt_of_ne hℓb with h | h
  · exact red45_A X hX hℓ hℓ1 h (by omega) hbT
  · exact red45_A X hXf (hmem hℓ) (by omega) (by omega) (by omega) (hnT hbk hbT)

end Aux_lemma_4_5_single

open Aux_lemma_4_5_single in
/-- Lemma 4.5 for a single symmetric promise relation: if `S ⊆ T ⊆ {0,…,k}` and some `y ∈ AT(Ham_k(S))` has weight outside `T`, then every idempotent folded polymorphism of `(Ham_k(S), Ham_k(T))` is a polymorphism of `(Ham_{k'}({1}), Ham_{k'}({0,…,k'-2,k'}))` for some `k' ≥ 3`, or of `(Ham_{k'}({0,b}), Ham_{k'}({0,…,k'-1}))` for some `k' ≥ 2`, `1 ≤ b ≤ k'-1`. -/
theorem lemma_4_5_single {k : ℕ} {S T : Set ℕ} (hST : S ⊆ T) (hT : T ⊆ Set.Iic k)
    {y : Fin k → Bool} (hy : y ∈ ATImage (Ham k S)) (hyT : hw y ∉ T) :
    ∃ k' : ℕ,
      (3 ≤ k' ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsIdempotent f → IsFolded f →
        PolOf (Ham k S) (Ham k T) f → PolOf (Ham k' {1}) (Ham k' (Set.Iic (k' - 2) ∪ {k'})) f) ∨
      (2 ≤ k' ∧ ∃ b : ℕ, 1 ≤ b ∧ b ≤ k' - 1 ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool),
        IsIdempotent f → IsFolded f → PolOf (Ham k S) (Ham k T) f →
        PolOf (Ham k' {0, b}) (Ham k' (Set.Iic (k' - 1))) f) := by
  have hyS : hw y ∉ S := fun h => hyT (hST h)
  obtain ⟨ℓ, hℓS, hℓ1, hℓk⟩ : ∃ ℓ ∈ S, 1 ≤ ℓ ∧ ℓ + 1 ≤ k := by
    by_contra hne
    push Not at hne
    have hsub : Ham k S ⊆ Ham k {0, k} := fun x hx => by
      have h1 := hne _ hx; have h2 := hw_le' x
      show hw x ∈ ({0, k} : Set ℕ)
      by_cases h0 : hw x = 0
      · exact Or.inl h0
      · exact Or.inr (by have := h1 (by omega); show hw x = k; omega)
    obtain ⟨L, hL, hyL⟩ := hy
    exact hyS (image_subset_of_conservative (AT L) (AT_conservative hL) _ hsub hyL)
  refine red45 (fun L f => PolOf (Ham k S) (Ham k T) f) (fun L f _ _ h => h) hST hT (hw_le' y)
    hyT hℓS hℓ1 hℓk ?_
  intro hb
  by_contra hne
  push Not at hne
  have hS : Ham k S = Ham k {ℓ} := by
    ext x; exact ⟨fun h => hne _ h, fun h => show hw x ∈ S from (Set.mem_singleton_iff.mp h) ▸ hℓS⟩
  rw [hS, (claim_4_6 k (by omega)).2.2.2.1 (by omega) ℓ hℓ1 (by omega)] at hy
  have : hw y ∈ Set.Icc 1 (k - 1) := hy
  simp only [Set.mem_Icc] at this; omega

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem cfixingFixture_69a9224cca4c438c9f2be0aac26f0ed4 {k : ℕ} {S T : Set ℕ} (hST : S ⊆ T) (hT : T ⊆ Set.Iic k)
    {y : Fin k → Bool} (hy : y ∈ ATImage (Ham k S)) (hyT : hw y ∉ T) :
    ∃ k' : ℕ,
      (3 ≤ k' ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsIdempotent f → IsFolded f →
        PolOf (Ham k S) (Ham k T) f → PolOf (Ham k' {1}) (Ham k' (Set.Iic (k' - 2) ∪ {k'})) f) ∨
      (2 ≤ k' ∧ ∃ b : ℕ, 1 ≤ b ∧ b ≤ k' - 1 ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool),
        IsIdempotent f → IsFolded f → PolOf (Ham k S) (Ham k T) f →
        PolOf (Ham k' {0, b}) (Ham k' (Set.Iic (k' - 1))) f) :=
  SymBoolPCSP.CFixing.lemma_4_5_single hST hT hy hyT

end cfixingModule_69a9224cca4c438c9f2be0aac26f0ed4

section cfixingModule_9e34808e03ff49049ff5c64eb1818f6d

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

namespace Aux_lemma_4_5

theorem hw_le' {k : ℕ} (y : Fin k → Bool) : hw y ≤ k := by
  unfold hw; exact (Finset.card_filter_le _ _).trans (by simp)

theorem exists_bad_rel {τ : Type} {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPF : IsPromiseFamily 𝔸 𝔹) (hsym : IsSymmetricFamily 𝔸 𝔹) {L : ℕ}
    (g : (Fin L → Bool) → Bool) (hg : ¬ IsPolymorphism 𝔸 𝔹 g) :
    ∃ (R : τ) (S T : Set ℕ), S ⊆ T ∧ T ⊆ Set.Iic (ar R) ∧ 𝔸.rel R = Ham (ar R) S ∧
      𝔹.rel R = Ham (ar R) T ∧ ∃ y ∈ image g (Ham (ar R) S), hw y ∉ T := by
  unfold IsPolymorphism at hg
  push Not at hg
  obtain ⟨R, M, hM, hout⟩ := hg
  have hA := isSymmetricRel_eq_ham (hsym R).1
  have hB := isSymmetricRel_eq_ham (hsym R).2
  refine ⟨R, _, _, ?_, ?_, hA, hB, fun c => g (fun l => M l c), ?_, ?_⟩
  · rintro s ⟨x, hx, rfl⟩; exact ⟨x, hPF R hx, rfl⟩
  · rintro s ⟨x, _, rfl⟩; exact hw_le' x
  · rw [← hA]; exact ⟨M, hM, rfl⟩
  · intro h; apply hout; rw [hB]; exact h

end Aux_lemma_4_5

open Aux_lemma_4_5 in
theorem lemma_4_5 {τ : Type} [Fintype τ] {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPF : IsPromiseFamily 𝔸 𝔹) (hsym : IsSymmetricFamily 𝔸 𝔹) (hfold : IsFoldedFamily 𝔸 𝔹)
    (hidem : IsIdempotentFamily 𝔸 𝔹) (L : ℕ) (hL : Odd L) (hAT : ¬ IsPolymorphism 𝔸 𝔹 (AT L)) :
    ∃ k : ℕ,
      (3 ≤ k ∧ IsRelaxation 𝔸 𝔹 (Ham k {1}) (Ham k (Set.Iic (k - 2) ∪ {k}))) ∨
      (2 ≤ k ∧ ∃ b : ℕ, 1 ≤ b ∧ b ≤ k - 1 ∧
        IsRelaxation 𝔸 𝔹 (Ham k {0, b}) (Ham k (Set.Iic (k - 1)))) := by
  obtain ⟨R, S, T, hST, hT, hA, hB, y, hy, hyT⟩ := exists_bad_rel 𝔸 𝔹 hPF hsym _ hAT
  have hpol : ∀ (L' : ℕ) (f : (Fin L' → Bool) → Bool), IsPolymorphism 𝔸 𝔹 f →
      PolOf (Ham (ar R) S) (Ham (ar R) T) f := fun L' f hp => by
    rw [← hA, ← hB]; exact hp R
  obtain ⟨k', ⟨hk, H⟩ | ⟨hk, b, hb1, hb2, H⟩⟩ := lemma_4_5_single hST hT ⟨L, hL, hy⟩ hyT
  · exact ⟨k', Or.inl ⟨hk, fun L' f hp =>
      H L' f (hidem L' f hp) (hfold L' f hp) (hpol L' f hp)⟩⟩
  · exact ⟨k', Or.inr ⟨hk, b, hb1, hb2, fun L' f hp =>
      H L' f (hidem L' f hp) (hfold L' f hp) (hpol L' f hp)⟩⟩

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem cfixingFixture_9e34808e03ff49049ff5c64eb1818f6d {τ : Type} [Fintype τ] {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPF : IsPromiseFamily 𝔸 𝔹) (hsym : IsSymmetricFamily 𝔸 𝔹) (hfold : IsFoldedFamily 𝔸 𝔹)
    (hidem : IsIdempotentFamily 𝔸 𝔹) (L : ℕ) (hL : Odd L) (hAT : ¬ IsPolymorphism 𝔸 𝔹 (AT L)) :
    ∃ k : ℕ,
      (3 ≤ k ∧ IsRelaxation 𝔸 𝔹 (Ham k {1}) (Ham k (Set.Iic (k - 2) ∪ {k}))) ∨
      (2 ≤ k ∧ ∃ b : ℕ, 1 ≤ b ∧ b ≤ k - 1 ∧
        IsRelaxation 𝔸 𝔹 (Ham k {0, b}) (Ham k (Set.Iic (k - 1)))) :=
  SymBoolPCSP.CFixing.lemma_4_5 𝔸 𝔹 hPF hsym hfold hidem L hL hAT

end cfixingModule_9e34808e03ff49049ff5c64eb1818f6d

section cfixingModule_cb726dae295f4a9880eba1c762a9997d

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

namespace Aux_lemma_4_7_single

theorem hw_le' {k : ℕ} (y : Fin k → Bool) : hw y ≤ k := by
  unfold hw; exact (Finset.card_filter_le _ _).trans (by simp)

theorem polOf_mono {k L : ℕ} {P Q P' Q' : Set (Fin k → Bool)} {f : (Fin L → Bool) → Bool}
    (hf : PolOf P Q f) (hP : P' ⊆ P) (hQ : Q ⊆ Q') : PolOf P' Q' f :=
  fun M hM => hQ (hf M (fun l => hP (hM l)))

theorem ham_subset {k : ℕ} {X Y : Set ℕ} (h : ∀ l ≤ k, l ∈ X → l ∈ Y) : Ham k X ⊆ Ham k Y :=
  fun x hx => h _ (hw_le' x) hx

theorem Maj_conservative {L : ℕ} (hL : Odd L) (v : Fin L → Bool) : ∃ l, Maj L v = v l := by
  by_cases h : ∃ l, v l = Maj L v
  · obtain ⟨l, hl⟩ := h; exact ⟨l, hl.symm⟩
  · push Not at h
    exfalso
    have hL1 : 1 ≤ L := by obtain ⟨t, rfl⟩ := hL; omega
    cases hA : Maj L v
    · have : ∀ i, v i = true := fun i => by have := h i; rw [hA] at this; simpa using this
      have hwL : hw v = L := by simp [hw, this]
      simp only [Maj, hwL, decide_eq_false_iff_not] at hA
      omega
    · have : ∀ i, v i = false := fun i => by have := h i; rw [hA] at this; simpa using this
      simp [Maj, hw, this] at hA

theorem hw_neg {k : ℕ} (x : Fin k → Bool) : hw (neg x) = k - hw x := by
  have : hw x + hw (neg x) = k := by
    unfold hw neg
    rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun i _ => show (if x i = true then 1 else 0) +
      (if (!x i) = true then 1 else 0) = 1 by cases x i <;> simp)]
    simp
  omega

theorem neg_neg' {k : ℕ} (x : Fin k → Bool) : neg (neg x) = x := by
  funext i; simp [neg]

theorem Maj_folded {L : ℕ} (hL : Odd L) : IsFolded (Maj L) := by
  intro x
  have h1 := hw_neg x
  have h2 : hw x ≤ L := by
    unfold hw; exact (Finset.card_filter_le _ _).trans (by simp)
  obtain ⟨t, rfl⟩ := hL
  simp only [Maj, h1]
  by_cases h : 2 * t + 1 < 2 * hw x
  · have : ¬ (2 * t + 1 < 2 * (2 * t + 1 - hw x)) := by omega
    simp [h, this]
  · have : 2 * t + 1 < 2 * (2 * t + 1 - hw x) := by omega
    simp [h, this]

theorem MajImage_negRel {k : ℕ} (P : Set (Fin k → Bool)) :
    MajImage (negRel P) = negRel (MajImage P) := by
  ext y; constructor
  · rintro ⟨L, hL, hy⟩
    rw [image_negRel_of_folded _ (Maj_folded hL)] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    exact ⟨y', ⟨L, hL, hy'⟩, rfl⟩
  · rintro ⟨y', ⟨L, hL, hy'⟩, rfl⟩
    refine ⟨L, hL, ?_⟩
    rw [image_negRel_of_folded _ (Maj_folded hL)]
    exact ⟨y', hy', rfl⟩

theorem negRel_ham {k : ℕ} (S : Set ℕ) (hS : ∀ s ∈ S, s ≤ k) :
    negRel (Ham k S) = Ham k ((fun s => k - s) '' S) := by
  ext x; constructor
  · rintro ⟨x', hx', rfl⟩
    exact ⟨hw x', hx', (hw_neg x').symm⟩
  · rintro ⟨s, hs, hsx⟩
    refine ⟨neg x, ?_, neg_neg' x⟩
    show hw (neg x) ∈ S
    rw [hw_neg]; have := hS s hs; simp only at hsx; rw [← hsx]
    rwa [Nat.sub_sub_self this]

theorem red47_1 {k M b : ℕ} {S T : Set ℕ} (X : ∀ L : ℕ, ((Fin L → Bool) → Bool) → Prop)
    (hX : ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsIdempotent f → IsFolded f → X L f →
      PolOf (Ham k S) (Ham k T) f)
    (hM : M ∈ S) (hMb : M < b) (hb2 : b + 1 ≤ 2 * M) (hbk : b ≤ k) (hbT : b ∉ T) :
    ∃ k' : ℕ,
      (3 ≤ k' ∧ Odd k' ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsIdempotent f → IsFolded f →
        X L f → PolOf (Ham k' {(k' + 1) / 2}) (Ham k' (Set.Iic (k' - 1))) f) ∨
      (3 ≤ k' ∧ ∃ b : ℕ, 2 ≤ b ∧ b ≤ k' - 1 ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool),
        IsIdempotent f → IsFolded f → X L f →
        PolOf (Ham k' {1, k'}) (Ham k' (Set.Iic k' \ {b})) f) := by
  obtain ⟨i, rfl⟩ : ∃ i, k = (2 * (b - M) + 1) + (2 * M - b - 1) + i := ⟨k - b, by omega⟩
  refine ⟨2 * (b - M) + 1, Or.inl ⟨by omega, ⟨b - M, rfl⟩, fun L f hi hfo hx => ?_⟩⟩
  have h := polOf_mono (hX L f hi hfo hx) (P' := Ham _ {M})
    (Q' := Ham _ (Set.Iic ((2 * (b - M) + 1) + (2 * M - b - 1) + i) \ {b}))
    (ham_subset fun l _ h => by rw [Set.mem_singleton_iff.mp h]; exact hM)
    (ham_subset fun l hl h => Set.mem_diff_of_mem (Set.mem_Iic.mpr hl)
      (fun e => hbT (by rw [Set.mem_singleton_iff] at e; subst e; exact h)))
  have h2 := polOf_ham_pin (n := 2 * (b - M) + 1) (j := 2 * M - b - 1) (i := i)
    (fun l h => by
      simp only [Set.mem_singleton_iff, Set.mem_diff, Set.mem_Iic] at h ⊢; omega)
    Set.diff_subset f hi hfo h
  exact polOf_mono h2 (ham_subset fun l hl h => by simp at h ⊢ <;> omega)
    (ham_subset fun l hl h => by simp at h ⊢ <;> omega)

theorem red47_2 {k ℓ₁ ℓ₂ b : ℕ} {S T : Set ℕ} (X : ∀ L : ℕ, ((Fin L → Bool) → Bool) → Prop)
    (hX : ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsIdempotent f → IsFolded f → X L f →
      PolOf (Ham k S) (Ham k T) f)
    (h₁ : ℓ₁ ∈ S) (h₂ : ℓ₂ ∈ S) (h1 : 1 ≤ ℓ₁) (h1b : ℓ₁ < b) (hb2 : b < ℓ₂) (h2k : ℓ₂ ≤ k)
    (hbT : b ∉ T) :
    ∃ k' : ℕ,
      (3 ≤ k' ∧ Odd k' ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsIdempotent f → IsFolded f →
        X L f → PolOf (Ham k' {(k' + 1) / 2}) (Ham k' (Set.Iic (k' - 1))) f) ∨
      (3 ≤ k' ∧ ∃ b : ℕ, 2 ≤ b ∧ b ≤ k' - 1 ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool),
        IsIdempotent f → IsFolded f → X L f →
        PolOf (Ham k' {1, k'}) (Ham k' (Set.Iic k' \ {b})) f) := by
  obtain ⟨i, rfl⟩ : ∃ i, k = (ℓ₂ - ℓ₁ + 1) + (ℓ₁ - 1) + i := ⟨k - ℓ₂, by omega⟩
  refine ⟨ℓ₂ - ℓ₁ + 1, Or.inr ⟨by omega, b - ℓ₁ + 1, by omega, by omega,
    fun L f hi hfo hx => ?_⟩⟩
  have h := polOf_mono (hX L f hi hfo hx) (P' := Ham _ {ℓ₁, ℓ₂})
    (Q' := Ham _ (Set.Iic ((ℓ₂ - ℓ₁ + 1) + (ℓ₁ - 1) + i) \ {b}))
    (ham_subset fun l _ h => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with rfl | rfl <;> assumption)
    (ham_subset fun l hl h => Set.mem_diff_of_mem (Set.mem_Iic.mpr hl)
      (fun e => hbT (by rw [Set.mem_singleton_iff] at e; subst e; exact h)))
  have h2 := polOf_ham_pin (n := ℓ₂ - ℓ₁ + 1) (j := ℓ₁ - 1) (i := i)
    (fun l h => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_diff, Set.mem_Iic] at h ⊢
      omega)
    Set.diff_subset f hi hfo h
  exact polOf_mono h2 (ham_subset fun l hl h => by simp at h ⊢ <;> omega)
    (ham_subset fun l hl h => by simp at h ⊢ <;> omega)

theorem red47 {k ℓ m M b : ℕ} {S T : Set ℕ} (X : ∀ L : ℕ, ((Fin L → Bool) → Bool) → Prop)
    (hX : ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsIdempotent f → IsFolded f → X L f →
      PolOf (Ham k S) (Ham k T) f)
    (hST : S ⊆ T) (hT : T ⊆ Set.Iic k) (hbk : b ≤ k) (hbT : b ∉ T)
    (hℓ : ℓ ∈ S) (hℓ1 : 1 ≤ ℓ) (hℓk : ℓ + 1 ≤ k)
    (hM : M ∈ S) (hMmax : ∀ s ∈ S, s ≤ M) (hbM : b + 1 ≤ 2 * M)
    (hm : m ∈ S) (hmmin : ∀ s ∈ S, m ≤ s) (hbm : (k - b) + 1 ≤ 2 * (k - m)) :
    ∃ k' : ℕ,
      (3 ≤ k' ∧ Odd k' ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsIdempotent f → IsFolded f →
        X L f → PolOf (Ham k' {(k' + 1) / 2}) (Ham k' (Set.Iic (k' - 1))) f) ∨
      (3 ≤ k' ∧ ∃ b : ℕ, 2 ≤ b ∧ b ≤ k' - 1 ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool),
        IsIdempotent f → IsFolded f → X L f →
        PolOf (Ham k' {1, k'}) (Ham k' (Set.Iic k' \ {b})) f) := by
  have hXf : ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsIdempotent f → IsFolded f → X L f →
      PolOf (Ham k {l | l ≤ k ∧ k - l ∈ S}) (Ham k {l | l ≤ k ∧ k - l ∈ T}) f :=
    fun L f hi hfo hx => polOf_ham_flip hST f hfo (hX L f hi hfo hx)
  have hmem : ∀ {s}, s ∈ S → k - s ∈ {l | l ≤ k ∧ k - l ∈ S} := fun {s} hs => by
    have : s ≤ k := hT (hST hs)
    exact ⟨Nat.sub_le _ _, by rw [Nat.sub_sub_self this]; exact hs⟩
  have hnT : k - b ∉ {l | l ≤ k ∧ k - l ∈ T} := fun h =>
    hbT (by have := h.2; rwa [Nat.sub_sub_self hbk] at this)
  have hMk : M ≤ k := hT (hST hM)
  have hbS : ∀ s ∈ S, s ≠ b := fun s hs e => hbT (e ▸ hST hs)
  have hmM := hmmin _ hM
  have hmℓ := hmmin _ hℓ
  have hℓM := hMmax _ hℓ
  have h1 := hbS _ hℓ; have h2 := hbS _ hM; have h3 := hbS _ hm
  rcases Nat.lt_or_ge M b with hb | hb
  · exact red47_1 X hX hM hb hbM hbk hbT
  rcases Nat.lt_or_ge b m with hb' | hb'
  · exact red47_1 X hXf (hmem hm) (by omega) (by omega) (Nat.sub_le _ _) hnT
  rcases Nat.lt_or_gt_of_ne h1 with h | h
  · exact red47_2 X hX hℓ hM hℓ1 h (by omega) hMk hbT
  · exact red47_2 X hXf (hmem hℓ) (hmem hm) (by omega) (by omega) (by omega) (Nat.sub_le _ _) hnT

end Aux_lemma_4_7_single

open Aux_lemma_4_7_single in
/-- Lemma 4.7 for a single symmetric promise relation: if `S ⊆ T ⊆ {0,…,k}` and some `y ∈ Maj(Ham_k(S))` has weight outside `T`, then every idempotent folded polymorphism of `(Ham_k(S), Ham_k(T))` is a polymorphism of `(Ham_{k'}({(k'+1)/2}), Ham_{k'}({0,…,k'-1}))` for some odd `k' ≥ 3`, or of `(Ham_{k'}({1,k'}), Ham_{k'}({0,…,k'} ∖ {b}))` for some `k' ≥ 3`, `2 ≤ b ≤ k'-1`. -/
theorem lemma_4_7_single {k : ℕ} {S T : Set ℕ} (hST : S ⊆ T) (hT : T ⊆ Set.Iic k)
    {y : Fin k → Bool} (hy : y ∈ MajImage (Ham k S)) (hyT : hw y ∉ T) :
    ∃ k' : ℕ,
      (3 ≤ k' ∧ Odd k' ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsIdempotent f → IsFolded f →
        PolOf (Ham k S) (Ham k T) f →
        PolOf (Ham k' {(k' + 1) / 2}) (Ham k' (Set.Iic (k' - 1))) f) ∨
      (3 ≤ k' ∧ ∃ b : ℕ, 2 ≤ b ∧ b ≤ k' - 1 ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool),
        IsIdempotent f → IsFolded f → PolOf (Ham k S) (Ham k T) f →
        PolOf (Ham k' {1, k'}) (Ham k' (Set.Iic k' \ {b})) f) := by
  have hyS : hw y ∉ S := fun h => hyT (hST h)
  have hSk : ∀ s ∈ S, s ≤ k := fun s hs => hT (hST hs)
  obtain ⟨ℓ, hℓS, hℓ1, hℓk⟩ : ∃ ℓ ∈ S, 1 ≤ ℓ ∧ ℓ + 1 ≤ k := by
    by_contra hne
    push Not at hne
    have hsub : Ham k S ⊆ Ham k {0, k} := fun x hx => by
      have h1 := hne _ hx; have h2 := hw_le' x
      show hw x ∈ ({0, k} : Set ℕ)
      by_cases h0 : hw x = 0
      · exact Or.inl h0
      · exact Or.inr (by have := h1 (by omega); show hw x = k; omega)
    obtain ⟨L, hL, hyL⟩ := hy
    exact hyS (image_subset_of_conservative (Maj L) (Maj_conservative hL) _ hsub hyL)
  have hfin : S.Finite := (Set.finite_Iic k).subset (hST.trans hT)
  obtain ⟨M, hMS, hMmax⟩ := Set.exists_max_image S id hfin ⟨ℓ, hℓS⟩
  obtain ⟨m, hmS, hmmin⟩ := Set.exists_min_image S id hfin ⟨ℓ, hℓS⟩
  have hMk := hSk M hMS
  have hmk := hSk m hmS
  have hmℓ := hmmin ℓ hℓS
  have hℓM := hMmax ℓ hℓS
  simp only [id] at hmℓ hℓM
  have hup := (majImage_ham_upper hℓS hℓ1 hMS hMk hMmax).1 y hy
  have hny : neg y ∈ MajImage (Ham k ((fun s => k - s) '' S)) := by
    rw [← negRel_ham S hSk, MajImage_negRel]; exact ⟨y, hy, rfl⟩
  have hlo := (majImage_ham_upper (S := (fun s => k - s) '' S) (l := k - ℓ) (w := k - m)
    ⟨ℓ, hℓS, rfl⟩ (by omega) ⟨m, hmS, rfl⟩ (Nat.sub_le _ _)
    (by rintro _ ⟨s, hs, rfl⟩; have := hmmin s hs; exact Nat.sub_le_sub_left this k)).1 _ hny
  rw [hw_neg] at hlo
  exact red47 (fun L f => PolOf (Ham k S) (Ham k T) f) (fun L f _ _ h => h) hST hT (hw_le' y) hyT
    hℓS hℓ1 hℓk hMS hMmax (by omega) hmS hmmin (by omega)

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem cfixingFixture_cb726dae295f4a9880eba1c762a9997d {k : ℕ} {S T : Set ℕ} (hST : S ⊆ T) (hT : T ⊆ Set.Iic k)
    {y : Fin k → Bool} (hy : y ∈ MajImage (Ham k S)) (hyT : hw y ∉ T) :
    ∃ k' : ℕ,
      (3 ≤ k' ∧ Odd k' ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsIdempotent f → IsFolded f →
        PolOf (Ham k S) (Ham k T) f →
        PolOf (Ham k' {(k' + 1) / 2}) (Ham k' (Set.Iic (k' - 1))) f) ∨
      (3 ≤ k' ∧ ∃ b : ℕ, 2 ≤ b ∧ b ≤ k' - 1 ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool),
        IsIdempotent f → IsFolded f → PolOf (Ham k S) (Ham k T) f →
        PolOf (Ham k' {1, k'}) (Ham k' (Set.Iic k' \ {b})) f) :=
  SymBoolPCSP.CFixing.lemma_4_7_single hST hT hy hyT

end cfixingModule_cb726dae295f4a9880eba1c762a9997d

section cfixingModule_e2b6b99a43e244eaab7482ae668c6b3e

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

namespace Aux_lemma_4_7

theorem hw_le' {k : ℕ} (y : Fin k → Bool) : hw y ≤ k := by
  unfold hw; exact (Finset.card_filter_le _ _).trans (by simp)

theorem exists_bad_rel {τ : Type} {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPF : IsPromiseFamily 𝔸 𝔹) (hsym : IsSymmetricFamily 𝔸 𝔹) {L : ℕ}
    (g : (Fin L → Bool) → Bool) (hg : ¬ IsPolymorphism 𝔸 𝔹 g) :
    ∃ (R : τ) (S T : Set ℕ), S ⊆ T ∧ T ⊆ Set.Iic (ar R) ∧ 𝔸.rel R = Ham (ar R) S ∧
      𝔹.rel R = Ham (ar R) T ∧ ∃ y ∈ image g (Ham (ar R) S), hw y ∉ T := by
  unfold IsPolymorphism at hg
  push Not at hg
  obtain ⟨R, M, hM, hout⟩ := hg
  have hA := isSymmetricRel_eq_ham (hsym R).1
  have hB := isSymmetricRel_eq_ham (hsym R).2
  refine ⟨R, _, _, ?_, ?_, hA, hB, fun c => g (fun l => M l c), ?_, ?_⟩
  · rintro s ⟨x, hx, rfl⟩; exact ⟨x, hPF R hx, rfl⟩
  · rintro s ⟨x, _, rfl⟩; exact hw_le' x
  · rw [← hA]; exact ⟨M, hM, rfl⟩
  · intro h; apply hout; rw [hB]; exact h

end Aux_lemma_4_7

open Aux_lemma_4_7 in
theorem lemma_4_7 {τ : Type} [Fintype τ] {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPF : IsPromiseFamily 𝔸 𝔹) (hsym : IsSymmetricFamily 𝔸 𝔹) (hfold : IsFoldedFamily 𝔸 𝔹)
    (hidem : IsIdempotentFamily 𝔸 𝔹) (L : ℕ) (hL : Odd L) (hMaj : ¬ IsPolymorphism 𝔸 𝔹 (Maj L)) :
    ∃ k : ℕ,
      (3 ≤ k ∧ Odd k ∧ IsRelaxation 𝔸 𝔹 (Ham k {(k + 1) / 2}) (Ham k (Set.Iic (k - 1)))) ∨
      (3 ≤ k ∧ ∃ b : ℕ, 2 ≤ b ∧ b ≤ k - 1 ∧
        IsRelaxation 𝔸 𝔹 (Ham k {1, k}) (Ham k (Set.Iic k \ {b}))) := by
  obtain ⟨R, S, T, hST, hT, hA, hB, y, hy, hyT⟩ := exists_bad_rel 𝔸 𝔹 hPF hsym _ hMaj
  have hpol : ∀ (L' : ℕ) (f : (Fin L' → Bool) → Bool), IsPolymorphism 𝔸 𝔹 f →
      PolOf (Ham (ar R) S) (Ham (ar R) T) f := fun L' f hp => by
    rw [← hA, ← hB]; exact hp R
  obtain ⟨k', ⟨hk, hodd, H⟩ | ⟨hk, b, hb1, hb2, H⟩⟩ := lemma_4_7_single hST hT ⟨L, hL, hy⟩ hyT
  · exact ⟨k', Or.inl ⟨hk, hodd, fun L' f hp =>
      H L' f (hidem L' f hp) (hfold L' f hp) (hpol L' f hp)⟩⟩
  · exact ⟨k', Or.inr ⟨hk, b, hb1, hb2, fun L' f hp =>
      H L' f (hidem L' f hp) (hfold L' f hp) (hpol L' f hp)⟩⟩

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem cfixingFixture_e2b6b99a43e244eaab7482ae668c6b3e {τ : Type} [Fintype τ] {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPF : IsPromiseFamily 𝔸 𝔹) (hsym : IsSymmetricFamily 𝔸 𝔹) (hfold : IsFoldedFamily 𝔸 𝔹)
    (hidem : IsIdempotentFamily 𝔸 𝔹) (L : ℕ) (hL : Odd L) (hMaj : ¬ IsPolymorphism 𝔸 𝔹 (Maj L)) :
    ∃ k : ℕ,
      (3 ≤ k ∧ Odd k ∧ IsRelaxation 𝔸 𝔹 (Ham k {(k + 1) / 2}) (Ham k (Set.Iic (k - 1)))) ∨
      (3 ≤ k ∧ ∃ b : ℕ, 2 ≤ b ∧ b ≤ k - 1 ∧
        IsRelaxation 𝔸 𝔹 (Ham k {1, k}) (Ham k (Set.Iic k \ {b}))) :=
  SymBoolPCSP.CFixing.lemma_4_7 𝔸 𝔹 hPF hsym hfold hidem L hL hMaj

end cfixingModule_e2b6b99a43e244eaab7482ae668c6b3e

section cfixingModule_781d28e66b004282afd9342cb0c3c686

open PCSPBLPAff.Symmetric

open SymBoolPCSP.CFixing in
theorem _root_.SymBoolPCSP.CFixing.proposition_2_10 {τ : Type} [Fintype τ] {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPF : IsPromiseFamily 𝔸 𝔹) {L : ℕ} (f : (Fin L → Bool) → Bool) :
    (IsPolymorphism 𝔸 𝔹 f ∧ IsIdempotent f) ↔
      IsPolymorphism (withConsts 𝔸) (withConsts 𝔹) f := by
  constructor
  · rintro ⟨hf, h0, h1⟩
    intro R M hM
    cases R with
    | inl R => exact hf R M hM
    | inr b =>
      show (fun c : Fin 1 => f (fun l => M l c)) = fun _ => b
      funext c
      have hc : (fun l => M l c) = fun _ => b := by
        funext l
        have h' : M l = fun _ => b := hM l
        rw [h']
      rw [hc]
      cases b
      · exact h0
      · exact h1
  · intro h
    refine ⟨fun R M hM => h (Sum.inl R) M hM, ?_, ?_⟩
    · have h' : (fun c : Fin 1 => f (fun l => (fun _ _ => false : Fin L → Fin 1 → Bool) l c)) = fun _ => false :=
        h (Sum.inr false) (fun _ _ => false) (fun l => rfl)
      exact congrFun h' (0 : Fin 1)
    · have h' : (fun c : Fin 1 => f (fun l => (fun _ _ => true : Fin L → Fin 1 → Bool) l c)) = fun _ => true :=
        h (Sum.inr true) (fun _ _ => true) (fun l => rfl)
      exact congrFun h' (0 : Fin 1)

end cfixingModule_781d28e66b004282afd9342cb0c3c686

section cfixingModule_3491dce6126f4a20a4a8f4ecb3a93803

open PCSPBLPAff.Symmetric

open SymBoolPCSP.CFixing in
theorem _root_.SymBoolPCSP.CFixing.proposition_2_12 {k L : ℕ} (P Q : Set (Fin k → Bool)) (hPQ : P ⊆ Q)
    (f : (Fin L → Bool) → Bool) (hf : PolOf P Q f) (hnd : IsNonDegenerate f)
    (hni : ¬ IsIdempotent f) :
    P ⊆ negRel Q ∧ IsIdempotent (fun x => !f x) ∧ PolOf P (negRel Q) (fun x => !f x) := by
  unfold IsNonDegenerate at hnd
  unfold IsIdempotent at hni
  have h01 : f (fun _ => false) = true ∧ f (fun _ => true) = false := by
    cases h0 : f (fun _ => false) <;> cases h1 : f (fun _ => true) <;> simp_all
  obtain ⟨h0, h1⟩ := h01
  have hb : ∀ b : Bool, f (fun _ => b) = !b := by
    intro b; cases b
    · exact h0
    · exact h1
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have := hf (fun _ => x) (fun _ => hx)
    refine ⟨_, this, ?_⟩
    funext c
    simp only [neg]
    rw [hb]
    simp
  · unfold IsIdempotent
    simp [h0, h1]
  · intro M hM
    exact ⟨_, hf M hM, rfl⟩

end cfixingModule_3491dce6126f4a20a4a8f4ecb3a93803

section cfixingModule_5972b99a326a429c84ee5deb75981a34

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

namespace Aux_subset_true_of_relax_maj

theorem hw_eq_sum {k : ℕ} (x : Fin k → Bool) :
    hw x = ∑ c, (if x c = true then 1 else 0) := by
  unfold hw; rw [Finset.card_filter]

theorem hw_equiv {α : Type} [Fintype α] {k : ℕ} (e : α ≃ Fin k) (x : Fin k → Bool) :
    hw x = ∑ a, (if x (e a) = true then 1 else 0) := by
  rw [hw_eq_sum]; exact (Equiv.sum_comp e (fun c => if x c = true then 1 else 0)).symm

theorem neg_of_folded {L : ℕ} {f : (Fin L → Bool) → Bool} (hfold : IsFolded f)
    (x : Fin L → Bool) : f (neg x) = !f x := by
  have hnn : neg (neg x) = x := funext fun i => by simp [neg]
  rw [hfold (neg x), hnn]

end Aux_subset_true_of_relax_maj

open Aux_subset_true_of_relax_maj in
/-- Case 1 of BG Lemma 4.12: let `f` be a folded polymorphism of
`(Ham_{2m+1}({m+1}), Ham_{2m+1}({0, …, 2m}))` and let `Z` be an `m`-set of coordinates on each
of which `f` is somewhere-increasing. Then `f(e_Z) = 1`. -/
theorem subset_true_of_relax_maj {L m : ℕ} (f : (Fin L → Bool) → Bool) (hfold : IsFolded f)
    (hpol : PolOf (Ham (2 * m + 1) {m + 1}) (Ham (2 * m + 1) (Set.Iic (2 * m))) f)
    (Z : Finset (Fin L)) (hZ : Z.card = m)
    (hwit : ∀ j ∈ Z, ∃ Y : Finset (Fin L), j ∉ Y ∧ f (indicator Y) = false ∧
      f (indicator (insert j Y)) = true) :
    f (indicator Z) = true := by
  classical
  choose Y hY using hwit
  have hcard : Fintype.card ((Z × Bool) ⊕ Unit) = 2 * m + 1 := by
    simp [Fintype.card_sum, Fintype.card_prod, hZ]; ring
  let e := Fintype.equivFinOfCardEq hcard
  let v : (Z × Bool) ⊕ Unit → Fin L → Bool := Sum.elim
    (fun p => if p.2 then indicator (insert p.1.1 (Y p.1.1 p.1.2))
      else neg (indicator (Y p.1.1 p.1.2)))
    (fun _ => neg (indicator Z))
  have key := hpol (fun l c => v (e.symm c) l) (by
    intro l
    simp only [Ham, Set.mem_setOf_eq, Set.mem_singleton_iff]
    rw [hw_equiv e]
    simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, Fintype.sum_prod_type,
      Fintype.sum_bool, Finset.univ_unique, Finset.sum_singleton]
    have hterm : ∀ z : Z, ((if v (Sum.inl (z, true)) l = true then 1 else 0) +
        (if v (Sum.inl (z, false)) l = true then 1 else 0) : ℕ) =
        1 + (if l = (z : Fin L) then 1 else 0) := by
      intro z
      have hz := (hY z.1 z.2).1
      by_cases hl : l = (z : Fin L)
      · subst hl; simp [v, indicator, neg, hz]
      · by_cases hlY : l ∈ Y z.1 z.2 <;> simp [v, indicator, neg, hl, hlY]
    rw [Finset.sum_congr rfl (fun z _ => hterm z), Finset.sum_add_distrib]
    rw [Finset.sum_coe_sort Z (fun z => if l = z then 1 else 0), Finset.sum_ite_eq]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, hZ, smul_eq_mul, mul_one]
    by_cases hlZ : l ∈ Z <;> simp [v, indicator, neg, hlZ])
  simp only [Ham, Set.mem_setOf_eq, Set.mem_Iic] at key
  rw [hw_equiv e] at key
  simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Fintype.sum_bool, Finset.univ_unique, Finset.sum_singleton] at key
  have h1 : ∀ z : Z, f (v (Sum.inl (z, true))) = true := fun z => by
    simp only [v, Sum.elim_inl, if_true]; exact (hY z.1 z.2).2.2
  have h2 : ∀ z : Z, f (v (Sum.inl (z, false))) = true := fun z => by
    simp only [v, Sum.elim_inl, Bool.false_eq_true, if_false]
    rw [neg_of_folded hfold, (hY z.1 z.2).2.1]; rfl
  simp only [h1, h2, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_coe, hZ,
    smul_eq_mul, mul_one] at key
  have h3 : f (v (Sum.inr ())) = !f (indicator Z) := by
    simp only [v, Sum.elim_inr]; exact neg_of_folded hfold _
  rw [h3] at key
  cases hfz : f (indicator Z)
  · simp [hfz] at key; omega
  · rfl

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem cfixingFixture_5972b99a326a429c84ee5deb75981a34 {L m : ℕ} (f : (Fin L → Bool) → Bool) (hfold : IsFolded f)
    (hpol : PolOf (Ham (2 * m + 1) {m + 1}) (Ham (2 * m + 1) (Set.Iic (2 * m))) f)
    (Z : Finset (Fin L)) (hZ : Z.card = m)
    (hwit : ∀ j ∈ Z, ∃ Y : Finset (Fin L), j ∉ Y ∧ f (indicator Y) = false ∧
      f (indicator (insert j Y)) = true) :
    f (indicator Z) = true :=
  SymBoolPCSP.CFixing.subset_true_of_relax_maj f hfold hpol Z hZ hwit

end cfixingModule_5972b99a326a429c84ee5deb75981a34

section cfixingModule_72b9b63d0f154de48d461fea5bdd32ab

namespace SymBoolPCSP.CFixing

/-- The sum conditions (1)–(2) of Lemma 4.9 (bounded by `N`), with `n ≥ 2`, `0 ∈ S₀`,
`1 ∈ S₁`, make both `S₀` and `S₁` closed under adding `2n-2` and adding `3n-4`
(as long as the result is at most `N`). -/
theorem sum_conditions_add_closed (n N : ℕ) (hn : 2 ≤ n) (S₀ S₁ : Set ℕ)
    (h0 : 0 ∈ S₀) (h1 : 1 ∈ S₁)
    (hs0 : ∀ b : Fin n → ℕ, (∀ i, b i ∈ S₁) → ∑ i, b i ≤ N → ∑ i, b i ∈ S₀)
    (hs1 : ∀ a ∈ S₀, ∀ b : Fin (n - 1) → ℕ, (∀ i, b i ∈ S₁) →
      a + ∑ i, b i ≤ N → a + ∑ i, b i ∈ S₁) :
    (∀ x ∈ S₀, x + (2 * n - 2) ≤ N → x + (2 * n - 2) ∈ S₀) ∧
    (∀ x ∈ S₀, x + (3 * n - 4) ≤ N → x + (3 * n - 4) ∈ S₀) ∧
    (∀ x ∈ S₁, x + (2 * n - 2) ≤ N → x + (2 * n - 2) ∈ S₁) ∧
    (∀ x ∈ S₁, x + (3 * n - 4) ≤ N → x + (3 * n - 4) ∈ S₁) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hs1' : ∀ a ∈ S₀, ∀ b : Fin (m + 1) → ℕ, (∀ i, b i ∈ S₁) →
      a + ∑ i, b i ≤ N → a + ∑ i, b i ∈ S₁ := hs1
  -- (3): a ∈ S₀ ⇒ a + (m+1) ∈ S₁
  have st3 : ∀ a ∈ S₀, a + (m + 1) ≤ N → a + (m + 1) ∈ S₁ := by
    intro a ha hN
    have := hs1' a ha (fun _ => 1) (fun _ => h1) (by simpa using hN)
    simpa using this
  -- (4): b ∈ S₁ ⇒ b + (m+1) ∈ S₀
  have st4 : ∀ b ∈ S₁, b + (m + 1) ≤ N → b + (m + 1) ∈ S₀ := by
    intro b hb hN
    have hsum : ∑ i, (Fin.cons b (fun _ : Fin (m + 1) => (1 : ℕ)) : Fin (m + 2) → ℕ) i =
        b + (m + 1) := by simp [Fin.sum_cons]
    have := hs0 (Fin.cons b (fun _ => 1)) (fun i => Fin.cases hb (fun _ => h1) i)
      (by rw [hsum]; exact hN)
    rwa [hsum] at this
  -- (5): b ∈ S₁ ⇒ b + m ∈ S₁
  have st5 : ∀ b ∈ S₁, b + m ≤ N → b + m ∈ S₁ := by
    intro b hb hN
    have hsum : ∑ i, (Fin.cons b (fun _ : Fin m => (1 : ℕ)) : Fin (m + 1) → ℕ) i = b + m := by
      simp [Fin.sum_cons]
    have := hs1' 0 h0 (Fin.cons b (fun _ => 1)) (fun i => Fin.cases hb (fun _ => h1) i)
      (by rw [hsum]; omega)
    rwa [hsum, zero_add] at this
  have e2 : 2 * (m + 2) - 2 = (m + 1) + (m + 1) := by omega
  have e3 : 3 * (m + 2) - 4 = (m + 1) + m + (m + 1) := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx hN; rw [e2] at hN ⊢; rw [← add_assoc]
    exact st4 _ (st3 x hx (by omega)) (by omega)
  · intro x hx hN; rw [e3] at hN ⊢
    have : x + (m + 1 + m + (m + 1)) = x + (m + 1) + m + (m + 1) := by ring
    rw [this]
    exact st4 _ (st5 _ (st3 x hx (by omega)) (by omega)) (by omega)
  · intro x hx hN; rw [e2] at hN ⊢; rw [← add_assoc]
    exact st3 _ (st4 x hx (by omega)) (by omega)
  · intro x hx hN; rw [e3] at hN ⊢
    have : x + (m + 1 + m + (m + 1)) = x + m + (m + 1) + (m + 1) := by ring
    rw [this]
    exact st3 _ (st4 _ (st5 x hx (by omega)) (by omega)) (by omega)

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem cfixingFixture_72b9b63d0f154de48d461fea5bdd32ab (n N : ℕ) (hn : 2 ≤ n) (S₀ S₁ : Set ℕ)
    (h0 : 0 ∈ S₀) (h1 : 1 ∈ S₁)
    (hs0 : ∀ b : Fin n → ℕ, (∀ i, b i ∈ S₁) → ∑ i, b i ≤ N → ∑ i, b i ∈ S₀)
    (hs1 : ∀ a ∈ S₀, ∀ b : Fin (n - 1) → ℕ, (∀ i, b i ∈ S₁) →
      a + ∑ i, b i ≤ N → a + ∑ i, b i ∈ S₁) :
    (∀ x ∈ S₀, x + (2 * n - 2) ≤ N → x + (2 * n - 2) ∈ S₀) ∧
    (∀ x ∈ S₀, x + (3 * n - 4) ≤ N → x + (3 * n - 4) ∈ S₀) ∧
    (∀ x ∈ S₁, x + (2 * n - 2) ≤ N → x + (2 * n - 2) ∈ S₁) ∧
    (∀ x ∈ S₁, x + (3 * n - 4) ≤ N → x + (3 * n - 4) ∈ S₁) :=
  SymBoolPCSP.CFixing.sum_conditions_add_closed n N hn S₀ S₁ h0 h1 hs0 hs1

end cfixingModule_72b9b63d0f154de48d461fea5bdd32ab

section cfixingModule_9511efc42a954305bad20e2cb14cb4f7

namespace SymBoolPCSP.CFixing

/-- Bounded form of Lemma 4.9 of Brakensiek–Guruswami, with the explicit constant `c(n) = 0` for `n = 1` and
`c(n) = 1 + (2n-2)(3n-4)` for `n ≥ 2`. -/
theorem lemma_4_9_bounded_explicit (n N : ℕ) (hn : 0 < n) (S₀ S₁ : Set ℕ)
    (h0 : 0 ∈ S₀) (h1 : 1 ∈ S₁)
    (hs0 : ∀ b : Fin n → ℕ, (∀ i, b i ∈ S₁) → ∑ i, b i ≤ N → ∑ i, b i ∈ S₀)
    (hs1 : ∀ a ∈ S₀, ∀ b : Fin (n - 1) → ℕ, (∀ i, b i ∈ S₁) →
      a + ∑ i, b i ≤ N → a + ∑ i, b i ∈ S₁) :
    (Odd n → (if n = 1 then 0 else 1 + (2 * n - 2) * (3 * n - 4)) ≤ N →
      (if n = 1 then 0 else 1 + (2 * n - 2) * (3 * n - 4)) ∈ S₀ ∧
      (if n = 1 then 0 else 1 + (2 * n - 2) * (3 * n - 4)) ∈ S₁) ∧
    (Even n → ∀ M : ℕ, (if n = 1 then 0 else 1 + (2 * n - 2) * (3 * n - 4)) ≤ M → M ≤ N →
      (Even M → M ∈ S₀) ∧ (Odd M → M ∈ S₁)) := by
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · -- n = 1
    have hn1 : n = 1 := by omega
    subst hn1
    refine ⟨fun _ _ => ⟨by simpa using h0, ?_⟩, fun he => absurd he (by decide)⟩
    have := hs1 0 h0 (fun i => absurd i.2 (by simp)) (fun i => absurd i.2 (by simp))
      (by simp <;> omega)
    simpa using this
  · have hne : n ≠ 1 := by omega
    simp only [hne, if_false]
    obtain ⟨c0p, c0q, c1p, c1q⟩ := sum_conditions_add_closed n N hge S₀ S₁ h0 h1 hs0 hs1
    have hp : 0 < 2 * n - 2 := by omega
    -- gcd(2n-2, 3n-4) divides 2
    have hg2 : Nat.gcd (2 * n - 2) (3 * n - 4) ∣ 2 := by
      have h3 : Nat.gcd (2 * n - 2) (3 * n - 4) ∣ 3 * (2 * n - 2) :=
        Dvd.dvd.mul_left (Nat.gcd_dvd_left _ _) 3
      have h4 : Nat.gcd (2 * n - 2) (3 * n - 4) ∣ 2 * (3 * n - 4) :=
        Dvd.dvd.mul_left (Nat.gcd_dvd_right _ _) 2
      have := Nat.dvd_sub h3 h4
      have e : 3 * (2 * n - 2) - 2 * (3 * n - 4) = 2 := by omega
      rwa [e] at this
    refine ⟨fun hodd hN => ?_, fun heven M hM hMN => ?_⟩
    · have hg1 : Nat.gcd (2 * n - 2) (3 * n - 4) = 1 := by
        have hoddq : Odd (3 * n - 4) := by
          obtain ⟨k, hk⟩ := hodd; exact ⟨3 * k - 1, by omega⟩
        have hd := Nat.le_of_dvd (by norm_num) hg2
        have hgo : ¬ 2 ∣ Nat.gcd (2 * n - 2) (3 * n - 4) := fun h2 =>
          (Nat.not_even_iff_odd.mpr hoddq) (even_iff_two_dvd.mpr (h2.trans (Nat.gcd_dvd_right _ _)))
        have hpos := Nat.gcd_pos_of_pos_left (3 * n - 4) hp
        interval_cases h : Nat.gcd (2 * n - 2) (3 * n - 4)
        · rfl
        · exact absurd (dvd_refl 2) hgo
      constructor
      · exact AddClosure.mem_of_add_closed_pair hp h0 c0p c0q (by omega) hN (by rw [hg1]; exact one_dvd _)
      · exact AddClosure.mem_of_add_closed_pair hp h1 c1p c1q (by omega) hN (by rw [hg1]; exact one_dvd _)
    · have hg : Nat.gcd (2 * n - 2) (3 * n - 4) = 2 := by
        have h2g : 2 ∣ Nat.gcd (2 * n - 2) (3 * n - 4) := by
          obtain ⟨k, hk⟩ := heven
          exact Nat.dvd_gcd ⟨n - 1, by omega⟩ ⟨3 * k - 2, by omega⟩
        exact Nat.dvd_antisymm hg2 h2g
      constructor
      · intro hMe
        refine AddClosure.mem_of_add_closed_pair hp h0 c0p c0q (by omega) hMN ?_
        rw [hg, Nat.sub_zero]; exact even_iff_two_dvd.mp hMe
      · intro hMo
        refine AddClosure.mem_of_add_closed_pair hp h1 c1p c1q (by omega) hMN ?_
        rw [hg]; obtain ⟨k, hk⟩ := hMo; exact ⟨k, by omega⟩

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem cfixingFixture_9511efc42a954305bad20e2cb14cb4f7 (n N : ℕ) (hn : 0 < n) (S₀ S₁ : Set ℕ)
    (h0 : 0 ∈ S₀) (h1 : 1 ∈ S₁)
    (hs0 : ∀ b : Fin n → ℕ, (∀ i, b i ∈ S₁) → ∑ i, b i ≤ N → ∑ i, b i ∈ S₀)
    (hs1 : ∀ a ∈ S₀, ∀ b : Fin (n - 1) → ℕ, (∀ i, b i ∈ S₁) →
      a + ∑ i, b i ≤ N → a + ∑ i, b i ∈ S₁) :
    (Odd n → (if n = 1 then 0 else 1 + (2 * n - 2) * (3 * n - 4)) ≤ N →
      (if n = 1 then 0 else 1 + (2 * n - 2) * (3 * n - 4)) ∈ S₀ ∧
      (if n = 1 then 0 else 1 + (2 * n - 2) * (3 * n - 4)) ∈ S₁) ∧
    (Even n → ∀ M : ℕ, (if n = 1 then 0 else 1 + (2 * n - 2) * (3 * n - 4)) ≤ M → M ≤ N →
      (Even M → M ∈ S₀) ∧ (Odd M → M ∈ S₁)) :=
  SymBoolPCSP.CFixing.lemma_4_9_bounded_explicit n N hn S₀ S₁ h0 h1 hs0 hs1

end cfixingModule_9511efc42a954305bad20e2cb14cb4f7

section cfixingModule_0ece19eab40e4ac8b9b082ae848f3bc5

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

namespace Aux_sum_conditions_of_relax_one

theorem hw_eq_sum {k : ℕ} (x : Fin k → Bool) : hw x = ∑ i, if x i = true then 1 else 0 := by
  unfold hw; rw [Finset.card_filter]

theorem neg_indicator {L : ℕ} (X : Finset (Fin L)) : neg (indicator X) = indicator Xᶜ := by
  funext l; simp [neg, indicator]

theorem sum_mem_parts {L n : ℕ} {X : Finset (Fin L)} {Y : Fin n → Finset (Fin L)}
    (hYX : ∀ i, Y i ⊆ X) (hu : ∀ x ∈ X, ∃! i, x ∈ Y i) (l : Fin L) :
    (∑ i, if l ∈ Y i then 1 else 0 : ℕ) = if l ∈ X then 1 else 0 := by
  split_ifs with hl
  · obtain ⟨i, hi, hiu⟩ := hu l hl
    rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro j _ hj; simp only [ite_eq_right_iff]; intro h; exact absurd (hiu j h) hj
    · simp
  · apply Finset.sum_eq_zero; intro i _; simp only [ite_eq_right_iff]; intro h
    exact absurd (hYX i h) hl

theorem core {L m r K : ℕ} {P Q : Set ℕ} (f : (Fin L → Bool) → Bool)
    (hf : PolOf (Ham K P) (Ham K Q) f) (hK : m + r = K) (X : Finset (Fin L))
    (Y : Fin m → Finset (Fin L)) (hYX : ∀ i, Y i ⊆ X) (hu : ∀ x ∈ X, ∃! i, x ∈ Y i)
    (Z : Fin r → Finset (Fin L))
    (hrow : ∀ l, (if l ∈ X then 1 else 0) + (∑ j, if l ∈ Z j then 1 else 0) ∈ P) :
    (∑ i, if f (indicator (Y i)) = true then 1 else 0) +
      (∑ j, if f (indicator (Z j)) = true then 1 else 0) ∈ Q := by
  subst hK
  have h := hf (fun l => Fin.append (fun i => decide (l ∈ Y i)) (fun j => decide (l ∈ Z j)))
    (fun l => by
      show hw _ ∈ P
      rw [hw_eq_sum, Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, decide_eq_true_eq]
      rw [sum_mem_parts hYX hu]; exact hrow l)
  change hw _ ∈ Q at h
  rw [hw_eq_sum, Fin.sum_univ_add] at h
  simp only [Fin.append_left, Fin.append_right] at h; exact h

end Aux_sum_conditions_of_relax_one

open Aux_sum_conditions_of_relax_one in
/-- Sum conditions from the first relaxation of Lemma 4.5: let `k ≥ 2` and let `f` be a folded polymorphism of `(Ham_k({1}), Ham_k({0,…,k−2} ∪ {k}))`. Fix `T ⊆ [L]` and let `S_β` (`β ∈ {0,1}`) be the set of `s` such that `f(e_X) = β` for every `X ⊆ T` with `|X| = s`. Then any sum of `k − 1` elements of `S₁` lies in `S₀`, and `a + b₁ + ⋯ + b_{k−2} ∈ S₁` whenever `a ∈ S₀` and all `bᵢ ∈ S₁`. -/
theorem sum_conditions_of_relax_one {k L : ℕ} (hk : 2 ≤ k) (f : (Fin L → Bool) → Bool)
    (hfold : IsFolded f) (hf : PolOf (Ham k {1}) (Ham k (Set.Iic (k - 2) ∪ {k})) f)
    (T : Finset (Fin L)) (S₀ S₁ : Set ℕ)
    (hS₀ : ∀ s, s ∈ S₀ ↔ ∀ X ⊆ T, X.card = s → f (indicator X) = false)
    (hS₁ : ∀ s, s ∈ S₁ ↔ ∀ X ⊆ T, X.card = s → f (indicator X) = true) :
    (∀ b : Fin (k - 1) → ℕ, (∀ i, b i ∈ S₁) → ∑ i, b i ∈ S₀) ∧
    (∀ a ∈ S₀, ∀ b : Fin (k - 1 - 1) → ℕ, (∀ i, b i ∈ S₁) → a + ∑ i, b i ∈ S₁) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  rw [show m + 2 - 2 = m by omega] at hf
  generalize hA : m + 2 - 1 - 1 = A
  generalize hB : m + 2 - 1 = B
  obtain rfl : m = A := by omega
  obtain rfl : B = m + 1 := by omega
  refine ⟨fun b hb => ?_, fun a ha b hb => ?_⟩
  · rw [hS₀]; intro X hXT hXc
    obtain ⟨Y, hYX, hYc, hu⟩ := FinsetParts.exists_parts_card_eq X b hXc.symm
    have h := core f hf (m := m + 1) (r := 1) (by omega) X Y hYX hu (fun _ => Xᶜ)
      (fun l => by by_cases hl : l ∈ X <;> simp [hl])
    have hY1 : ∀ i, f (indicator (Y i)) = true := fun i =>
      (hS₁ (b i)).mp (hb i) (Y i) ((hYX i).trans hXT) (hYc i)
    simp only [hY1, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one, Finset.univ_unique] at h
    rw [hfold, neg_indicator]
    cases hc : f (indicator Xᶜ) <;> simp [hc] at h ⊢ <;> omega
  · rw [hS₁]; intro X hXT hXc
    obtain ⟨Y0, hY0X, hY0c⟩ := Finset.exists_subset_card_eq (show a ≤ X.card by omega)
    obtain ⟨Y, hYX, hYc, hu⟩ := FinsetParts.exists_parts_card_eq (X \ Y0) b
      (by rw [Finset.card_sdiff_of_subset hY0X]; omega)
    have h := core f hf (m := m) (r := 2) (by omega) (X \ Y0) Y hYX hu ![Y0, Xᶜ]
      (fun l => by
        rcases em (l ∈ Y0) with h0 | h0
        · rw [Fin.sum_univ_two]; simp [h0, hY0X h0]
        · rw [Fin.sum_univ_two]; by_cases hl : l ∈ X <;> simp [hl, h0])
    have hY0 : f (indicator Y0) = false := (hS₀ a).mp ha Y0 (hY0X.trans hXT) hY0c
    have hY1 : ∀ i, f (indicator (Y i)) = true := fun i =>
      (hS₁ (b i)).mp (hb i) (Y i) ((hYX i).trans (Finset.sdiff_subset.trans hXT)) (hYc i)
    simp only [hY1, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one] at h
    rw [Fin.sum_univ_two] at h; simp [hY0] at h
    rw [hfold, neg_indicator]
    cases hc : f (indicator Xᶜ) <;> simp [hc] at h ⊢ <;> omega

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem cfixingFixture_0ece19eab40e4ac8b9b082ae848f3bc5 {k L : ℕ} (hk : 2 ≤ k) (f : (Fin L → Bool) → Bool)
    (hfold : IsFolded f) (hf : PolOf (Ham k {1}) (Ham k (Set.Iic (k - 2) ∪ {k})) f)
    (T : Finset (Fin L)) (S₀ S₁ : Set ℕ)
    (hS₀ : ∀ s, s ∈ S₀ ↔ ∀ X ⊆ T, X.card = s → f (indicator X) = false)
    (hS₁ : ∀ s, s ∈ S₁ ↔ ∀ X ⊆ T, X.card = s → f (indicator X) = true) :
    (∀ b : Fin (k - 1) → ℕ, (∀ i, b i ∈ S₁) → ∑ i, b i ∈ S₀) ∧
    (∀ a ∈ S₀, ∀ b : Fin (k - 1 - 1) → ℕ, (∀ i, b i ∈ S₁) → a + ∑ i, b i ∈ S₁) :=
  SymBoolPCSP.CFixing.sum_conditions_of_relax_one hk f hfold hf T S₀ S₁ hS₀ hS₁

end cfixingModule_0ece19eab40e4ac8b9b082ae848f3bc5

section cfixingModule_15145d8592ba4b47b3362858591b7a17

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

namespace Aux_sum_conditions_of_relax_zero

theorem hw_eq_sum {k : ℕ} (x : Fin k → Bool) : hw x = ∑ i, if x i = true then 1 else 0 := by
  unfold hw; rw [Finset.card_filter]

theorem neg_indicator {L : ℕ} (X : Finset (Fin L)) : neg (indicator X) = indicator Xᶜ := by
  funext l; simp [neg, indicator]

theorem sum_mem_parts {L n : ℕ} {X : Finset (Fin L)} {Y : Fin n → Finset (Fin L)}
    (hYX : ∀ i, Y i ⊆ X) (hu : ∀ x ∈ X, ∃! i, x ∈ Y i) (l : Fin L) :
    (∑ i, if l ∈ Y i then 1 else 0 : ℕ) = if l ∈ X then 1 else 0 := by
  split_ifs with hl
  · obtain ⟨i, hi, hiu⟩ := hu l hl
    rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro j _ hj; simp only [ite_eq_right_iff]; intro h; exact absurd (hiu j h) hj
    · simp
  · apply Finset.sum_eq_zero; intro i _; simp only [ite_eq_right_iff]; intro h
    exact absurd (hYX i h) hl

theorem core {L m r K : ℕ} {P Q : Set ℕ} (f : (Fin L → Bool) → Bool)
    (hf : PolOf (Ham K P) (Ham K Q) f) (hK : m + r = K) (X : Finset (Fin L))
    (Y : Fin m → Finset (Fin L)) (hYX : ∀ i, Y i ⊆ X) (hu : ∀ x ∈ X, ∃! i, x ∈ Y i)
    (Z : Fin r → Finset (Fin L))
    (hrow : ∀ l, (if l ∈ X then 1 else 0) + (∑ j, if l ∈ Z j then 1 else 0) ∈ P) :
    (∑ i, if f (indicator (Y i)) = true then 1 else 0) +
      (∑ j, if f (indicator (Z j)) = true then 1 else 0) ∈ Q := by
  subst hK
  have h := hf (fun l => Fin.append (fun i => decide (l ∈ Y i)) (fun j => decide (l ∈ Z j)))
    (fun l => by
      show hw _ ∈ P
      rw [hw_eq_sum, Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, decide_eq_true_eq]
      rw [sum_mem_parts hYX hu]; exact hrow l)
  change hw _ ∈ Q at h
  rw [hw_eq_sum, Fin.sum_univ_add] at h
  simp only [Fin.append_left, Fin.append_right] at h; exact h

end Aux_sum_conditions_of_relax_zero

open Aux_sum_conditions_of_relax_zero in
/-- Sum conditions from the second relaxation of Lemma 4.5: let `1 ≤ b ≤ k − 1`, `n = k − b + 1`, and let `f` be a folded polymorphism of `(Ham_k({0, b}), Ham_k({0,…,k−1}))`. Fix `T ⊆ [L]` and let `S_β` (`β ∈ {0,1}`) be the set of `s` such that `f(e_X) = β` for every `X ⊆ T` with `|X| = s`. Then any sum of `n` elements of `S₁` lies in `S₀`, and `a + b₁ + ⋯ + b_{n−1} ∈ S₁` whenever `a ∈ S₀` and all `bᵢ ∈ S₁`. -/
theorem sum_conditions_of_relax_zero {k b L : ℕ} (hb1 : 1 ≤ b) (hbk : b ≤ k - 1)
    (f : (Fin L → Bool) → Bool) (hfold : IsFolded f)
    (hf : PolOf (Ham k {0, b}) (Ham k (Set.Iic (k - 1))) f)
    (T : Finset (Fin L)) (S₀ S₁ : Set ℕ)
    (hS₀ : ∀ s, s ∈ S₀ ↔ ∀ X ⊆ T, X.card = s → f (indicator X) = false)
    (hS₁ : ∀ s, s ∈ S₁ ↔ ∀ X ⊆ T, X.card = s → f (indicator X) = true) :
    (∀ β : Fin (k - b + 1) → ℕ, (∀ i, β i ∈ S₁) → ∑ i, β i ∈ S₀) ∧
    (∀ a ∈ S₀, ∀ β : Fin (k - b + 1 - 1) → ℕ, (∀ i, β i ∈ S₁) → a + ∑ i, β i ∈ S₁) := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 + c := ⟨k - 2 - c, by omega⟩
  rw [show m + 2 + c - 1 = m + 1 + c by omega] at hf
  generalize hA : m + 2 + c - (c + 1) + 1 - 1 = A
  generalize hB : m + 2 + c - (c + 1) + 1 = B
  obtain rfl : m + 1 = A := by omega
  obtain rfl : B = m + 2 := by omega
  refine ⟨fun β hβ => ?_, fun a ha β hβ => ?_⟩
  · rw [hS₀]; intro X hXT hXc
    obtain ⟨Y, hYX, hYc, hu⟩ := FinsetParts.exists_parts_card_eq X β hXc.symm
    have h := core f hf (m := m + 2) (r := c) rfl X Y hYX hu (fun _ => X)
      (fun l => by by_cases hl : l ∈ X <;> simp [hl] <;> omega)
    have hY1 : ∀ i, f (indicator (Y i)) = true := fun i =>
      (hS₁ (β i)).mp (hβ i) (Y i) ((hYX i).trans hXT) (hYc i)
    simp only [hY1, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one] at h
    cases hc : f (indicator X) <;> simp [hc] at h ⊢ <;> omega
  · rw [hS₁]; intro X hXT hXc
    obtain ⟨Y0, hY0X, hY0c⟩ := Finset.exists_subset_card_eq (show a ≤ X.card by omega)
    obtain ⟨Y, hYX, hYc, hu⟩ := FinsetParts.exists_parts_card_eq (X \ Y0) β
      (by rw [Finset.card_sdiff_of_subset hY0X]; omega)
    have h := core f hf (m := m + 1) (r := c + 1) (by omega) (X \ Y0) Y hYX hu
      (Fin.cons Xᶜ (fun _ => Y0ᶜ))
      (fun l => by
        rcases em (l ∈ Y0) with h0 | h0
        · rw [Fin.sum_univ_succ]; simp [h0, hY0X h0]
        · rw [Fin.sum_univ_succ]; by_cases hl : l ∈ X <;> simp [hl, h0] <;> omega)
    have hY0 : f (indicator Y0) = false := (hS₀ a).mp ha Y0 (hY0X.trans hXT) hY0c
    have hY0' : f (indicator Y0ᶜ) = true := by
      have := hfold (indicator Y0); rw [neg_indicator, hY0] at this; simpa using this
    have hY1 : ∀ i, f (indicator (Y i)) = true := fun i =>
      (hS₁ (β i)).mp (hβ i) (Y i) ((hYX i).trans (Finset.sdiff_subset.trans hXT)) (hYc i)
    simp only [hY1, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one] at h
    rw [Fin.sum_univ_succ] at h; simp [hY0'] at h
    rw [hfold, neg_indicator]
    cases hc : f (indicator Xᶜ) <;> simp [hc] at h ⊢ <;> omega

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem cfixingFixture_15145d8592ba4b47b3362858591b7a17 {k b L : ℕ} (hb1 : 1 ≤ b) (hbk : b ≤ k - 1)
    (f : (Fin L → Bool) → Bool) (hfold : IsFolded f)
    (hf : PolOf (Ham k {0, b}) (Ham k (Set.Iic (k - 1))) f)
    (T : Finset (Fin L)) (S₀ S₁ : Set ℕ)
    (hS₀ : ∀ s, s ∈ S₀ ↔ ∀ X ⊆ T, X.card = s → f (indicator X) = false)
    (hS₁ : ∀ s, s ∈ S₁ ↔ ∀ X ⊆ T, X.card = s → f (indicator X) = true) :
    (∀ β : Fin (k - b + 1) → ℕ, (∀ i, β i ∈ S₁) → ∑ i, β i ∈ S₀) ∧
    (∀ a ∈ S₀, ∀ β : Fin (k - b + 1 - 1) → ℕ, (∀ i, β i ∈ S₁) → a + ∑ i, β i ∈ S₁) :=
  SymBoolPCSP.CFixing.sum_conditions_of_relax_zero hb1 hbk f hfold hf T S₀ S₁ hS₀ hS₁

end cfixingModule_15145d8592ba4b47b3362858591b7a17

section cfixingModule_affd63a41c564e20bb8fe76c4992de22

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

theorem lemma_4_10 {τ : Type} [Fintype τ] {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPF : IsPromiseFamily 𝔸 𝔹) (hsym : IsSymmetricFamily 𝔸 𝔹) (hfold : IsFoldedFamily 𝔸 𝔹)
    (hidem : IsIdempotentFamily 𝔸 𝔹) (L₁ L₂ : ℕ) (hL₁ : Odd L₁) (hL₂ : Odd L₂)
    (hPar : ¬ IsPolymorphism 𝔸 𝔹 (Par L₁)) (hAT : ¬ IsPolymorphism 𝔸 𝔹 (AT L₂)) :
    ∃ c : ℕ, ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsPolymorphism 𝔸 𝔹 f →
      (Finset.univ.filter (fun i : Fin L => f (indicator {i}) = true)).card ≤ c := by
  classical
  obtain ⟨k, hcase⟩ := lemma_4_5 𝔸 𝔹 hPF hsym hfold hidem L₂ hL₂ hAT
  have hn : ∃ n, 2 ≤ n ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsPolymorphism 𝔸 𝔹 f →
      ∀ (T : Finset (Fin L)) (S₀ S₁ : Set ℕ),
      (∀ s, s ∈ S₀ ↔ ∀ X ⊆ T, X.card = s → f (indicator X) = false) →
      (∀ s, s ∈ S₁ ↔ ∀ X ⊆ T, X.card = s → f (indicator X) = true) →
      (∀ b : Fin n → ℕ, (∀ i, b i ∈ S₁) → ∑ i, b i ∈ S₀) ∧
      (∀ a ∈ S₀, ∀ b : Fin (n - 1) → ℕ, (∀ i, b i ∈ S₁) → a + ∑ i, b i ∈ S₁) := by
    rcases hcase with ⟨hk, hR⟩ | ⟨hk, b, hb1, hbk, hR⟩
    · exact ⟨k - 1, by omega, fun L f hf T S₀ S₁ h0 h1 =>
        sum_conditions_of_relax_one (by omega) f (hfold L f hf) (hR L f hf) T S₀ S₁ h0 h1⟩
    · exact ⟨k - b + 1, by omega, fun L f hf T S₀ S₁ h0 h1 =>
        sum_conditions_of_relax_zero hb1 hbk f (hfold L f hf) (hR L f hf) T S₀ S₁ h0 h1⟩
  obtain ⟨n, hn2, hcond⟩ := hn
  refine ⟨(1 + (2 * n - 2) * (3 * n - 4)) + L₁ * ((1 + (2 * n - 2) * (3 * n - 4)) + 1),
    fun L f hf => ?_⟩
  generalize hC : 1 + (2 * n - 2) * (3 * n - 4) = C
  set T := univ.filter (fun i : Fin L => f (indicator {i}) = true) with hT
  by_contra hlt
  push Not at hlt
  obtain ⟨c1, c2⟩ := hcond L f hf T {s | ∀ X ⊆ T, X.card = s → f (indicator X) = false}
    {s | ∀ X ⊆ T, X.card = s → f (indicator X) = true} (fun s => Iff.rfl) (fun s => Iff.rfl)
  have h0 : 0 ∈ {s | ∀ X ⊆ T, X.card = s → f (indicator X) = false} := by
    intro X _ hX
    rw [Finset.card_eq_zero.mp hX]
    have hind : indicator (∅ : Finset (Fin L)) = fun _ => false := by
      funext i; simp [indicator]
    rw [hind]; exact (hidem L f hf).1
  have h1 : 1 ∈ {s | ∀ X ⊆ T, X.card = s → f (indicator X) = true} := by
    intro X hXT hX
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hX
    have := hXT (mem_singleton_self i)
    rw [hT, mem_filter] at this; exact this.2
  have key := lemma_4_9_bounded_explicit n T.card (by omega) _ _ h0 h1
    (fun b hb _ => c1 b hb) (fun a ha b hb _ => c2 a ha b hb)
  rw [if_neg (by omega), hC] at key
  rcases Nat.even_or_odd n with he | ho
  · have hpar : ∀ X ⊆ T, C ≤ X.card → f (indicator X) = decide (X.card % 2 = 1) := by
      intro X hXT hCX
      have := key.2 he X.card hCX (Finset.card_le_card hXT)
      rcases Nat.even_or_odd X.card with hx | hx
      · rw [this.1 hx X hXT rfl]; simp [Nat.even_iff.mp hx]
      · rw [this.2 hx X hXT rfl]; simp [Nat.odd_iff.mp hx]
    obtain ⟨π, hπ⟩ := par_minor_of_parity f (hfold L f hf) (hidem L f hf).1 hL₁ T C hpar
      ((Nat.le_add_left _ _).trans hlt.le)
    apply hPar
    have hP : Par L₁ = fun y => f (fun i => y (π i)) := funext fun y => (hπ y).symm
    rw [hP]
    intro R M hM
    exact hf R (fun l => M (π l)) (fun l => hM _)
  · obtain ⟨hA, hB⟩ := key.1 ho ((Nat.le_add_right _ _).trans hlt.le)
    obtain ⟨X, hXT, hXc⟩ := Finset.exists_subset_card_eq
      (show C ≤ T.card from (Nat.le_add_right _ _).trans hlt.le)
    have := (hA X hXT hXc).symm.trans (hB X hXT hXc)
    simp at this

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem cfixingFixture_affd63a41c564e20bb8fe76c4992de22 {τ : Type} [Fintype τ] {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPF : IsPromiseFamily 𝔸 𝔹) (hsym : IsSymmetricFamily 𝔸 𝔹) (hfold : IsFoldedFamily 𝔸 𝔹)
    (hidem : IsIdempotentFamily 𝔸 𝔹) (L₁ L₂ : ℕ) (hL₁ : Odd L₁) (hL₂ : Odd L₂)
    (hPar : ¬ IsPolymorphism 𝔸 𝔹 (Par L₁)) (hAT : ¬ IsPolymorphism 𝔸 𝔹 (AT L₂)) :
    ∃ c : ℕ, ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsPolymorphism 𝔸 𝔹 f →
      (Finset.univ.filter (fun i : Fin L => f (indicator {i}) = true)).card ≤ c :=
  SymBoolPCSP.CFixing.lemma_4_10 𝔸 𝔹 hPF hsym hfold hidem L₁ L₂ hL₁ hL₂ hPar hAT

end cfixingModule_affd63a41c564e20bb8fe76c4992de22

section cfixingModule_d24be593d7a841b5b375ff61c2305646

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

/-- Lemma 4.12 (p. 24): if `Γ` is finite, symmetric, folded and idempotent and
`Par_{L₁}, AT_{L₂}, Maj_{L₃} ∉ Pol(Γ)` for some odd `L₁, L₂, L₃`, then there is `C(Γ) ∈ ℕ` such
that every polymorphism of `Γ` is `C(Γ)`-fixing. -/
theorem lemma_4_12 {τ : Type} [Fintype τ] {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPF : IsPromiseFamily 𝔸 𝔹) (hsym : IsSymmetricFamily 𝔸 𝔹) (hfold : IsFoldedFamily 𝔸 𝔹)
    (hidem : IsIdempotentFamily 𝔸 𝔹) (L₁ L₂ L₃ : ℕ) (hL₁ : Odd L₁) (hL₂ : Odd L₂)
    (hL₃ : Odd L₃) (hPar : ¬ IsPolymorphism 𝔸 𝔹 (Par L₁)) (hAT : ¬ IsPolymorphism 𝔸 𝔹 (AT L₂))
    (hMaj : ¬ IsPolymorphism 𝔸 𝔹 (Maj L₃)) :
    ∃ C : ℕ, ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsPolymorphism 𝔸 𝔹 f → IsCFixing C f := by
  classical
  obtain ⟨c, hc⟩ := lemma_4_10 𝔸 𝔹 hPF hsym hfold hidem L₁ L₂ hL₁ hL₂ hPar hAT
  have hcor := corollary_4_11 𝔸 𝔹 hPF hsym hfold hidem L₁ L₂ hL₁ hL₂ hPar hAT c hc
  obtain ⟨k, hk⟩ := lemma_4_7 𝔸 𝔹 hPF hsym hfold hidem L₃ hL₃ hMaj
  rcases hk with ⟨_, ⟨m, rfl⟩, hrel⟩ | ⟨_, b, hb2, hbk, hrel⟩
  · -- Case 1: `k = 2m + 1`, relaxation `(Ham_k({m+1}), Ham_k({0, …, 2m}))`
    refine ⟨m * (c + 1), fun L f hf => ?_⟩
    have h0 : f (fun _ => false) = false := (hidem L f hf).1
    have hpol := hrel L f hf
    rw [show (2 * m + 1 + 1) / 2 = m + 1 by omega, show 2 * m + 1 - 1 = 2 * m by omega] at hpol
    refine ⟨Finset.univ.filter (fun j : Fin L => ∃ Y : Finset (Fin L), j ∉ Y ∧
      f (indicator Y) = false ∧ f (indicator (insert j Y)) = true),
      (card_lt_of_subsets_true f c m _ (fun Z hZ hZc =>
      subset_true_of_relax_maj f (hfold L f hf) hpol Z hZc
        (fun j hj => (Finset.mem_filter.mp (hZ hj)).2)) (hcor L f hf)).le, fun x hx => ?_⟩
    rw [eq_false_of_vanish_increasing f h0 x hx, h0]
  · -- Case 2: relaxation `(Ham_k({1, k}), Ham_k({0, …, k} \ {b}))`, `2 ≤ b ≤ k - 1`
    obtain ⟨r, rfl⟩ : ∃ r, k = b + r := ⟨k - b, by omega⟩
    refine ⟨(c + 1) * b, fun L f hf => ?_⟩
    refine cfixing_of_small_witness f (hidem L f hf).1 b c (fun X hX => ?_) (hcor L f hf)
    obtain ⟨T, hT, hTmin⟩ := Finset.exists_min_image
      (X.powerset.filter (fun T => f (indicator T) = true)) Finset.card
      ⟨X, Finset.mem_filter.mpr ⟨Finset.mem_powerset_self X, hX⟩⟩
    rw [Finset.mem_filter, Finset.mem_powerset] at hT
    refine ⟨T, hT.1, hT.2, (card_lt_of_minimal f (hfold L f hf) (by omega) (hrel L f hf) T hT.2
      (fun T' hT' => ?_)).le⟩
    by_contra hne
    have := hTmin T' (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hT'.subset.trans hT.1),
      by simpa using hne⟩)
    have := Finset.card_lt_card hT'
    omega

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem cfixingFixture_d24be593d7a841b5b375ff61c2305646 {τ : Type} [Fintype τ] {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPF : IsPromiseFamily 𝔸 𝔹) (hsym : IsSymmetricFamily 𝔸 𝔹) (hfold : IsFoldedFamily 𝔸 𝔹)
    (hidem : IsIdempotentFamily 𝔸 𝔹) (L₁ L₂ L₃ : ℕ) (hL₁ : Odd L₁) (hL₂ : Odd L₂)
    (hL₃ : Odd L₃) (hPar : ¬ IsPolymorphism 𝔸 𝔹 (Par L₁)) (hAT : ¬ IsPolymorphism 𝔸 𝔹 (AT L₂))
    (hMaj : ¬ IsPolymorphism 𝔸 𝔹 (Maj L₃)) :
    ∃ C : ℕ, ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsPolymorphism 𝔸 𝔹 f → IsCFixing C f :=
  SymBoolPCSP.CFixing.lemma_4_12 𝔸 𝔹 hPF hsym hfold hidem L₁ L₂ L₃ hL₁ hL₂ hL₃ hPar hAT hMaj

end cfixingModule_d24be593d7a841b5b375ff61c2305646


end cfixingAssembly_AcceptedClosure

section cfixingAssembly_OutputFixing

set_option autoImplicit false
open PCSPBLPAff.Symmetric
namespace SymBoolPCSP.CFixing

theorem folded_nondegenerate {L : ℕ} (f : (Fin L → Bool) → Bool)
    (hf : IsFolded f) : IsNonDegenerate f := by
  have h := hf (fun _ => false)
  change f (fun _ => false) = !f (fun _ => true) at h
  exact fun he => (Bool.eq_not_self _).mp (he.symm.trans h)

theorem folded_family_nondegenerate {τ : Type} {ar : τ → ℕ}
    (𝔸 𝔹 : RelStruct τ ar Bool) (hf : IsFoldedFamily 𝔸 𝔹) :
    IsNonDegenerateFamily 𝔸 𝔹 := by
  exact fun L f hp => folded_nondegenerate f (hf L f hp)

theorem cfixing_neg_output (C : ℕ) {L : ℕ} (f : (Fin L → Bool) → Bool)
    (hf : IsCFixing C f) : IsCFixing C (fun x => !f x) := by
  obtain ⟨S, hS, hfix⟩ := hf
  exact ⟨S, hS, fun x hx => congrArg Bool.not (hfix x hx)⟩

theorem cfixing_mono {C D L : ℕ} (f : (Fin L → Bool) → Bool)
    (hCD : C ≤ D) (hf : IsCFixing C f) : IsCFixing D f := by
  exact match hf with | ⟨S, hS, hfix⟩ => ⟨S, hS.trans hCD, hfix⟩

end SymBoolPCSP.CFixing


end cfixingAssembly_OutputFixing

section cfixingAssembly_FamilyCore

set_option autoImplicit false
open PCSPBLPAff.Symmetric
namespace SymBoolPCSP.CFixing

/-- Negating a polymorphism of the negated target returns a polymorphism of the target. -/
theorem root_pol_neg_target {τ : Type} {ar : τ → ℕ}
    (𝔸 𝔹 : RelStruct τ ar Bool) {L : ℕ} (f : (Fin L → Bool) → Bool)
    (hf : IsPolymorphism 𝔸 (negStruct 𝔹) f) :
    IsPolymorphism 𝔸 𝔹 (fun x => !f x) := by
  intro R M hM
  obtain ⟨y, hy, hyeq⟩ := hf R M hM
  convert hy using 1
  funext c
  have hc := congrFun hyeq c
  simpa only [SymBoolPCSP.CFixing.neg, Bool.not_not] using (congrArg Bool.not hc).symm


/-- Forgetting the two unary constants only removes constraints on a polymorphism. -/
theorem root_pol_with_consts {τ : Type} {ar : τ → ℕ}
    (𝔸 𝔹 : RelStruct τ ar Bool) {L : ℕ} (f : (Fin L → Bool) → Bool)
    (hf : IsPolymorphism (withConsts 𝔸) (withConsts 𝔹) f) :
    IsPolymorphism 𝔸 𝔹 f := by
  exact fun R M hM => hf (Sum.inl R) M hM


/-- Foldedness transfers through negating the target relations. -/
theorem root_fold_neg_target {τ : Type} {ar : τ → ℕ}
    (𝔸 𝔹 : RelStruct τ ar Bool) (hfold : IsFoldedFamily 𝔸 𝔹) :
    IsFoldedFamily 𝔸 (negStruct 𝔹) := by
  intro L f hf x
  have hh := hfold L (fun y => !f y) (root_pol_neg_target 𝔸 𝔹 f hf) x
  simpa only [Bool.not_not] using congrArg Bool.not hh


/-- Negating every coordinate preserves relation symmetry. -/
theorem root_negRel_symmetric {k : ℕ} (Q : Set (Fin k → Bool))
    (hQ : IsSymmetricRel Q) : IsSymmetricRel (negRel Q) := by
  rintro x ⟨y, hy, rfl⟩ σ
  exact ⟨y ∘ σ, hQ y hy σ, rfl⟩


theorem root_neg_struct_symmetric {τ : Type} {ar : τ → ℕ}
    (𝔸 𝔹 : RelStruct τ ar Bool) (h : IsSymmetricFamily 𝔸 𝔹) :
    IsSymmetricFamily 𝔸 (negStruct 𝔹) := by
  exact fun R => ⟨(h R).1, root_negRel_symmetric (𝔹.rel R) (h R).2⟩

end SymBoolPCSP.CFixing

end cfixingAssembly_FamilyCore

section cfixingAssembly_ConstFamily

set_option autoImplicit false
open PCSPBLPAff.Symmetric
namespace SymBoolPCSP.CFixing

private theorem const_rel_symmetric (b : Bool) :
    IsSymmetricRel ({fun _ : Fin 1 => b} : Set (Fin 1 → Bool)) := by
  intro x hx σ
  simp only [Set.mem_singleton_iff] at hx ⊢
  rw [hx]
  rfl

theorem withConsts_promise {τ : Type} {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (h : IsPromiseFamily 𝔸 𝔹) : IsPromiseFamily (withConsts 𝔸) (withConsts 𝔹) := by
  intro R
  cases R
  case inl R => exact h R
  case inr b => exact Set.Subset.rfl

theorem withConsts_symmetric {τ : Type} {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (h : IsSymmetricFamily 𝔸 𝔹) : IsSymmetricFamily (withConsts 𝔸) (withConsts 𝔹) := by
  intro R
  cases R
  case inl R => exact h R
  case inr b => exact ⟨const_rel_symmetric b, const_rel_symmetric b⟩

end SymBoolPCSP.CFixing

end cfixingAssembly_ConstFamily

section cfixingAssembly_FinishCases

set_option autoImplicit false
open PCSPBLPAff.Symmetric
namespace SymBoolPCSP.CFixing

theorem idempotent_family_of_no_witness {τ : Type} {ar : τ → ℕ}
    (A B : RelStruct τ ar Bool)
    (h : ¬∃ (L : ℕ) (f : (Fin L → Bool) → Bool),
      IsPolymorphism A B f ∧ ¬IsIdempotent f) : IsIdempotentFamily A B := by
  intro L f hf
  by_contra hid
  exact h ⟨L, f, hf, hid⟩

end SymBoolPCSP.CFixing

end cfixingAssembly_FinishCases

open PCSPBLPAff.Symmetric SymBoolPCSP.CFixing

theorem solution {τ : Type} [Fintype τ] {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPF : IsPromiseFamily 𝔸 𝔹) (hfold : IsFoldedFamily 𝔸 𝔹) (hsym : IsSymmetricFamily 𝔸 𝔹)
    (L₁ L₂ L₃ L₄ L₅ L₆ : ℕ) (hL₁ : Odd L₁) (hL₂ : Odd L₂) (hL₃ : Odd L₃) (hL₄ : Odd L₄)
    (hL₅ : Odd L₅) (hL₆ : Odd L₆)
    (h₁ : ¬ IsPolymorphism 𝔸 𝔹 (Par L₁)) (h₂ : ¬ IsPolymorphism 𝔸 𝔹 (AT L₂))
    (h₃ : ¬ IsPolymorphism 𝔸 𝔹 (Maj L₃))
    (h₄ : ¬ IsPolymorphism 𝔸 𝔹 (fun x : Fin L₄ → Bool => !Par L₄ x))
    (h₅ : ¬ IsPolymorphism 𝔸 𝔹 (fun x : Fin L₅ → Bool => !AT L₅ x))
    (h₆ : ¬ IsPolymorphism 𝔸 𝔹 (fun x : Fin L₆ → Bool => !Maj L₆ x)) :
    ∃ C : ℕ, ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsPolymorphism 𝔸 𝔹 f → IsCFixing C f := by
  classical
  by_cases hex : ∃ (L : ℕ) (f : (Fin L → Bool) → Bool),
      IsPolymorphism 𝔸 𝔹 f ∧ ¬ IsIdempotent f
  · have hnd := folded_family_nondegenerate 𝔸 𝔹 hfold
    have hNegPF : IsPromiseFamily 𝔸 (negStruct 𝔹) := by
      obtain ⟨Lw, fw, hfw, hniw⟩ := hex
      intro R
      exact (proposition_2_12 (𝔸.rel R) (𝔹.rel R) (hPF R) fw (hfw R)
        (hnd Lw fw hfw) hniw).1
    obtain ⟨C0, hC0⟩ : ∃ C : ℕ, ∀ (L : ℕ) (f : (Fin L → Bool) → Bool),
        IsPolymorphism (withConsts 𝔸) (withConsts 𝔹) f → IsCFixing C f := by
      exact lemma_4_12 (withConsts 𝔸) (withConsts 𝔹)
        (withConsts_promise 𝔸 𝔹 hPF)
        (withConsts_symmetric 𝔸 𝔹 hsym)
        (fun L f hf => hfold L f (root_pol_with_consts 𝔸 𝔹 f hf))
        (fun L f hf => ((proposition_2_10 𝔸 𝔹 hPF f).mpr hf).2)
        L₁ L₂ L₃ hL₁ hL₂ hL₃
        (fun hp => h₁ (root_pol_with_consts 𝔸 𝔹 (Par L₁) hp))
        (fun hp => h₂ (root_pol_with_consts 𝔸 𝔹 (AT L₂) hp))
        (fun hp => h₃ (root_pol_with_consts 𝔸 𝔹 (Maj L₃) hp))
    obtain ⟨C1, hC1⟩ : ∃ C : ℕ, ∀ (L : ℕ) (f : (Fin L → Bool) → Bool),
        IsPolymorphism (withConsts 𝔸) (withConsts (negStruct 𝔹)) f → IsCFixing C f := by
      exact lemma_4_12 (withConsts 𝔸) (withConsts (negStruct 𝔹))
        (withConsts_promise 𝔸 (negStruct 𝔹) hNegPF)
        (withConsts_symmetric 𝔸 (negStruct 𝔹) (root_neg_struct_symmetric 𝔸 𝔹 hsym))
        (fun L f hf => root_fold_neg_target 𝔸 𝔹 hfold L f
          (root_pol_with_consts 𝔸 (negStruct 𝔹) f hf))
        (fun L f hf => ((proposition_2_10 𝔸 (negStruct 𝔹) hNegPF f).mpr hf).2)
        L₄ L₅ L₆ hL₄ hL₅ hL₆
        (fun hp => h₄ (root_pol_neg_target 𝔸 𝔹 (Par L₄)
          (root_pol_with_consts 𝔸 (negStruct 𝔹) (Par L₄) hp)))
        (fun hp => h₅ (root_pol_neg_target 𝔸 𝔹 (AT L₅)
          (root_pol_with_consts 𝔸 (negStruct 𝔹) (AT L₅) hp)))
        (fun hp => h₆ (root_pol_neg_target 𝔸 𝔹 (Maj L₆)
          (root_pol_with_consts 𝔸 (negStruct 𝔹) (Maj L₆) hp)))
    refine ⟨max C0 C1, ?_⟩
    intro L f hf
    rcases (lemma_2_13_1 𝔸 𝔹 hPF hnd hex L f).mp hf with hf0 | ⟨g, hg, rfl⟩
    · exact cfixing_mono f (Nat.le_max_left C0 C1) (hC0 L f hf0)
    · exact cfixing_mono (fun x => !g x) (le_max_right C0 C1)
        (cfixing_neg_output C1 g (hC1 L g hg))
  · exact lemma_4_12 𝔸 𝔹 hPF hsym hfold (idempotent_family_of_no_witness 𝔸 𝔹 hex)
      L₁ L₂ L₃ hL₁ hL₂ hL₃ h₁ h₂ h₃

